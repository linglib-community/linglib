module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Core.Order.Pareto

/-!
# Zaslavsky, Kemp, Regier and Tishby (2018): Efficient Compression in Color Naming

This file formalizes the communication model of [zaslavsky-kemp-regier-tishby-2018], in which
a color naming system is an encoder that compresses meanings, distributions over the colors of
the environment, into words, and languages are hypothesized to trade off the complexity of the
lexicon against the accuracy of communication as the Information Bottleneck principle of
[tishby-pereira-bialek-1999] prescribes. The meanings are a Markov kernel from `M` to the
environment `U`, the cognitive source a probability measure on `M`, and the encoder a Markov
kernel from `M` to the words `W`. The listener is the Bayesian decoder, interpreting a word as
the posterior mixture of meanings (`decoder`), and no other decoder has lower expected
distortion (`distortion_le`). Complexity is the information the words carry about the meanings
(`complexity`), accuracy the information they carry about the environment (`accuracy`), and the
expected Kullback–Leibler distortion between the speaker's meaning and the listener's
interpretation is the information about the environment that the lexicon loses
(`distortion_eq`), so that minimizing distortion is maximizing accuracy. Accuracy is bounded by
complexity and by the information the meanings carry (`accuracy_le_complexity`,
`accuracy_le_sourceInfo`), and a lexicon that ignores the meaning has complexity `0`
(`complexity_const`).

The Information Bottleneck objective `F_β = I(M;W) − β I(W;U)` (`objective`) is, up to a
constant, complexity plus `β` times distortion (`objective_eq_complexity_add_mul_distortion`), so
a minimizer at `β > 0` lies on the IB curve, no lexicon being both simpler and less distorting
(`not_costPair_lt`). Below `β = 1` the
meaning-blind lexicon is optimal (`objective_const_le`). Every minimizer of `F_β` has the
self-consistent Boltzmann form in which a word's probability decays exponentially in its
divergence from the meaning (`ibUpdate`, `IsIBOptimum`, `isIBOptimum_of_forall_objective_le`), so
that at finite `β` the optimal categories are soft (`IsIBOptimum.real_pos`).

The cognitive source is the least informative source of the SI (§2). A least informative prior
of a naming distribution maximizes the entropy of the meaning less its conditional entropy given
the word (`IsLeastInformative`, eq. S10); that objective is the complexity of the lexicon
(`measureEntropy_sub_condEntropy`, eq. S11), so the least informative priors are the
capacity-achieving priors (`isLeastInformative_iff`) and, with positive mass everywhere, the
fixed points of the Blahut–Arimoto update of [blahut-1972] and [arimoto-1972]
(`IsLeastInformative.eq_blahutArimoto`). The complexity is also the word average of the
divergence of the posterior from the prior (`complexity_eq_sum_klDiv_posterior`, eq. S12), and the
universal source averages the least informative priors of the languages (`averagePrior`,
eq. S13).

## Implementation notes

* The information quantities are the mutual informations `Im[·]` of `InformationTheory`, and
  the distortion the divergences `klDiv` of mathlib; the paper's forms with the word marginal in
  the denominator are the averaged divergences of `InformationTheory.measureMutualInfo_compProd`
  (`complexity_eq`). On finite alphabets no positivity assumption is needed: a meaning and a word
  that co-occur make the meaning absolutely continuous with respect to the word's
  interpretation.
* `distortion_eq` and `distortion_le` are the compensation identity
  `InformationTheory.sum_mul_toReal_klDiv` for the meanings channel, applied at each word's
  posterior over meanings.
* Eq. 7 is a fixed-point equation: the Boltzmann encoder `ibUpdate` tilts the word marginal row
  by row (`Measure.tilted`), and `isIBOptimum_of_forall_objective_le` is the Gibbs variational
  principle of `Core.Probability.GibbsVariational` applied to each row. `F_β + β I(M;U)` is the
  source average of the negative free energies of the encoder's rows against its own word
  marginal and Bayesian decoder, and at most that average against any other; each row's free
  energy is at most its log partition function, with equality only at the tilt
  (`eq_tilted_of_freeEnergy_eq_cgf`). The theorem assumes a source and meanings of full
  support, as the paper's Gaussian meanings are.
* The efficiency loss `ε_l` divides the minimal deviation by the fitted `β_l`; the fit itself is
  a numerical optimization outside the formalization. The empirical encoders of the World Color
  Survey are not in the library.

## References

* [N. Zaslavsky, C. Kemp, T. Regier and N. Tishby, *Efficient compression in color naming and
  its evolution* (2018)][zaslavsky-kemp-regier-tishby-2018]
* [N. Tishby, F. C. Pereira and W. Bialek, *The information bottleneck method*
  (1999)][tishby-pereira-bialek-1999]
* [C. E. Shannon, *A Mathematical Theory of Communication* (1948)][shannon-1948]
* [R. E. Blahut, *Computation of channel capacity and rate-distortion functions*
  (1972)][blahut-1972]
* [S. Arimoto, *An algorithm for computing the capacity of arbitrary discrete memoryless
  channels* (1972)][arimoto-1972]
-/

@[expose] public section

namespace ZaslavskyKempRegierTishby2018

open MeasureTheory ProbabilityTheory InformationTheory Finset Real
open scoped ENNReal

variable {U M W : Type*} [MeasurableSpace U] [MeasurableSpace M] [MeasurableSpace W]
  [Fintype M] [MeasurableSingletonClass M] [Nonempty M]
  (meanings : Kernel M U) [IsMarkovKernel meanings] (source : Measure M)
  [IsProbabilityMeasure source] (encoder : Kernel M W) [IsMarkovKernel encoder]

/-! ### The Bayesian listener -/

/-- The listener's interpretation of a word (eq. 1), the posterior mixture of meanings
`m̂_w(u) = ∑ m, q(m | w) m(u)`. -/
noncomputable def decoder : Kernel W U := meanings ∘ₖ (encoder†source)

instance : IsMarkovKernel (decoder meanings source encoder) := by
  unfold decoder; infer_instance

omit [IsMarkovKernel meanings] in
theorem decoder_comp :
    decoder meanings source encoder ∘ₘ (encoder ∘ₘ source) = meanings ∘ₘ source := by
  rw [decoder, ← Measure.comp_assoc, posterior_comp_self]

/-! ### Complexity, accuracy and distortion -/

variable [Fintype U] [Fintype W] [MeasurableSingletonClass U] [MeasurableSingletonClass W]

/-- The complexity of the lexicon, `I_q(M;W)`. -/
noncomputable def complexity : ℝ := Im[source ⊗ₘ encoder]

/-- The accuracy of the lexicon, `I_q(W;U)`, between a word and the listener's interpretation. -/
noncomputable def accuracy : ℝ := Im[(encoder ∘ₘ source) ⊗ₘ decoder meanings source encoder]

/-- The information the meanings carry about the environment, `I(M;U)`, independent of the
encoder. -/
noncomputable def sourceInfo : ℝ := Im[source ⊗ₘ meanings]

/-- The expected distortion `E_q[D[m ‖ m̂_w]]` between the speaker's meaning and the listener's
interpretation (eq. 4). -/
noncomputable def distortion : ℝ :=
  ∫ p, (klDiv (meanings p.1) (decoder meanings source encoder p.2)).toReal ∂(source ⊗ₘ encoder)

omit [Nonempty M] in
/-- Complexity in the paper's form (eq. 2): the source average of the divergence of each
meaning's naming distribution from the word marginal. -/
theorem complexity_eq :
    complexity source encoder
      = ∑ m, source.real {m} * (klDiv (encoder m) (encoder ∘ₘ source)).toReal :=
  measureMutualInfo_compProd encoder source

omit [Nonempty M] in
theorem complexity_const (ν : Measure W) [IsProbabilityMeasure ν] :
    complexity source (Kernel.const M ν) = 0 := by
  rw [complexity, Measure.compProd_const, measureMutualInfo_prod]

omit [Nonempty M] in
private theorem integral_compProd (f : M × W → ℝ) :
    ∫ p, f p ∂(source ⊗ₘ encoder)
      = ∑ m, source.real {m} * ∑ w, (encoder m).real {w} * f (m, w) := by
  rw [integral_fintype .of_finite, Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [Measure.compProd_real_singleton, smul_eq_mul, mul_assoc]

private theorem integral_compProd_eq_sum_posterior (f : M × W → ℝ) :
    ∫ p, f p ∂(source ⊗ₘ encoder)
      = ∑ w, (encoder ∘ₘ source).real {w} * ∑ m, ((encoder†source) w).real {m} * f (m, w) := by
  rw [integral_compProd]
  simp_rw [mul_sum, ← mul_assoc, comp_real_mul_posterior_real encoder source]
  exact sum_comm

omit [Fintype W] [MeasurableSingletonClass W] in
private theorem sum_posterior_toReal_klDiv (w : W) (ν : Measure U) [IsProbabilityMeasure ν]
    (hν : ∀ m, (encoder†source) w {m} ≠ 0 → meanings m ≪ ν) :
    ∑ m, ((encoder†source) w).real {m} * (klDiv (meanings m) ν).toReal
      = ∑ m, ((encoder†source) w).real {m}
          * (klDiv (meanings m) (decoder meanings source encoder w)).toReal
        + (klDiv (decoder meanings source encoder w) ν).toReal := by
  have hd : decoder meanings source encoder w = meanings ∘ₘ (encoder†source) w := rfl
  rw [hd, sum_mul_toReal_klDiv meanings _ ν hν, ← measureMutualInfo_compProd]

/-- Eq. 5: the expected distortion is the information about the environment that the lexicon
loses, `E_q[D[M ‖ M̂]] = I(M;U) − I_q(W;U)`. -/
theorem distortion_eq :
    distortion meanings source encoder
      = sourceInfo meanings source - accuracy meanings source encoder := by
  have hsrc : sourceInfo meanings source
      = ∫ p, (klDiv (meanings p.1) (meanings ∘ₘ source)).toReal ∂(source ⊗ₘ encoder) := by
    rw [sourceInfo, measureMutualInfo_compProd, integral_compProd]
    refine sum_congr rfl fun m _ => ?_
    dsimp only
    rw [← sum_mul, sum_measureReal_singleton_eq_one, one_mul]
  rw [eq_sub_iff_add_eq, distortion, hsrc, accuracy, measureMutualInfo_compProd, decoder_comp,
    integral_compProd_eq_sum_posterior, integral_compProd_eq_sum_posterior, ← sum_add_distrib]
  refine sum_congr rfl fun w _ => ?_
  dsimp only
  obtain hw | hw := eq_or_ne ((encoder ∘ₘ source) {w}) 0
  · simp [measureReal_def, hw]
  rw [← mul_add, sum_posterior_toReal_klDiv meanings source encoder w (meanings ∘ₘ source)
    fun m hm => meanings.absolutelyContinuous_comp source fun h => hm ?_]
  rw [posterior_apply_singleton encoder source hw, h, zero_mul, ENNReal.zero_div]

/-- The Bayesian listener of eq. 1 is optimal: no decoder whose interpretations allow every
state that a meaning allows has lower expected distortion. -/
theorem distortion_le (d : Kernel W U) [IsMarkovKernel d] (hd : ∀ m w, meanings m ≪ d w) :
    distortion meanings source encoder
      ≤ ∫ p, (klDiv (meanings p.1) (d p.2)).toReal ∂(source ⊗ₘ encoder) := by
  rw [distortion, integral_compProd_eq_sum_posterior, integral_compProd_eq_sum_posterior]
  refine sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  dsimp only
  rw [sum_posterior_toReal_klDiv meanings source encoder w (d w) fun m _ => hd m w]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-! ### The information plane -/

theorem accuracy_le_sourceInfo : accuracy meanings source encoder ≤ sourceInfo meanings source := by
  have : 0 ≤ distortion meanings source encoder := integral_nonneg fun _ => ENNReal.toReal_nonneg
  linarith [distortion_eq meanings source encoder]

theorem accuracy_le_complexity : accuracy meanings source encoder ≤ complexity source encoder := by
  rw [accuracy, complexity, decoder, ← Measure.parallelComp_comp_compProd,
    ← measureMutualInfo_map_swap (source ⊗ₘ encoder), ← compProd_posterior_eq_map_swap]
  exact measureMutualInfo_parallelComp_id_comp_le _ meanings

/-! ### The Information Bottleneck objective -/

/-- The Information Bottleneck objective (eq. 6), `F_β = I_q(M;W) − β I_q(W;U)`. -/
noncomputable def objective (β : ℝ) : ℝ :=
  complexity source encoder - β * accuracy meanings source encoder

/-- The complexity–distortion cost pair of the lexicon. -/
noncomputable def costPair : ℝ × ℝ :=
  (complexity source encoder, distortion meanings source encoder)

theorem objective_eq_complexity_add_mul_distortion (β : ℝ) :
    objective meanings source encoder β = complexity source encoder
      + β * distortion meanings source encoder - β * sourceInfo meanings source := by
  rw [objective, distortion_eq]
  ring

/-- A minimizer of the objective at `β > 0` lies on the IB curve: no lexicon is both simpler and
less distorting. -/
theorem not_costPair_lt {β : ℝ} (hβ : 0 < β)
    (hmin : ∀ (q : Kernel M W) [IsMarkovKernel q],
      objective meanings source encoder β ≤ objective meanings source q β)
    (q : Kernel M W) [IsMarkovKernel q] :
    ¬ costPair meanings source q < costPair meanings source encoder := fun h ↦ by
  have := hmin q
  rw [objective_eq_complexity_add_mul_distortion, objective_eq_complexity_add_mul_distortion,
    sub_le_sub_iff_right] at this
  exact (strictMono_fst_add_mul_snd hβ h).not_ge this

/-- For `β ≤ 1` a lexicon ignoring the meaning minimizes the objective, so IB optima are informative
only above `β = 1` (eq. 6). -/
theorem objective_const_le (ν : Measure W) [IsProbabilityMeasure ν] {β : ℝ} (hβ : β ≤ 1) :
    objective meanings source (Kernel.const M ν) β ≤ objective meanings source encoder β := by
  have h0 : accuracy meanings source (Kernel.const M ν) = 0 :=
    le_antisymm ((accuracy_le_complexity ..).trans (complexity_const source ν).le)
      (measureMutualInfo_nonneg _)
  have h1 := accuracy_le_complexity meanings source encoder
  have h2 : 0 ≤ accuracy meanings source encoder := measureMutualInfo_nonneg _
  rw [objective, objective, complexity_const, h0]
  nlinarith [mul_nonneg (sub_nonneg.2 hβ) h2]

/-- The right side of eq. 7: the encoder whose row at a meaning tilts the word marginal by `−β`
times the divergence of the meaning from each word's interpretation. -/
noncomputable def ibUpdate (β : ℝ) : Kernel M W :=
  Kernel.ofFunOfCountable fun m => (encoder ∘ₘ source).tilted
    fun w => -β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal

omit [IsMarkovKernel meanings] [Fintype U] [Fintype W] [MeasurableSingletonClass U]
  [MeasurableSingletonClass W] in
theorem ibUpdate_apply (β : ℝ) (m : M) :
    ibUpdate meanings source encoder β m = (encoder ∘ₘ source).tilted
      fun w => -β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal := rfl

instance (β : ℝ) : IsMarkovKernel (ibUpdate meanings source encoder β) :=
  ⟨fun _ => isProbabilityMeasure_tilted .of_finite⟩

/-- The self-consistent form of the Information Bottleneck optima (eq. 7): the encoder is its
own update. -/
def IsIBOptimum (β : ℝ) : Prop := encoder = ibUpdate meanings source encoder β

omit [IsMarkovKernel meanings] [Fintype U] [MeasurableSingletonClass U] in
/-- Eq. 7 pointwise: each word's probability decays exponentially, at rate `β`, in the
divergence between the meaning and the word's interpretation. -/
theorem ibUpdate_real_singleton (β : ℝ) (m : M) (w : W) :
    (ibUpdate meanings source encoder β m).real {w} =
      (encoder ∘ₘ source).real {w}
          * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
        / ∑ w', (encoder ∘ₘ source).real {w'}
          * exp (-β * (klDiv (meanings m) (decoder meanings source encoder w')).toReal) :=
  tilted_real_singleton _ _ w

omit [IsMarkovKernel meanings] [Fintype U] [MeasurableSingletonClass U] in
theorem IsIBOptimum.real_pos {β : ℝ} (h : IsIBOptimum meanings source encoder β) {w : W}
    (hw : (encoder ∘ₘ source) {w} ≠ 0) (m : M) : 0 < (encoder m).real {w} := by
  rw [DFunLike.congr_fun h m]
  exact ENNReal.toReal_pos (fun h0 => hw (absolutelyContinuous_tilted .of_finite h0))
    (measure_ne_top _ _)

omit [IsMarkovKernel meanings] [Fintype W] [MeasurableSingletonClass W] in
private theorem absolutelyContinuous_decoder (hmeanings : ∀ m u, meanings m {u} ≠ 0) (m : M)
    (w : W) : meanings m ≪ decoder meanings source encoder w := by
  refine Measure.absolutelyContinuous_of_forall_singleton fun u hu => absurd hu ?_
  obtain ⟨m', hm'⟩ : ∃ m', (encoder†source) w {m'} ≠ 0 := by
    by_contra! h
    have := measure_univ (μ := (encoder†source) w)
    rw [← coe_univ, ← sum_measure_singleton, sum_eq_zero fun m' _ => h m'] at this
    exact zero_ne_one this
  rw [show decoder meanings source encoder w {u} = _ from
    Kernel.comp_apply_singleton meanings (encoder†source) w u]
  exact fun h => mul_ne_zero hm' (hmeanings m' u) (sum_eq_zero_iff.1 h m' (mem_univ m'))

omit [Nonempty M] [IsMarkovKernel meanings] [Fintype U] [MeasurableSingletonClass U] in
private theorem neg_sum_freeEnergy (q : Kernel M W) [IsMarkovKernel q] (ρ : Measure W)
    (d : Kernel W U) (β : ℝ) :
    -∑ m, source.real {m}
        * ρ.freeEnergy (fun w => -β * (klDiv (meanings m) (d w)).toReal) (q m)
      = ∑ m, source.real {m} * (klDiv (q m) ρ).toReal
        + β * ∫ p, (klDiv (meanings p.1) (d p.2)).toReal ∂(source ⊗ₘ q) := by
  rw [integral_compProd, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun m _ => ?_
  simp only [Measure.freeEnergy, integral_fintype .of_finite, smul_eq_mul, mul_sum]
  rw [mul_sub, mul_sum, neg_sub, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun w _ => by ring

private theorem objective_add_eq (β : ℝ) :
    objective meanings source encoder β + β * sourceInfo meanings source
      = -∑ m, source.real {m} * (encoder ∘ₘ source).freeEnergy
          (fun w => -β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
          (encoder m) := by
  rw [neg_sum_freeEnergy, ← complexity_eq, ← distortion, distortion_eq, objective]
  ring

private theorem objective_add_le (q : Kernel M W) [IsMarkovKernel q] (ρ : Measure W)
    [IsProbabilityMeasure ρ] (hq : ∀ m, q m ≪ ρ) (d : Kernel W U) [IsMarkovKernel d]
    (hd : ∀ m w, meanings m ≪ d w) {β : ℝ} (hβ : 0 ≤ β) :
    objective meanings source q β + β * sourceInfo meanings source
      ≤ -∑ m, source.real {m}
          * ρ.freeEnergy (fun w => -β * (klDiv (meanings m) (d w)).toReal) (q m) := by
  rw [neg_sum_freeEnergy, sum_mul_toReal_klDiv q source ρ fun m _ => hq m, objective,
    complexity]
  have h := mul_le_mul_of_nonneg_left (distortion_le meanings source q d hd) hβ
  rw [distortion_eq] at h
  have : 0 ≤ (klDiv (q ∘ₘ source) ρ).toReal := ENNReal.toReal_nonneg
  linarith

/-- Eq. 7: for a source and meanings of full support, every minimizer of the objective at
`β ≥ 0` has the self-consistent Boltzmann form. -/
theorem isIBOptimum_of_forall_objective_le {β : ℝ} (hβ : 0 ≤ β)
    (hsource : ∀ m, source {m} ≠ 0) (hmeanings : ∀ m u, meanings m {u} ≠ 0)
    (hmin : ∀ (q : Kernel M W) [IsMarkovKernel q],
      objective meanings source encoder β ≤ objective meanings source q β) :
    IsIBOptimum meanings source encoder β := by
  have hq (m : M) : encoder m ≪ encoder ∘ₘ source :=
    encoder.absolutelyContinuous_comp source (hsource m)
  -- each row's free energy is at most the log partition function, attained at the Boltzmann row
  have hle (m : M) := freeEnergy_le_cgf (encoder ∘ₘ source) (encoder m)
    (f := fun w => -β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
    (hq m) .of_finite .of_finite .of_finite
  have hg (m : M) := freeEnergy_tilted (encoder ∘ₘ source)
    (f := fun w => -β * (klDiv (meanings m) (decoder meanings source encoder w)).toReal)
    .of_finite .of_finite .of_finite
  -- minimality forces the average to be attained too
  have hsum : ∑ m, source.real {m} * (cgf (fun w => -β * (klDiv (meanings m)
        (decoder meanings source encoder w)).toReal) (encoder ∘ₘ source) 1
      - (encoder ∘ₘ source).freeEnergy (fun w => -β * (klDiv (meanings m)
        (decoder meanings source encoder w)).toReal) (encoder m)) ≤ 0 := by
    have := objective_add_le meanings source (ibUpdate meanings source encoder β)
      (encoder ∘ₘ source) (fun _ => tilted_absolutelyContinuous _ _)
      (decoder meanings source encoder) (absolutelyContinuous_decoder meanings source encoder
        hmeanings) hβ
    simp only [ibUpdate_apply, hg] at this
    simp only [mul_sub, sum_sub_distrib]
    linarith [objective_add_eq meanings source encoder β, hmin (ibUpdate meanings source encoder β)]
  refine Kernel.ext fun m => eq_tilted_of_freeEnergy_eq_cgf _ _ (hq m) .of_finite .of_finite
    .of_finite (le_antisymm (hle m) ?_)
  have := (sum_eq_zero_iff_of_nonneg fun m _ => mul_nonneg measureReal_nonneg
    (sub_nonneg.2 (hle m))).1 (hsum.antisymm (sum_nonneg fun m _ => mul_nonneg
      measureReal_nonneg (sub_nonneg.2 (hle m)))) m (mem_univ m)
  rw [mul_eq_zero, sub_eq_zero] at this
  exact (this.resolve_left (mt (measureReal_eq_zero_iff (measure_ne_top _ _)).1
    (hsource m))).le

variable (encoder' : Kernel M W) [IsMarkovKernel encoder']

/-- The deviation `ΔF_β` of the lexicon from a reference encoder at `β`. -/
noncomputable def deviation (β : ℝ) : ℝ :=
  objective meanings source encoder β - objective meanings source encoder' β

/-- The efficiency loss `ε_l = ΔF_{β_l} / β_l` at the fitted trade-off. -/
noncomputable def efficiencyLoss (β : ℝ) : ℝ :=
  deviation meanings source encoder encoder' β / β

omit [IsMarkovKernel meanings] [Fintype U] [Fintype W] [MeasurableSingletonClass U]
  [MeasurableSingletonClass W] in
theorem efficiencyLoss_nonneg {β : ℝ} (hβ : 0 < β)
    (hmin : ∀ (q : Kernel M W) [IsMarkovKernel q],
      objective meanings source encoder' β ≤ objective meanings source q β) :
    0 ≤ efficiencyLoss meanings source encoder encoder' β :=
  div_nonneg (sub_nonneg.2 (hmin encoder)) hβ.le

/-! ### The least informative source -/

section LeastInformative

omit [Nonempty M] [IsProbabilityMeasure source] [IsMarkovKernel encoder] [Fintype W] [Fintype M]
  [MeasurableSingletonClass M] [MeasurableSingletonClass W] in
/-- A least informative prior for a naming distribution (SI eq. S10): a prior over the meanings
maximizing the entropy of the meaning less its conditional entropy given the word. -/
def IsLeastInformative : Prop :=
  ∀ p : ProbabilityMeasure M,
    Hm[(p : Measure M)] - H[Prod.fst | Prod.snd ; (p : Measure M) ⊗ₘ encoder]
      ≤ Hm[source] - H[Prod.fst | Prod.snd ; source ⊗ₘ encoder]

omit [Nonempty M] in
theorem measureEntropy_sub_condEntropy :
    Hm[source] - H[Prod.fst | Prod.snd ; source ⊗ₘ encoder] = complexity source encoder := by
  rw [condEntropy_fst_snd, Measure.fst_compProd, complexity]
  ring

omit [Nonempty M] in
theorem isLeastInformative_iff :
    IsLeastInformative source encoder ↔ complexity source encoder = channelCapacity encoder := by
  rw [IsLeastInformative, measureEntropy_sub_condEntropy]
  simp only [measureEntropy_sub_condEntropy]
  refine ⟨fun h => le_antisymm (measureMutualInfo_compProd_le_channelCapacity encoder source)
    (Real.iSup_le h (measureMutualInfo_nonneg _)), fun h p => ?_⟩
  rw [h]
  exact measureMutualInfo_compProd_le_channelCapacity encoder p

theorem complexity_eq_sum_klDiv_posterior :
    complexity source encoder
      = ∑ w, (encoder ∘ₘ source).real {w} * (klDiv ((encoder†source) w) source).toReal := by
  rw [complexity, ← measureMutualInfo_map_swap, ← compProd_posterior_eq_map_swap,
    measureMutualInfo_compProd, posterior_comp_self]

/-- A least informative prior of positive mass everywhere is a fixed point of the Blahut–Arimoto
update (SI §2.1). -/
theorem IsLeastInformative.eq_blahutArimoto (h : IsLeastInformative source encoder)
    (hsource : ∀ m, source {m} ≠ 0) : source = blahutArimoto encoder source :=
  (eq_blahutArimoto_iff encoder source).1 ⟨(isLeastInformative_iff source encoder).1 h, hsource⟩

end LeastInformative

omit [Fintype M] [MeasurableSingletonClass M] [Nonempty M] in
/-- SI eq. S13: the universal least informative source averages the least informative priors of
`L` languages. -/
noncomputable def averagePrior {L : ℕ} (priors : Fin L → Measure M) : Measure M :=
  (L : ℝ≥0∞)⁻¹ • ∑ l, priors l

omit [Fintype M] [MeasurableSingletonClass M] [Nonempty M] in
instance {L : ℕ} [NeZero L] (priors : Fin L → Measure M)
    [∀ l, IsProbabilityMeasure (priors l)] : IsProbabilityMeasure (averagePrior priors) := by
  constructor
  rw [averagePrior, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne L) (ENNReal.natCast_ne_top L)

end ZaslavskyKempRegierTishby2018
