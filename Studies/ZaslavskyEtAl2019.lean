module

public import Linglib.Core.InformationTheory.ChannelCapacity
public import Linglib.Core.Probability.ConditionalProbability
public import Studies.ZaslavskyKempRegierTishby2018

/-!
# Zaslavsky et al. (2019): Color Naming Reflects Both Perceptual Structure and Communicative Need

This file formalizes [zaslavsky-etal-2019]'s information-theoretic link between communicative
need and communicative precision in color naming. A language's color naming distribution
`p(w | c)` is a channel `κ : Kernel C W` from colors to words and a need distribution is a prior
`μ` over colors. The expected surprisal `S(c)` of a color (eq. 1) is the surprisal of the color
to a listener who hears its name and inverts the lexicon by Bayes' rule (eq. 2), the measure of
communicative imprecision with which [gibson-etal-2017] found warm colors named more precisely
than cool ones. The capacity of the lexicon (eqs. 3 and 4) is `channelCapacity κ`, and the
paper's central observation is that the need distributions attaining it are those with
`p(c) ∝ exp(−S(c))` (eq. 5, `capacityAchieving_iff`), so that `−log p(c)` is linear in `S(c)`
with slope one (eq. 6, `neg_log_eq_add_channelCapacity`). The intercept `log Z` of eq. 6 is the
capacity itself.

The divergence of the row `κ c` from the word marginal is `−S(c) − log p(c)`
(`toReal_klDiv_eq`), so eq. 5 is the divergence condition of `InformationTheory`'s capacity
theorems: sufficiency (`measureMutualInfo_compProd_eq_channelCapacity`) and necessity at a prior
of positive mass everywhere (`toReal_klDiv_eq_channelCapacity`).

The artificial naming systems obtained by clustering the chips in perceptual space are
deterministic channels (`ofPartition`). Under a uniform need the surprisal of a color is the log
size of its cluster (`expectedSurprisal_ofPartition_uniformOn`), so that their warm–cool
asymmetry is an asymmetry in cluster size (`warmCoolAsymmetry_ofPartition_uniformOn_iff`). The
prior spreading mass equally over clusters (`clusterPrior`) is capacity-achieving
(`capacityAchieving_clusterPrior`) and the capacity of a `k`-term clustering system is `log k`
(`channelCapacity_ofPartition`). The universal need distribution inferred from the World Color
Survey averages the per-language capacity-achieving priors (eq. 7), which are the least
informative priors of [zaslavsky-kemp-regier-tishby-2018] (`isLeastInformative_iff`).

## Implementation notes

* The paper states eq. 5 as necessary and sufficient for a prior to be capacity-achieving.
  `capacityAchieving_iff` states it with the positivity that eq. 5 itself entails: a need
  distribution satisfies eq. 5 exactly when it is capacity-achieving and gives every color
  positive mass. A capacity-achieving prior may leave a color unused, and eq. 5 then fails.
* Every prior giving the clusters of a clustering system equal mass satisfies eq. 5, so the
  capacity-achieving prior of such a system is not unique; `clusterPrior` is the one uniform
  within each cluster.
* The perceptual coordinates of the chips and the `k`-means procedure are not represented; a
  clustering enters only through its assignment of chips to terms. The survey data that
  instantiate `WarmCoolAsymmetry` are not in the library.

## References

* [N. Zaslavsky, C. Kemp, N. Tishby and T. Regier, *Color naming reflects both perceptual
  structure and communicative need* (2019)][zaslavsky-etal-2019]
* [E. Gibson, R. Futrell, J. Jara-Ettinger, K. Mahowald, L. Bergen, S. Ratnasingam, M. Gibson,
  S. T. Piantadosi and B. R. Conway, *Color naming across languages reflects color use*
  (2017)][gibson-etal-2017]
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2006)][cover-thomas-2006]
* [C. E. Shannon, *A Mathematical Theory of Communication* (1948)][shannon-1948]
* [N. Zaslavsky, C. Kemp, T. Regier and N. Tishby, *Efficient compression in color naming and
  its evolution* (2018)][zaslavsky-kemp-regier-tishby-2018]
-/

@[expose] public section

namespace ZaslavskyEtAl2019

open MeasureTheory ProbabilityTheory InformationTheory Finset Real
open scoped ENNReal

variable {C W : Type*} [MeasurableSpace C] [MeasurableSpace W] [Fintype C]
  [MeasurableSingletonClass C] [MeasurableSingletonClass W] [Nonempty C]

/-! ### Communicative precision -/

/-- The expected surprisal `S(c)` of a color (eq. 1): the surprisal of the color to a listener
who hears its name and recovers a color by Bayes' rule (eq. 2), averaged over its names. Lower
values mean more precise communication. -/
noncomputable def expectedSurprisal (κ : Kernel C W) [IsFiniteKernel κ] (μ : Measure C)
    [IsFiniteMeasure μ] (c : C) : ℝ :=
  ∫ w, surprisal ((κ†μ) w) c ∂(κ c)

/-- The temperature of a color chip. -/
inductive Temperature
  | warm | cool
  deriving DecidableEq, Repr

/-- The warm–cool asymmetry of [gibson-etal-2017]: under the need distribution `μ`, the warm
colors have lower mean expected surprisal than the cool ones. -/
def WarmCoolAsymmetry (κ : Kernel C W) [IsFiniteKernel κ] (μ : Measure C) [IsFiniteMeasure μ]
    (temp : C → Temperature) : Prop :=
  (∑ c ∈ univ.filter (temp · = .warm), expectedSurprisal κ μ c) / #(univ.filter (temp · = .warm))
    < (∑ c ∈ univ.filter (temp · = .cool), expectedSurprisal κ μ c)
        / #(univ.filter (temp · = .cool))

/-! ### Need and precision at capacity -/

section Capacity

variable [Fintype W] (κ : Kernel C W) [IsMarkovKernel κ] (μ : Measure C)
  [IsProbabilityMeasure μ]

omit [Fintype W] [MeasurableSingletonClass W] in
theorem neg_expectedSurprisal (c : C) :
    -expectedSurprisal κ μ c = ∫ w, log (((κ†μ) w).real {c}) ∂(κ c) := by
  rw [expectedSurprisal, ← integral_neg]
  simp only [surprisal, neg_neg]

/-- The identity behind eq. 5: the divergence of a color's naming distribution from the word
marginal is its negative expected surprisal less its log need. -/
theorem toReal_klDiv_eq {c : C} (hc : μ {c} ≠ 0) :
    (klDiv (κ c) (κ ∘ₘ μ)).toReal = -expectedSurprisal κ μ c - log (μ.real {c}) := by
  rw [toReal_klDiv_eq_integral_log_sub κ μ hc, neg_expectedSurprisal]

/-- At a capacity-achieving need distribution of positive mass, `−log p(c)` is the expected
surprisal plus the lexicon's capacity (Eq. 6). -/
theorem neg_log_eq_add_channelCapacity (h : Im[μ ⊗ₘ κ] = channelCapacity κ)
    (hμ : ∀ c, μ {c} ≠ 0) (c : C) :
    -log (μ.real {c}) = expectedSurprisal κ μ c + channelCapacity κ := by
  have := toReal_klDiv_eq_channelCapacity κ μ hμ h c
  rw [toReal_klDiv_eq κ μ (hμ c)] at this
  linarith

/-- A need distribution satisfies `p(c) ∝ exp(−S(c))` exactly when it is capacity-achieving with
positive mass on every color (Eq. 5). -/
theorem capacityAchieving_iff :
    (Im[μ ⊗ₘ κ] = channelCapacity κ ∧ ∀ c, μ {c} ≠ 0) ↔
      ∃ Z > 0, ∀ c, μ.real {c} = exp (-expectedSurprisal κ μ c) / Z := by
  have := isProbabilityMeasure_uniformOn (Set.finite_univ (α := C)) Set.univ_nonempty
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  rw [eq_channelCapacity_iff_eq_tilted, eq_tilted_iff]
  simp_rw [uniformOn_univ_real_singleton, ← neg_expectedSurprisal]
  constructor
  · rintro ⟨Z, hZ, h⟩
    refine ⟨Z * Fintype.card C, by positivity, fun c => ?_⟩
    rw [h]
    field_simp
  · rintro ⟨Z, hZ, h⟩
    refine ⟨Z / Fintype.card C, by positivity, fun c => ?_⟩
    rw [h]
    field_simp

end Capacity

/-! ### Naming systems from a hard clustering -/

/-- The naming system of a hard clustering: each color is named by the term of its cluster. -/
noncomputable abbrev ofPartition (f : C → W) : Kernel C W :=
  Kernel.deterministic f (measurable_of_finite f)

private theorem mem_preimage_self {α β : Type*} (f : α → β) (a : α) : a ∈ f ⁻¹' {f a} := rfl

private theorem ncard_preimage_pos {α β : Type*} [Finite α] (f : α → β) (a : α) :
    (0 : ℝ) < (f ⁻¹' {f a}).ncard := by
  exact_mod_cast (Set.ncard_pos (Set.toFinite _)).mpr ⟨a, mem_preimage_self f a⟩

theorem expectedSurprisal_ofPartition (f : C → W) (μ : Measure C) [IsProbabilityMeasure μ]
    {c : C} (hc : μ {c} ≠ 0) :
    expectedSurprisal (ofPartition f) μ c = log (μ.real (f ⁻¹' {f c})) - log (μ.real {c}) := by
  have hsub := Set.singleton_subset_iff.mpr (mem_preimage_self f c)
  have hF : μ (f ⁻¹' {f c}) ≠ 0 := fun h => hc (measure_mono_null hsub h)
  rw [expectedSurprisal, Kernel.deterministic_apply, integral_dirac, surprisal,
    posterior_deterministic_eq_cond μ _ hF,
    cond_real_apply μ (measurable_of_finite f (measurableSet_singleton _)),
    Set.inter_eq_right.mpr hsub, log_div, neg_sub]
  · rwa [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)]
  · rwa [Ne, measureReal_eq_zero_iff (measure_ne_top _ _)]

/-- Under a uniform need, the surprisal of a color in a clustering system is the log size of its
cluster (Fig. 3C). -/
theorem expectedSurprisal_ofPartition_uniformOn (f : C → W) (c : C) :
    expectedSurprisal (ofPartition f) (uniformOn Set.univ) c = log (f ⁻¹' {f c}).ncard := by
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  rw [expectedSurprisal_ofPartition f _ (uniformOn_univ_singleton_ne_zero c),
    uniformOn_real_apply, uniformOn_univ_real_singleton, Set.univ_inter, Set.ncard_univ,
    Nat.card_eq_fintype_card, log_div (ncard_preimage_pos f c).ne' hC.ne', log_inv]
  ring

/-- For a clustering system, the warm–cool asymmetry under a uniform need is an asymmetry in
mean log cluster size (Fig. 3C). -/
theorem warmCoolAsymmetry_ofPartition_uniformOn_iff (f : C → W) (temp : C → Temperature) :
    WarmCoolAsymmetry (ofPartition f) (uniformOn Set.univ) temp ↔
      (∑ c ∈ univ.filter (temp · = .warm), log (f ⁻¹' {f c}).ncard)
          / #(univ.filter (temp · = .warm))
        < (∑ c ∈ univ.filter (temp · = .cool), log (f ⁻¹' {f c}).ncard)
          / #(univ.filter (temp · = .cool)) := by
  simp only [WarmCoolAsymmetry, expectedSurprisal_ofPartition_uniformOn]

/-! ### The capacity-achieving prior of a clustering system -/

section ClusterPrior

variable [DecidableEq W]

private theorem card_image_pos {α β : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    (f : α → β) : (0 : ℝ) < #(univ.image f) := by
  exact_mod_cast card_pos.mpr (univ_nonempty.image f)

/-- The need distribution that spreads mass equally over the clusters of `f` and uniformly
within each: a capacity-achieving prior of one clustering system, of the kind averaged into
KM-CAP (Fig. 4B). -/
noncomputable def clusterPrior (f : C → W) : Measure C :=
  (#(univ.image f) : ℝ≥0∞)⁻¹ • ∑ w ∈ univ.image f, uniformOn (f ⁻¹' {w})

omit [Nonempty C] in
theorem clusterPrior_apply_singleton (f : C → W) (c : C) :
    clusterPrior f {c} = (#(univ.image f) : ℝ≥0∞)⁻¹ * ((f ⁻¹' {f c}).ncard : ℝ≥0∞)⁻¹ := by
  rw [clusterPrior, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    sum_eq_single_of_mem (f c) (mem_image_of_mem f (mem_univ c)), smul_eq_mul]
  · rw [uniformOn, cond_apply (measurable_of_finite f (measurableSet_singleton _)),
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (mem_preimage_self f c)),
      Measure.count_singleton, mul_one, Measure.count_apply_finite _ (Set.toFinite _),
      ← Set.ncard_eq_toFinset_card]
  · intro w _ hw
    rw [uniformOn, cond_apply (measurable_of_finite f (measurableSet_singleton _)),
      Set.inter_singleton_eq_empty.mpr (fun h => hw h.symm), measure_empty, mul_zero]

instance (f : C → W) : IsProbabilityMeasure (clusterPrior f) := by
  have hk : (#(univ.image f) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (card_pos.mpr (univ_nonempty.image f)).ne'
  constructor
  rw [clusterPrior, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    sum_congr rfl fun w hw => ?_, sum_const, nsmul_eq_mul, mul_one, smul_eq_mul,
    ENNReal.inv_mul_cancel hk (ENNReal.natCast_ne_top _)]
  obtain ⟨c, -, rfl⟩ := mem_image.mp hw
  have := isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨c, mem_preimage_self f c⟩
  exact measure_univ

omit [Nonempty C] in
theorem clusterPrior_real_singleton (f : C → W) (c : C) :
    (clusterPrior f).real {c} = ((#(univ.image f) : ℝ) * (f ⁻¹' {f c}).ncard)⁻¹ := by
  rw [measureReal_def, clusterPrior_apply_singleton, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_inv]

theorem clusterPrior_real_preimage (f : C → W) (c : C) :
    (clusterPrior f).real (f ⁻¹' {f c}) = (#(univ.image f) : ℝ)⁻¹ := by
  have hF := ncard_preimage_pos f c
  have hk := card_image_pos f
  rw [← (Set.toFinite (f ⁻¹' {f c})).coe_toFinset, ← sum_measureReal_singleton,
    sum_congr rfl (g := fun _ => ((#(univ.image f) : ℝ) * (f ⁻¹' {f c}).ncard)⁻¹)
      fun c' hc' => by
        rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hc'
        rw [clusterPrior_real_singleton, hc'],
    sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card]
  field_simp

theorem expectedSurprisal_ofPartition_clusterPrior (f : C → W) (c : C) :
    expectedSurprisal (ofPartition f) (clusterPrior f) c = log (f ⁻¹' {f c}).ncard := by
  rw [expectedSurprisal_ofPartition f _ ?_, clusterPrior_real_preimage,
    clusterPrior_real_singleton, log_inv, log_inv,
    log_mul (card_image_pos f).ne' (ncard_preimage_pos f c).ne']
  · ring
  · rw [clusterPrior_apply_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))

variable [Fintype W]

/-- The cluster prior satisfies eq. 5 with normalizer the number of terms, so it is a
capacity-achieving prior of the clustering system (Fig. 4B). -/
theorem capacityAchieving_clusterPrior (f : C → W) :
    Im[clusterPrior f ⊗ₘ ofPartition f] = channelCapacity (ofPartition f) := by
  refine ((capacityAchieving_iff _ _).mpr ⟨#(univ.image f), card_image_pos f, fun c => ?_⟩).1
  rw [clusterPrior_real_singleton, expectedSurprisal_ofPartition_clusterPrior, exp_neg,
    exp_log (ncard_preimage_pos f c), mul_inv, div_eq_mul_inv, mul_comm]

/-- The capacity of a `k`-term clustering system is `log k`: the intercept of eq. 6 at its
capacity-achieving prior. -/
theorem channelCapacity_ofPartition (f : C → W) :
    channelCapacity (ofPartition f) = log #(univ.image f) := by
  obtain ⟨c⟩ := ‹Nonempty C›
  have hμ (c : C) : clusterPrior f {c} ≠ 0 := by
    rw [clusterPrior_apply_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  have := neg_log_eq_add_channelCapacity _ _ (capacityAchieving_clusterPrior f) hμ c
  rw [clusterPrior_real_singleton, expectedSurprisal_ofPartition_clusterPrior, log_inv, neg_neg,
    log_mul (card_image_pos f).ne' (ncard_preimage_pos f c).ne'] at this
  linarith

end ClusterPrior

/-! ### The universal need distribution

Eq. 7 averages the per-language capacity-achieving priors into a universal need distribution,
following [zaslavsky-kemp-regier-tishby-2018]: it is that paper's least informative source
(`ZaslavskyKempRegierTishby2018.averagePrior`), whose per-language priors are the least
informative priors of the languages' naming distributions. -/

/-- The least informative priors of [zaslavsky-kemp-regier-tishby-2018] with positive mass are
exactly the need distributions satisfying eq. 5 (eq. 7). -/
theorem isLeastInformative_iff [Fintype W] (κ : Kernel C W) [IsMarkovKernel κ] (μ : Measure C)
    [IsProbabilityMeasure μ] :
    (ZaslavskyKempRegierTishby2018.IsLeastInformative μ κ ∧ ∀ c, μ {c} ≠ 0) ↔
      ∃ Z > 0, ∀ c, μ.real {c} = exp (-expectedSurprisal κ μ c) / Z := by
  rw [ZaslavskyKempRegierTishby2018.isLeastInformative_iff,
    ZaslavskyKempRegierTishby2018.complexity]
  exact capacityAchieving_iff κ μ

end ZaslavskyEtAl2019
