module

public import Linglib.Core.Analysis.SpecialFunctions.Gamma.Basic
public import Linglib.Core.Probability.Distributions.PolyaUrn
public import Linglib.Core.Probability.Kernel.OfWeights
public import Studies.GriffithsKalish2007

/-!
# Kirby, Dowman and Griffiths (2007): Innateness and culture in the evolution of language

A learner who adopts language $h$ with probability proportional to $[P(d \mid h)\,P(h)]^r$ [keeps
the prior stationary at $r = 1$](##invariant_exponentiatedPosterior_one). If every datum is
impossible or equally likely under each language, it is the posterior for the prior proportional
to $P(h)^r$, which it therefore [keeps stationary](##invariant_exponentiatedPosterior), [raising
the prior odds to the power $r$](##exponentiatedPrior_real_div), while MAP learners [keep the
uniform distribution on the prior's modes](##invariant_mapLearner). In the paper's model without
noise those are [the fully regular languages](##invariant_mapLearner_produce_zero), however weak
the bias; noise meets the condition [only at two degenerate levels](##constantOrZero_produce_iff).

## Implementation notes

* `exponentiatedPosterior` is the paper's "exponentiated posterior distribution". The paper names
  neither the normalized `P(h)^r` nor anything else here; `exponentiatedPrior` is our name, by
  analogy.
* `exponentiatedPosterior` gives the zero measure at a datum that no language of positive prior
  mass produces (`exponentiatedPosterior_apply_eq_zero`), so it is not a Markov kernel; the
  theorems use it only on the data the prior predicts. `mapLearner` ties every language there
  instead (`GriffithsKalish2007.mapLearner_apply`).
* The condition that `P(d|h)` be "either constant or zero across all hypotheses" is
  `ConstantOrZero`, stated without the constant: two languages that both give a datum positive
  probability give it the same.
* The exponent is positive: at `r = 0` the extended-real `0 ^ 0 = 1` would give positive weight to
  languages that cannot produce the datum.
* The paper assumes the chain on languages is ergodic. Invariance does not need it; uniqueness of
  the stationary distribution does.
* The distribution of meanings `P` is a parameter, uniform in the paper's Fig. 3 and Zipfian in its
  Fig. 4. Both figures are simulations and are not formalized; Fig. 3's `α` and `ε` are not
  reported.

## Errata

* Eq. (5) multiplies `Γ(n_k + α)` over `j`; the factor is `Γ(n_j + α)`, the count of class `j`
  ([`prior_real_singleton`](##prior_real_singleton)).
* The noisy model is said not to meet the condition "unless ε = 0". It also meets it at
  `ε = (k-1)/k`, where every class is produced with probability `1/k`, and at `ε = 1`, where a class
  is produced with probability `0` or `1/(k-1)`
  ([`constantOrZero_produce_iff`](##constantOrZero_produce_iff)).
* The proof that weak biases give strong universals assumes an ergodic chain, which its own MAP
  endpoint is not without noise: each fully regular language is a sink
  ([`invariant_mapLearner_dirac`](##invariant_mapLearner_dirac)).

## TODO

* On every datum some language of positive prior mass can produce, the limit of the exponentiated
  posterior as `r → ∞` is the MAP learner of [griffiths-kalish-2007], uniform on ties. The
  available limits of normalized powers (`Real.tendsto_softmax_atTop`,
  `RSA.tendsto_speaker_dirac_real_singleton_atTop`) assume a unique maximizer, which the fully
  regular languages are not.

## References

* [kirby-dowman-griffiths-2007]
* [griffiths-kalish-2007]
-/

@[expose] public section

namespace KirbyDowmanGriffiths2007

open MeasureTheory ProbabilityTheory Finset Filter
open GriffithsKalish2007 (mapLearner mapLearner_apply)
open scoped ENNReal

/-- The paper's condition that `P(d|h)` be "either constant or zero across all hypotheses": two
languages that both give a datum positive probability give it the same. -/
def ConstantOrZero {H D : Type*} [MeasurableSpace H] [MeasurableSpace D] (κ : Kernel H D) :
    Prop :=
  ∀ d h h', κ h {d} ≠ 0 → κ h' {d} ≠ 0 → κ h {d} = κ h' {d}

/-! ### The exponentiated posterior -/

section Exponentiated

variable {H D : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSpace D]

/-- p. 5243: the learner who adopts language `h` with probability proportional to
`[P(d|h) P(h)]^r`. -/
noncomputable def exponentiatedPosterior [Countable D] [MeasurableSingletonClass D]
    (κ : Kernel H D) (μ : Measure H) (r : ℝ) : Kernel D H :=
  Kernel.ofWeights fun d h ↦ (μ {h} * κ h {d}) ^ r

/-- Methods: the distribution `P(h)^r / ∑ h', P(h')^r`. -/
noncomputable def exponentiatedPrior (μ : Measure H) (r : ℝ) : Measure H :=
  (Measure.ofWeights fun h ↦ μ {h} ^ r)[|Set.univ]

instance (μ : Measure H) (r : ℝ) : IsFiniteMeasure (exponentiatedPrior μ r) :=
  inferInstanceAs (IsFiniteMeasure ((Measure.ofWeights _)[|Set.univ]))

theorem exponentiatedPosterior_apply_eq_zero [Countable D] [MeasurableSingletonClass D]
    [MeasurableSingletonClass H] {κ : Kernel H D} {μ : Measure H} {r : ℝ} (hr : 0 < r) {d : D}
    (hd : ∀ h, μ {h} * κ h {d} = 0) : exponentiatedPosterior κ μ r d = 0 :=
  Measure.ext_of_singleton fun h ↦ by
    simp [exponentiatedPosterior, hd, ENNReal.zero_rpow_of_pos hr]

private theorem sum_rpow_ne_zero (μ : Measure H) [IsFiniteMeasure μ] [NeZero μ] (r : ℝ) :
    (∑ h, μ {h} ^ r) ≠ 0 := by
  obtain ⟨h, hh⟩ := Measure.exists_measure_singleton_ne_zero μ
  exact fun h₀ ↦ (ENNReal.rpow_pos (pos_iff_ne_zero.2 hh) (measure_ne_top _ _)).ne'
    (sum_eq_zero_iff.1 h₀ h (mem_univ h))

private theorem sum_rpow_ne_top (μ : Measure H) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r) :
    (∑ h, μ {h} ^ r) ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.rpow_ne_top_of_nonneg hr (measure_ne_top _ _)

-- Under the condition, at a datum some mode of the prior can produce, the MAP choices are the
-- modes that can produce it.
private theorem argmax_eq_filter {κ : Kernel H D} [IsFiniteKernel κ] (hκ : ConstantOrZero κ)
    {μ : Measure H} [NeZero μ] {d : D} {h₀ : H} (h₀M : h₀ ∈ univ.argmax fun h ↦ μ {h})
    (hh₀ : κ h₀ {d} ≠ 0) :
    univ.argmax (fun h ↦ μ {h} * κ h {d}) =
      (univ.argmax fun h ↦ μ {h}).filter (κ · {d} ≠ 0) := by
  have hμ₀ : μ {h₀} ≠ 0 := by
    obtain ⟨h', hh'⟩ := Measure.exists_measure_singleton_ne_zero μ
    exact fun h₁ ↦ hh' (le_antisymm (h₁ ▸ (mem_argmax.1 h₀M).2 h' (mem_univ _)) zero_le)
  ext h
  simp only [mem_argmax, mem_univ, true_and, mem_filter]
  refine ⟨fun hmax ↦ ?_, fun ⟨hm, hne⟩ h' _ ↦ ?_⟩
  · have hle := hmax h₀ trivial
    have hne : κ h {d} ≠ 0 := fun h₁ ↦ by
      rw [h₁, mul_zero, nonpos_iff_eq_zero] at hle
      exact mul_ne_zero hμ₀ hh₀ hle
    rw [hκ d h h₀ hne hh₀, ENNReal.mul_le_mul_iff_left hh₀ (measure_ne_top _ _)] at hle
    exact ⟨fun h' _ ↦ ((mem_argmax.1 h₀M).2 h' (mem_univ _)).trans hle, hne⟩
  · rw [hκ d h h₀ hne hh₀]
    by_cases h₁ : κ h' {d} = 0
    · simp [h₁]
    · rw [hκ d h' h₀ h₁ hh₀]
      exact mul_le_mul_left (hm h' trivial) _

variable [MeasurableSingletonClass H]

theorem exponentiatedPrior_apply_singleton (μ : Measure H) (r : ℝ) (h : H) :
    exponentiatedPrior μ r {h} = (∑ h', μ {h'} ^ r)⁻¹ * μ {h} ^ r := by
  rw [exponentiatedPrior, cond_apply .univ, Set.univ_inter, Measure.ofWeights_apply_singleton,
    ← coe_univ, Measure.ofWeights_apply_finset]

theorem isProbabilityMeasure_exponentiatedPrior (μ : Measure H) [IsProbabilityMeasure μ] {r : ℝ}
    (hr : 0 ≤ r) : IsProbabilityMeasure (exponentiatedPrior μ r) := by
  have hZ : Measure.ofWeights (fun h ↦ μ {h} ^ r) Set.univ = ∑ h, μ {h} ^ r := by
    rw [← coe_univ, Measure.ofWeights_apply_finset]
  exact cond_isProbabilityMeasure_of_finite (hZ ▸ sum_rpow_ne_zero μ r)
    (hZ ▸ sum_rpow_ne_top μ hr)

/-- p. 5244, "systematically overrepresented": the stationary distribution proportional to
`P(h)^r` raises the prior odds between any two languages to the power `r`. -/
theorem exponentiatedPrior_real_div (μ : Measure H) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (h h' : H) :
    (exponentiatedPrior μ r).real {h'} / (exponentiatedPrior μ r).real {h} =
      (μ.real {h'} / μ.real {h}) ^ r := by
  have hZ : ((∑ h, μ {h} ^ r)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (sum_rpow_ne_top μ hr.le),
      ENNReal.inv_ne_top.2 (sum_rpow_ne_zero μ r)⟩
  simp only [measureReal_def, exponentiatedPrior_apply_singleton, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow]
  rw [mul_div_mul_left _ _ hZ, Real.div_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

-- p. 5244: for `r > 1` the less probable of two languages loses ground.
theorem exponentiatedPrior_real_div_lt (μ : Measure H) [IsProbabilityMeasure μ] {r : ℝ}
    (hr : 1 < r) {h h' : H} (h₀ : 0 < μ.real {h'}) (hlt : μ.real {h'} < μ.real {h}) :
    (exponentiatedPrior μ r).real {h'} / (exponentiatedPrior μ r).real {h} <
      μ.real {h'} / μ.real {h} := by
  rw [exponentiatedPrior_real_div μ (by linarith) h h']
  exact Real.rpow_lt_self_of_lt_one (div_pos h₀ (h₀.trans hlt)) ((div_lt_one (h₀.trans hlt)).2 hlt)
    hr

variable [Countable D] [MeasurableSingletonClass D] [Nonempty H] (κ : Kernel H D)
  [IsMarkovKernel κ] (μ : Measure H) [IsProbabilityMeasure μ]

-- p. 5243: at `r = 1` the learner samples from the posterior, whose stationary distribution is
-- the prior [griffiths-kalish-2007].
theorem invariant_exponentiatedPosterior_one : (exponentiatedPosterior κ μ 1 ∘ₖ κ).Invariant μ :=
  invariant_comp_of_ae_eq_posterior <| ae_iff_of_countable.2 fun d hd ↦
    Measure.ext_of_singleton fun h ↦ by
      simp only [exponentiatedPosterior, Kernel.ofWeights_apply_singleton, ENNReal.rpow_one,
        posterior_apply_singleton κ μ hd, Measure.comp_apply_singleton]

/-- Methods, eqs. (6)–(10): if every datum is either impossible or equally likely under each
language, iterated learning with the exponentiated posterior has a stationary distribution
proportional to `P(h)^r`. The learner is the posterior under that distribution, so the result is
[griffiths-kalish-2007]'s at a different prior. -/
theorem invariant_exponentiatedPosterior (hκ : ConstantOrZero κ) {r : ℝ} (hr : 0 < r) :
    (exponentiatedPosterior κ μ r ∘ₖ κ).Invariant (exponentiatedPrior μ r) := by
  refine invariant_comp_of_ae_eq_posterior (ae_eq_posterior_of_eq_of_ne_zero κ _ hκ (μ {·} ^ r)
    (ENNReal.inv_ne_zero.2 (sum_rpow_ne_top μ hr.le)) (ENNReal.inv_ne_top.2 (sum_rpow_ne_zero μ r))
    (exponentiatedPrior_apply_singleton μ r) fun d hd h ↦ ?_)
  obtain ⟨h₀, -, hh₀⟩ := (Measure.comp_apply_singleton_ne_zero_iff κ _).1 hd
  have key (h : H) : (μ {h} * κ h {d}) ^ r =
      κ h₀ {d} ^ r * if κ h {d} = 0 then 0 else μ {h} ^ r := by
    by_cases h₁ : κ h {d} = 0
    · simp [h₁, ENNReal.zero_rpow_of_pos hr]
    · simp only [h₁, ↓reduceIte]
      rw [hκ d h h₀ h₁ hh₀, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
      ring
  simp only [exponentiatedPosterior, Kernel.ofWeights_apply_singleton, key]
  rw [← mul_sum, ENNReal.mul_div_mul_left _ _
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hh₀) (measure_ne_top _ _)).ne'
    (ENNReal.rpow_ne_top_of_nonneg hr.le (measure_ne_top _ _))]

-- Under the condition, MAP learners keep the uniform distribution on any set `S` of modes of the
-- prior that holds every mode producing a datum some member of `S` produces.
theorem invariant_mapLearner_uniformOn (hκ : ConstantOrZero κ) {S : Finset H} (hS : S.Nonempty)
    (hSM : S ⊆ univ.argmax fun h ↦ μ {h})
    (hSc : ∀ d, ∀ a ∈ S, κ a {d} ≠ 0 → ∀ h ∈ univ.argmax (fun h ↦ μ {h}), κ h {d} ≠ 0 → h ∈ S) :
    (mapLearner κ μ ∘ₖ κ).Invariant (uniformOn ↑S) := by
  classical
  have hS₀ : (#S : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 hS).ne'
  refine invariant_comp_of_ae_eq_posterior (ae_eq_posterior_of_eq_of_ne_zero κ _ hκ
    (fun h ↦ if h ∈ S then 1 else 0) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    (ENNReal.inv_ne_top.2 hS₀) (fun h ↦ ?_) fun d hd h ↦ ?_)
  · rw [uniformOn_finset_apply_singleton]
    split_ifs <;> simp
  obtain ⟨h₀, hν₀, hh₀⟩ := (Measure.comp_apply_singleton_ne_zero_iff κ _).1 hd
  have h₀S : h₀ ∈ S := by
    by_contra h₀S
    exact hν₀ (by simp [uniformOn_finset_apply_singleton, h₀S])
  have hfilter : (univ.argmax fun h ↦ μ {h}).filter (κ · {d} ≠ 0) = S.filter (κ · {d} ≠ 0) := by
    ext h
    simp only [mem_filter]
    exact ⟨fun ⟨hM, hd'⟩ ↦ ⟨hSc d h₀ h₀S hh₀ h hM hd', hd'⟩, fun ⟨hS', hd'⟩ ↦ ⟨hSM hS', hd'⟩⟩
  have hite (h : H) : (if κ h {d} = 0 then 0 else if h ∈ S then 1 else 0 : ℝ≥0∞) =
      if h ∈ S.filter (κ · {d} ≠ 0) then 1 else 0 := by
    by_cases h₁ : κ h {d} = 0 <;> by_cases hm : h ∈ S <;> simp [h₁, hm]
  rw [mapLearner_apply, argmax_eq_filter hκ (hSM h₀S) hh₀, hfilter,
    uniformOn_finset_apply_singleton, hite]
  simp_rw [hite]
  rw [sum_boole, filter_mem_eq_inter, univ_inter]
  split_ifs <;> simp

/-- The `r = ∞` endpoint: if every datum is either impossible or equally likely under each
language, iterated learning by MAP estimation has the uniform distribution on the modes of the
prior as a stationary distribution. Two priors with the same modes, one weak and one strong, give
the same one. -/
theorem invariant_mapLearner (hκ : ConstantOrZero κ) :
    (mapLearner κ μ ∘ₖ κ).Invariant (uniformOn ↑(univ.argmax fun h ↦ μ {h})) :=
  invariant_mapLearner_uniformOn κ μ hκ (argmax_nonempty univ_nonempty) subset_rfl
    fun _ _ _ _ _ hh _ ↦ hh

end Exponentiated

/-! ### The meaning-class model

A language assigns each of `n` meanings one of `k` classes. A learner sees `m` pairs of a meaning,
drawn from `P`, and the class produced for it, which is the language's class with probability
`1 - ε` and each other class with probability `ε / (k - 1)`. -/

section MeaningClass

variable {n k m : ℕ}

/-- Eq. (5): the prior over languages, the law of `n` draws from the Pólya urn with weight `α` on
each class. Small `α` favours languages that use few classes. -/
noncomputable def prior (α : ℝ) : Measure (Fin n → Fin k) :=
  polyaUrn (fun _ ↦ α) n

theorem isProbabilityMeasure_prior [NeZero k] {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (prior (n := n) (k := k) α) :=
  isProbabilityMeasure_polyaUrn (fun _ ↦ hα) n

/-- Eqs. (3)–(4): the data produced by a language. -/
noncomputable def produce (P : Measure (Fin n)) (ε : ℝ) :
    Kernel (Fin n → Fin k) (Fin m → Fin n × Fin k) :=
  Kernel.ofFunOfCountable fun h ↦ Measure.pi fun _ ↦ Measure.ofRealWeights fun d ↦
    P.real {d.1} * if d.2 = h d.1 then 1 - ε else ε / (k - 1)

theorem produce_apply_singleton (P : Measure (Fin n)) (ε : ℝ) (h : Fin n → Fin k)
    (d : Fin m → Fin n × Fin k) :
    produce P ε h {d} = ∏ i, ENNReal.ofReal
      (P.real {(d i).1} * if (d i).2 = h (d i).1 then 1 - ε else ε / (k - 1)) := by
  rw [produce, Kernel.ofFunOfCountable_apply, Measure.pi_singleton]
  simp only [Measure.ofRealWeights, Measure.ofWeights_apply_singleton]

private theorem sub_one_pos (hk : 2 ≤ k) : (0 : ℝ) < k - 1 := by
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

private theorem sum_ite_class {ε : ℝ} (hk : 2 ≤ k) (a : Fin k) :
    ∑ y : Fin k, (if y = a then 1 - ε else ε / (k - 1)) = 1 := by
  have hk' : (k : ℝ) - 1 ≠ 0 := (sub_one_pos hk).ne'
  rw [show (fun y : Fin k ↦ if y = a then 1 - ε else ε / (k - 1)) =
      fun y ↦ ε / (k - 1) + if y = a then 1 - ε - ε / (k - 1) else 0 by
    ext y; split_ifs <;> ring]
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, sum_ite_eq']
  simp only [mem_univ, ite_true, nsmul_eq_mul]
  field_simp
  ring

theorem isMarkovKernel_produce (P : Measure (Fin n)) [IsProbabilityMeasure P] {ε : ℝ}
    (hk : 2 ≤ k) (h₀ : 0 ≤ ε) (h₁ : ε ≤ 1) :
    IsMarkovKernel (produce (n := n) (k := k) (m := m) P ε) := by
  have hk' := sub_one_pos hk
  refine ⟨fun h ↦ ?_⟩
  have : ∀ i : Fin m, IsProbabilityMeasure (Measure.ofRealWeights fun d : Fin n × Fin k ↦
      P.real {d.1} * if d.2 = h d.1 then 1 - ε else ε / (k - 1)) := fun _ ↦ by
    refine Measure.isProbabilityMeasure_ofRealWeights
      (fun d ↦ mul_nonneg measureReal_nonneg (by split_ifs <;> first | linarith | positivity)) ?_
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, sum_ite_class hk, mul_one]
    rw [sum_measureReal_singleton, coe_univ, probReal_univ]
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

-- Eq. (5), with `#{i | h i = j}` the number of meanings expressed by class `j`.
theorem prior_real_singleton [NeZero k] {α : ℝ} (hα : 0 < α) (h : Fin n → Fin k) :
    (prior α).real {h} = Real.Gamma (k * α) / (Real.Gamma α ^ k * Real.Gamma (k * α + n)) *
      ∏ j, Real.Gamma (α + #{i | h i = j}) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hΓ := (Real.Gamma_pos_of_pos hα).ne'
  have hΓk := (Real.Gamma_pos_of_pos (mul_pos hk hα)).ne'
  have hx {x : ℝ} (hx : 0 < x) (j : ℕ) : x ≠ -j := ((neg_nonpos.2 j.cast_nonneg).trans_lt hx).ne'
  rw [prior, polyaUrn_real_singleton (fun _ ↦ hα), polyaUrnProb, sum_countVec, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Real.Gamma_add_nat_div_Gamma_eq _ (hx (mul_pos hk hα))]
  simp_rw [← Real.Gamma_add_nat_div_Gamma_eq _ (hx hα), countVec]
  rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
  field_simp

-- At no noise, at the noise `(k - 1) / k` and at noise one, every datum has the same
-- probability under each language that can produce it.
private theorem produce_eq_of_ne_zero (P : Measure (Fin n)) {ε : ℝ} (hk : 2 ≤ k)
    (hε : ε = 0 ∨ ε = (k - 1) / k ∨ ε = 1) {d : Fin m → Fin n × Fin k} {h : Fin n → Fin k}
    (hh : produce P ε h {d} ≠ 0) :
    produce P ε h {d} = ∏ i, ENNReal.ofReal
      (P.real {(d i).1} * if ε = 1 then 1 / ((k : ℝ) - 1) else 1 - ε) := by
  have hk' : (k : ℝ) - 1 ≠ 0 := (sub_one_pos hk).ne'
  have hk₀ : (k : ℝ) ≠ 0 := by positivity
  have hg (b : Prop) [Decidable b] : (if b then 1 - ε else ε / (k - 1)) = 0 ∨
      (if b then 1 - ε else ε / (k - 1)) = if ε = 1 then 1 / ((k : ℝ) - 1) else 1 - ε := by
    rcases hε with rfl | rfl | rfl
    · split_ifs <;> simp_all
    · have : ((k : ℝ) - 1) / k ≠ 1 := fun h ↦ by field_simp at h; linarith
      right
      split_ifs
      · rfl
      · field_simp
        ring
    · split_ifs <;> simp_all
  rw [produce_apply_singleton] at hh ⊢
  refine prod_congr rfl fun i _ ↦ ?_
  rcases hg ((d i).2 = h (d i).1) with h₀ | h₀
  · exact absurd (prod_eq_zero (mem_univ i) (by rw [h₀, mul_zero, ENNReal.ofReal_zero])) hh
  · rw [h₀]

-- Without noise, at the noise `(k - 1) / k` and at noise one, the model meets the condition.
theorem constantOrZero_produce (P : Measure (Fin n)) {ε : ℝ} (hk : 2 ≤ k)
    (hε : ε = 0 ∨ ε = (k - 1) / k ∨ ε = 1) : ConstantOrZero (produce (k := k) (m := m) P ε) :=
  fun _ _ _ hh hh' ↦ by rw [produce_eq_of_ne_zero P hk hε hh, produce_eq_of_ne_zero P hk hε hh']

/-- Methods: the noisy meaning-class model meets the condition of `invariant_exponentiatedPosterior`
exactly when there is no noise, when every class is produced with probability `1/k`, or when the
language's own class is never produced. -/
theorem constantOrZero_produce_iff (P : Measure (Fin n)) [IsProbabilityMeasure P] {ε : ℝ}
    (hk : 2 ≤ k) (hm : m ≠ 0) (h₀ : 0 ≤ ε) (h₁ : ε ≤ 1) :
    ConstantOrZero (produce (k := k) (m := m) P ε) ↔ ε = 0 ∨ ε = (k - 1) / k ∨ ε = 1 := by
  refine ⟨fun hc ↦ ?_, constantOrZero_produce P hk⟩
  by_contra hε
  simp only [not_or] at hε
  obtain ⟨hε₀, hεk, hε₁⟩ := hε
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨x, hx⟩ := Measure.exists_measure_singleton_ne_zero P
  have hp : 0 < P.real {x} := ENNReal.toReal_pos hx (measure_ne_top _ _)
  let c₀ : Fin k := ⟨0, by omega⟩
  let c₁ : Fin k := ⟨1, by omega⟩
  have hc₀₁ : c₀ ≠ c₁ := by simp [c₀, c₁, Fin.ext_iff]
  have ha : 0 < P.real {x} * (1 - ε) := mul_pos hp (sub_pos.2 (h₁.lt_of_ne hε₁))
  have hb : 0 < P.real {x} * (ε / (k - 1)) :=
    mul_pos hp (div_pos (h₀.lt_of_ne (Ne.symm hε₀)) (by linarith))
  have := hc (fun _ ↦ (x, c₀)) (fun _ ↦ c₀) (fun _ ↦ c₁)
  simp only [produce_apply_singleton, ↓reduceIte, hc₀₁, prod_const, card_univ,
    Fintype.card_fin] at this
  have heq := congrArg ENNReal.toReal (this (pow_ne_zero _ (ENNReal.ofReal_pos.2 ha).ne')
    (pow_ne_zero _ (ENNReal.ofReal_pos.2 hb).ne'))
  rw [ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal hb.le, pow_left_inj₀ ha.le hb.le hm, mul_right_inj' hp.ne'] at heq
  exact hεk (by field_simp at heq ⊢; linarith)

-- The modes of the prior (5) are the fully regular languages, which express every meaning by the
-- same class, whatever the bias strength `α`.
theorem argmax_prior [NeZero k] {α : ℝ} (hα : 0 < α) :
    univ.argmax (fun h : Fin n → Fin k ↦ prior α {h}) = univ.image fun j _ ↦ j :=
  argmax_polyaUrn_const hα n

-- Without noise, a language can produce only data that pair each meaning with its class.
private theorem eq_of_produce_zero_apply_ne_zero (P : Measure (Fin n)) {h : Fin n → Fin k}
    {d : Fin m → Fin n × Fin k} (hh : produce P 0 h {d} ≠ 0) (i : Fin m) : (d i).2 = h (d i).1 := by
  rw [produce_apply_singleton] at hh
  by_contra hi
  exact hh (prod_eq_zero (mem_univ i) (by simp [hi]))

/-- The meaning-class model without noise: for every bias strength `α`, iterated learning by MAP
estimation has the uniform distribution on the fully regular languages as a stationary
distribution. Sampling learners keep the prior instead, which depends on `α`
(`invariant_exponentiatedPosterior_one`). -/
theorem invariant_mapLearner_produce_zero (P : Measure (Fin n)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) {α : ℝ} (hα : 0 < α) :
    (mapLearner (produce (m := m) P 0) (prior α) ∘ₖ produce P 0).Invariant
      (uniformOn (Set.range fun j : Fin k ↦ fun _ : Fin n ↦ j)) := by
  have : NeZero k := ⟨by omega⟩
  have := isMarkovKernel_produce (m := m) P hk le_rfl zero_le_one
  have := isProbabilityMeasure_prior (n := n) (k := k) hα
  have h := invariant_mapLearner (produce (m := m) P 0) (prior α)
    (constantOrZero_produce P hk (.inl rfl))
  rwa [argmax_prior hα, coe_image, coe_univ, Set.image_univ] at h

-- Errata: without noise each fully regular language is a sink of the MAP chain, so its
-- stationary distribution is not unique and the chain is not ergodic.
theorem invariant_mapLearner_dirac (P : Measure (Fin n)) [IsProbabilityMeasure P] (hk : 2 ≤ k)
    (hm : m ≠ 0) {α : ℝ} (hα : 0 < α) (j : Fin k) :
    (mapLearner (produce (m := m) P 0) (prior α) ∘ₖ produce P 0).Invariant
      (Measure.dirac fun _ : Fin n ↦ j) := by
  have : NeZero k := ⟨by omega⟩
  have := isMarkovKernel_produce (m := m) P hk le_rfl zero_le_one
  have := isProbabilityMeasure_prior (n := n) (k := k) hα
  have hδ : uniformOn ↑({fun _ ↦ j} : Finset (Fin n → Fin k)) =
      Measure.dirac fun _ : Fin n ↦ j := by
    classical
    ext s hs
    rw [coe_singleton, uniformOn_singleton, Measure.dirac_apply' _ hs, Set.indicator_apply,
      Pi.one_apply]
  have hSc : ∀ d : Fin m → Fin n × Fin k, ∀ a ∈ ({fun _ ↦ j} : Finset (Fin n → Fin k)),
      produce P 0 a {d} ≠ 0 →
      ∀ h ∈ univ.argmax (fun h ↦ prior α {h}), produce P 0 h {d} ≠ 0 →
        h ∈ ({fun _ ↦ j} : Finset (Fin n → Fin k)) := by
    intro d a ha hka h hh hkh
    rw [mem_singleton] at ha ⊢
    subst ha
    rw [argmax_prior hα, mem_image] at hh
    obtain ⟨j', _, rfl⟩ := hh
    have i₀ : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    have h₁ := eq_of_produce_zero_apply_ne_zero P hkh i₀
    have h₂ := eq_of_produce_zero_apply_ne_zero P hka i₀
    funext i
    exact h₁.symm.trans h₂
  rw [← hδ]
  exact invariant_mapLearner_uniformOn (produce (m := m) P 0) (prior α)
    (constantOrZero_produce P hk (.inl rfl))
    (singleton_nonempty _) (by
      rw [argmax_prior hα, singleton_subset_iff]
      exact mem_image.2 ⟨j, mem_univ _, rfl⟩) hSc

/-- With two meanings and two classes, MAP learners without noise have a stationary distribution
that gives each fully regular language probability `1/2` and the language giving each meaning its
own class probability `0`, although the prior gives that language positive mass. -/
example (P : Measure (Fin 2)) [IsProbabilityMeasure P] {α : ℝ} (hα : 0 < α) :
    (mapLearner (produce (k := 2) (m := 3) P 0) (prior α) ∘ₖ produce P 0).Invariant
        (uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j)) ∧
      uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j) {fun _ ↦ 0} = 2⁻¹ ∧
      uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j) {fun i ↦ i} = 0 ∧
      prior α {fun i : Fin 2 ↦ i} ≠ 0 := by
  have hmem : (fun _ : Fin 2 ↦ (0 : Fin 2)) ∈ univ.image fun j (_ : Fin 2) ↦ j := by decide
  have hnmem : (fun i : Fin 2 ↦ i) ∉ univ.image fun j (_ : Fin 2) ↦ j := by decide
  have hcard : #(univ.image fun j (_ : Fin 2) ↦ (j : Fin 2)) = 2 := by decide
  refine ⟨invariant_mapLearner_produce_zero P le_rfl hα, ?_, ?_, ?_⟩
  · rw [← Set.image_univ, ← coe_univ, ← coe_image, uniformOn_finset_apply_singleton]
    simp [hmem, hcard]
  · rw [← Set.image_univ, ← coe_univ, ← coe_image, uniformOn_finset_apply_singleton]
    simp [hnmem]
  · rw [prior, polyaUrn_singleton (fun _ ↦ hα)]
    exact (ENNReal.ofReal_pos.2 (polyaUrnProb_pos (fun _ ↦ hα) _)).ne'

/-- The condition of `invariant_exponentiatedPosterior` is met without noise, so learners with
exponent `2` keep the squared prior, a probability measure, stationary. -/
example (P : Measure (Fin 2)) [IsProbabilityMeasure P] {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (exponentiatedPrior (prior (n := 2) (k := 2) α) 2) ∧
      (exponentiatedPosterior (produce (k := 2) (m := 3) P 0) (prior α) 2 ∘ₖ
        produce P 0).Invariant (exponentiatedPrior (prior α) 2) := by
  have := isMarkovKernel_produce (k := 2) (m := 3) P le_rfl le_rfl zero_le_one
  have := isProbabilityMeasure_prior (n := 2) (k := 2) hα
  exact ⟨isProbabilityMeasure_exponentiatedPrior _ zero_le_two,
    invariant_exponentiatedPosterior _ _ (constantOrZero_produce P le_rfl (.inl rfl)) two_pos⟩

/-- A strong bias (`α = 1/100`) and a weak one (`α = 100`) give MAP learners the same stationary
distribution, uniform on the two fully regular languages. -/
example (P : Measure (Fin 2)) [IsProbabilityMeasure P] :
    (mapLearner (produce (k := 2) (m := 3) P 0) (prior (1 / 100)) ∘ₖ produce P 0).Invariant
        (uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j)) ∧
      (mapLearner (produce (k := 2) (m := 3) P 0) (prior 100) ∘ₖ produce P 0).Invariant
        (uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j)) :=
  ⟨invariant_mapLearner_produce_zero P le_rfl (by norm_num),
    invariant_mapLearner_produce_zero P le_rfl (by norm_num)⟩

/-- With four classes, noise `1/10` breaks the condition and noise `3/4` keeps it. -/
example (P : Measure (Fin 2)) [IsProbabilityMeasure P] :
    ¬ ConstantOrZero (produce (k := 4) (m := 1) P (1 / 10)) ∧
      ConstantOrZero (produce (k := 4) (m := 1) P (3 / 4)) := by
  refine ⟨fun h ↦ ?_, constantOrZero_produce P (by norm_num) (.inr (.inl (by norm_num)))⟩
  rcases (constantOrZero_produce_iff P (k := 4) (m := 1) (ε := 1 / 10) (by norm_num) one_ne_zero
    (by norm_num) (by norm_num)).1 h with h | h | h <;> norm_num at h

/-- With two meanings, two classes and `α = 1`, the prior makes a fully regular language twice as
likely as the language giving each meaning its own class; squaring makes it four times as likely. -/
example : (exponentiatedPrior (prior (n := 2) (k := 2) 1) 2).real {fun i ↦ i} /
    (exponentiatedPrior (prior (n := 2) (k := 2) 1) 2).real {fun _ ↦ 0} = (1 / 2) ^ (2 : ℝ) := by
  have := isProbabilityMeasure_prior (n := 2) (k := 2) one_pos
  have h₁ : countVec (fun i : Fin 2 ↦ i) = fun _ ↦ 1 := by decide
  have h₂ : countVec (fun _ : Fin 2 ↦ (0 : Fin 2)) = fun j ↦ if j = 0 then 2 else 0 := by decide
  rw [exponentiatedPrior_real_div _ two_pos, prior, polyaUrn_real_singleton (fun _ ↦ one_pos),
    polyaUrn_real_singleton (fun _ ↦ one_pos), h₁, h₂]
  norm_num [polyaUrnProb, Fin.prod_univ_two, ascPochhammer_succ_eval]

end MeaningClass

end KirbyDowmanGriffiths2007
