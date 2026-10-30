module

public import Linglib.Core.Probability.Distributions.PolyaUrn
public import Linglib.Core.Probability.Kernel.OfWeights
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Studies.GriffithsKalish2007

/-!
# Kirby, Dowman and Griffiths (2007): Innateness and culture in the evolution of language

A learner who adopts language $h$ with probability proportional to $[P(d \mid h)\,P(h)]^r$
samples from the posterior at $r = 1$ and maximizes it as $r \to \infty$. If every datum is
impossible or equally likely under each language, this learner is the posterior for the prior
proportional to $P(h)^r$, so iterated learning [keeps that prior
stationary](##invariant_exponentiatedPosterior), which [raises the odds to the power
$r$](##exponentiatedPrior_real_div); at $r = \infty$ [the uniform distribution on the prior's
modes](##invariant_mapLearner) is stationary, however weak the bias. Without noise, MAP learners of
the paper's meaning-class model have [a stationary distribution on the fully regular languages
alone](##invariant_mapLearner_produce_zero); with noise the model [meets the condition only at two
degenerate levels](##constant_or_zero_iff).

## Implementation notes

* `exponentiatedPosterior` is the paper's "exponentiated posterior distribution". The paper names
  neither the normalized `P(h)^r` nor anything else here; `exponentiatedPrior` is our name, by
  analogy.
* The condition that `P(d|h)` be "either constant or zero across all hypotheses" is the hypothesis
  `hκ`, stated without the constant: two languages that both give a datum positive probability
  give it the same.
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
  is produced with probability `0` or `1/(k-1)` ([`constant_or_zero_iff`](##constant_or_zero_iff)).
* The proof that weak biases give strong universals assumes an ergodic chain, which its own MAP
  endpoint is not without noise: each fully regular language is a sink
  ([`invariant_mapLearner_dirac`](##invariant_mapLearner_dirac)).

## TODO

* The limit of the exponentiated posterior as `r → ∞` is the MAP learner of
  [griffiths-kalish-2007], uniform on ties. The available limits of normalized powers
  (`Real.tendsto_softmax_atTop`, `RSA.tendsto_speaker_dirac_real_singleton_atTop`) assume a unique
  maximizer, which the fully regular languages are not.

## References

* [kirby-dowman-griffiths-2007]
* [griffiths-kalish-2007]
-/

@[expose] public section

namespace KirbyDowmanGriffiths2007

open MeasureTheory ProbabilityTheory Finset Filter
open GriffithsKalish2007 (mapLearner mapLearner_apply invariant_comp_of_ae_eq_posterior)
open scoped ENNReal

/-! ### The exponentiated posterior -/

section Exponentiated

variable {H D : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
  [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]

/-- p. 5243: the learner who adopts language `h` with probability proportional to
`[P(d|h) P(h)]^r`. -/
noncomputable def exponentiatedPosterior (κ : Kernel H D) (μ : Measure H) (r : ℝ) : Kernel D H :=
  Kernel.ofWeights fun d h ↦ (μ {h} * κ h {d}) ^ r

/-- Methods: the distribution `P(h)^r / ∑ h', P(h')^r`. -/
noncomputable def exponentiatedPrior (μ : Measure H) (r : ℝ) : Measure H :=
  (Measure.ofWeights fun h ↦ μ {h} ^ r)[|Set.univ]

instance (μ : Measure H) (r : ℝ) : IsFiniteMeasure (exponentiatedPrior μ r) :=
  inferInstanceAs (IsFiniteMeasure ((Measure.ofWeights _)[|Set.univ]))

theorem exponentiatedPrior_apply_singleton (μ : Measure H) (r : ℝ) (h : H) :
    exponentiatedPrior μ r {h} = (∑ h', μ {h'} ^ r)⁻¹ * μ {h} ^ r := by
  rw [exponentiatedPrior, cond_apply .univ, Set.univ_inter, Measure.ofWeights_apply_singleton,
    ← coe_univ, Measure.ofWeights_apply_finset]

variable (κ : Kernel H D) (μ : Measure H)

omit [Countable D] in
private theorem exists_of_comp_apply_ne_zero {ν : Measure H} {d : D} (hd : (κ ∘ₘ ν) {d} ≠ 0) :
    ∃ h, ν {h} ≠ 0 ∧ κ h {d} ≠ 0 := by
  rw [Measure.comp_apply_singleton] at hd
  obtain ⟨h, -, hh⟩ := exists_ne_zero_of_sum_ne_zero hd
  exact ⟨h, left_ne_zero_of_mul hh, right_ne_zero_of_mul hh⟩

omit [MeasurableSingletonClass H] in
private theorem exists_apply_ne_zero [IsProbabilityMeasure μ] : ∃ h, μ {h} ≠ 0 := by
  by_contra! h₀
  exact NeZero.ne μ (Measure.ext_of_singleton fun h ↦ by simp [h₀ h])

omit [MeasurableSingletonClass H] in
private theorem sum_rpow_ne_zero [IsProbabilityMeasure μ] (r : ℝ) : (∑ h, μ {h} ^ r) ≠ 0 := by
  obtain ⟨h, hh⟩ := exists_apply_ne_zero μ
  exact fun h₀ ↦ (ENNReal.rpow_pos (pos_iff_ne_zero.2 hh) (measure_ne_top _ _)).ne'
    (sum_eq_zero_iff.1 h₀ h (mem_univ h))

omit [MeasurableSingletonClass H] in
private theorem sum_rpow_ne_top {r : ℝ} (hr : 0 ≤ r) [IsFiniteMeasure μ] :
    (∑ h, μ {h} ^ r) ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.rpow_ne_top_of_nonneg hr (measure_ne_top _ _)

variable [StandardBorelSpace H] [Nonempty H]

-- Under the condition, a learner that normalizes weights `w` over the languages consistent with
-- the datum is the posterior under a prior proportional to `w`, on the data that prior predicts.
private theorem ae_eq_posterior_of_weights
    (hκ : ∀ d h h', κ h {d} ≠ 0 → κ h' {d} ≠ 0 → κ h {d} = κ h' {d})
    {ν : Measure H} [IsFiniteMeasure ν] [IsFiniteKernel κ] {L : Kernel D H} (w : H → ℝ≥0∞)
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) (hν : ∀ h, ν {h} = c * w h)
    (hL : ∀ d, (κ ∘ₘ ν) {d} ≠ 0 → ∀ h, L d {h} =
      (if κ h {d} = 0 then 0 else w h) / ∑ h', if κ h' {d} = 0 then 0 else w h') :
    L =ᵐ[κ ∘ₘ ν] κ†ν := by
  refine ae_iff_of_countable.2 fun d hd ↦ Measure.ext_of_singleton fun h ↦ ?_
  obtain ⟨h₀, -, hh₀⟩ := exists_of_comp_apply_ne_zero κ hd
  have key (h : H) : ν {h} * κ h {d} = (c * κ h₀ {d}) * if κ h {d} = 0 then 0 else w h := by
    by_cases h₁ : κ h {d} = 0
    · simp [h₁]
    · simp only [h₁, ↓reduceIte]
      rw [hν, hκ d h h₀ h₁ hh₀]
      ring
  have hsum : (κ ∘ₘ ν) {d} = (c * κ h₀ {d}) * ∑ h', if κ h' {d} = 0 then 0 else w h' := by
    rw [Measure.comp_apply_singleton, mul_sum]
    exact sum_congr rfl fun h _ ↦ key h
  rw [hL d hd h, posterior_apply_singleton κ ν hd h, key, hsum,
    ENNReal.mul_div_mul_left _ _ (mul_ne_zero hc₀ hh₀) (ENNReal.mul_ne_top hc (measure_ne_top _ _))]

variable [IsMarkovKernel κ] [IsProbabilityMeasure μ]

-- p. 5243: at `r = 1` the learner samples from the posterior, whose stationary distribution is
-- the prior [griffiths-kalish-2007].
theorem invariant_exponentiatedPosterior_one : (exponentiatedPosterior κ μ 1 ∘ₖ κ).Invariant μ :=
  invariant_comp_of_ae_eq_posterior κ μ <| ae_iff_of_countable.2 fun d hd ↦
    Measure.ext_of_singleton fun h ↦ by
      simp only [exponentiatedPosterior, Kernel.ofWeights_apply_singleton, ENNReal.rpow_one,
        posterior_apply_singleton κ μ hd, Measure.comp_apply_singleton]

/-- Methods, eqs. (6)–(10): if every datum is either impossible or equally likely under each
language, iterated learning with the exponentiated posterior has the stationary distribution
proportional to `P(h)^r`. The learner is the posterior under that distribution, so the result is
[griffiths-kalish-2007]'s at a different prior. -/
theorem invariant_exponentiatedPosterior
    (hκ : ∀ d h h', κ h {d} ≠ 0 → κ h' {d} ≠ 0 → κ h {d} = κ h' {d}) {r : ℝ} (hr : 0 < r) :
    (exponentiatedPosterior κ μ r ∘ₖ κ).Invariant (exponentiatedPrior μ r) := by
  refine invariant_comp_of_ae_eq_posterior κ _ (ae_eq_posterior_of_weights κ hκ (μ {·} ^ r)
    (ENNReal.inv_ne_zero.2 (sum_rpow_ne_top μ hr.le)) (ENNReal.inv_ne_top.2 (sum_rpow_ne_zero μ r))
    (exponentiatedPrior_apply_singleton μ r) fun d hd h ↦ ?_)
  obtain ⟨h₀, -, hh₀⟩ := exists_of_comp_apply_ne_zero κ hd
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

omit [MeasurableSingletonClass H] [Countable D] [MeasurableSingletonClass D]
  [StandardBorelSpace H] [Nonempty H] in
-- Under the condition, at a datum some mode of the prior can produce, the MAP choices are the
-- modes that can produce it.
private theorem argmax_eq_filter
    (hκ : ∀ d h h', κ h {d} ≠ 0 → κ h' {d} ≠ 0 → κ h {d} = κ h' {d}) {d : D} {h₀ : H}
    (h₀M : h₀ ∈ univ.argmax fun h ↦ μ {h}) (hh₀ : κ h₀ {d} ≠ 0) :
    univ.argmax (fun h ↦ μ {h} * κ h {d}) =
      (univ.argmax fun h ↦ μ {h}).filter (κ · {d} ≠ 0) := by
  have hμ₀ : μ {h₀} ≠ 0 := by
    obtain ⟨h', hh'⟩ := exists_apply_ne_zero μ
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

/-- The `r = ∞` endpoint: if every datum is either impossible or equally likely under each
language, iterated learning by MAP estimation has the uniform distribution on the modes of the
prior as a stationary distribution. Two priors with the same modes, one weak and one strong, give
the same one. -/
theorem invariant_mapLearner (hκ : ∀ d h h', κ h {d} ≠ 0 → κ h' {d} ≠ 0 → κ h {d} = κ h' {d}) :
    (mapLearner κ μ ∘ₖ κ).Invariant (uniformOn ↑(univ.argmax fun h ↦ μ {h})) := by
  classical
  set M := univ.argmax fun h ↦ μ {h}
  have hM₀ : (#M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 (argmax_nonempty univ_nonempty)).ne'
  refine invariant_comp_of_ae_eq_posterior κ _ (ae_eq_posterior_of_weights κ hκ
    (fun h ↦ if h ∈ M then 1 else 0) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    (ENNReal.inv_ne_top.2 hM₀) (fun h ↦ ?_) fun d hd h ↦ ?_)
  · rw [uniformOn_finset_apply_singleton]
    split_ifs <;> simp
  obtain ⟨h₀, hν₀, hh₀⟩ := exists_of_comp_apply_ne_zero κ hd
  have h₀M : h₀ ∈ M := by
    by_contra h₀M
    exact hν₀ (by simp [uniformOn_finset_apply_singleton, h₀M])
  have hite (h : H) : (if κ h {d} = 0 then 0 else if h ∈ M then 1 else 0 : ℝ≥0∞) =
      if h ∈ M.filter (κ · {d} ≠ 0) then 1 else 0 := by
    by_cases h₁ : κ h {d} = 0 <;> by_cases hm : h ∈ M <;> simp [h₁, hm]
  rw [mapLearner_apply, argmax_eq_filter κ μ hκ h₀M hh₀, uniformOn_finset_apply_singleton, hite]
  simp_rw [hite]
  rw [sum_boole, filter_mem_eq_inter, univ_inter]
  split_ifs <;> simp [M]

omit [StandardBorelSpace H] [Nonempty H] [IsMarkovKernel κ] in
/-- p. 5244, "systematically overrepresented": the stationary distribution proportional to
`P(h)^r` raises the prior odds between any two languages to the power `r`. -/
theorem exponentiatedPrior_real_div {r : ℝ} (hr : 0 < r) (h h' : H) :
    (exponentiatedPrior μ r).real {h'} / (exponentiatedPrior μ r).real {h} =
      (μ.real {h'} / μ.real {h}) ^ r := by
  have hZ : ((∑ h, μ {h} ^ r)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (sum_rpow_ne_top μ hr.le),
      ENNReal.inv_ne_top.2 (sum_rpow_ne_zero μ r)⟩
  simp only [measureReal_def, exponentiatedPrior_apply_singleton, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow]
  rw [mul_div_mul_left _ _ hZ, Real.div_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

omit [StandardBorelSpace H] [Nonempty H] [IsMarkovKernel κ] in
-- p. 5244: for `r > 1` the less probable of two languages loses ground.
theorem exponentiatedPrior_real_div_lt {r : ℝ} (hr : 1 < r) {h h' : H} (h₀ : 0 < μ.real {h'})
    (hlt : μ.real {h'} < μ.real {h}) :
    (exponentiatedPrior μ r).real {h'} / (exponentiatedPrior μ r).real {h} <
      μ.real {h'} / μ.real {h} := by
  rw [exponentiatedPrior_real_div μ (by linarith) h h']
  exact Real.rpow_lt_self_of_lt_one (div_pos h₀ (h₀.trans hlt)) ((div_lt_one (h₀.trans hlt)).2 hlt)
    hr

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

private theorem sum_ite_class {ε : ℝ} (hk : 2 ≤ k) (a : Fin k) :
    ∑ y : Fin k, (if y = a then 1 - ε else ε / (k - 1)) = 1 := by
  have hk' : (k : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
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
  have hk' : (0 : ℝ) < k - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨fun h ↦ ?_⟩
  have : ∀ i : Fin m, IsProbabilityMeasure (Measure.ofRealWeights fun d : Fin n × Fin k ↦
      P.real {d.1} * if d.2 = h d.1 then 1 - ε else ε / (k - 1)) := fun _ ↦ by
    refine Measure.isProbabilityMeasure_ofRealWeights
      (fun d ↦ mul_nonneg measureReal_nonneg (by split_ifs <;> first | linarith | positivity)) ?_
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, sum_ite_class hk, mul_one]
    rw [sum_measureReal_singleton, coe_univ, probReal_univ]
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

private theorem ascPochhammer_eval_eq_gamma {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (ascPochhammer ℝ j).eval x = Real.Gamma (j + x) / Real.Gamma x := by
  induction j with
  | zero => simp [(Real.Gamma_pos_of_pos hx).ne']
  | succ j ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.cast_succ, add_right_comm,
      Real.Gamma_add_one (by positivity : (j : ℝ) + x ≠ 0)]
    ring

-- Eq. (5), with `#{i | h i = j}` the number of meanings expressed by class `j`.
theorem prior_real_singleton [NeZero k] {α : ℝ} (hα : 0 < α) (h : Fin n → Fin k) :
    (prior α).real {h} = Real.Gamma (k * α) / (Real.Gamma α ^ k * Real.Gamma (n + k * α)) *
      ∏ j, Real.Gamma (#{i | h i = j} + α) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hΓ := (Real.Gamma_pos_of_pos hα).ne'
  have hΓk := (Real.Gamma_pos_of_pos (mul_pos hk hα)).ne'
  rw [prior, polyaUrn_real_singleton (fun _ ↦ hα), polyaUrnProb, sum_countVec, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, ascPochhammer_eval_eq_gamma (mul_pos hk hα)]
  simp_rw [ascPochhammer_eval_eq_gamma hα, countVec]
  rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
  field_simp

-- At no noise, at the noise `(k - 1) / k` and at noise one, every datum has the same
-- probability under each language that can produce it.
private theorem produce_eq_of_ne_zero (P : Measure (Fin n)) {ε : ℝ} (hk : 2 ≤ k)
    (hε : ε = 0 ∨ ε = (k - 1) / k ∨ ε = 1) {d : Fin m → Fin n × Fin k} {h : Fin n → Fin k}
    (hh : produce P ε h {d} ≠ 0) :
    produce P ε h {d} = ∏ i, ENNReal.ofReal
      (P.real {(d i).1} * if ε = 1 then 1 / ((k : ℝ) - 1) else 1 - ε) := by
  have hk' : (k : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
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

/-- Methods: the noisy meaning-class model meets the condition of `invariant_exponentiatedPosterior`
exactly when there is no noise, when every class is produced with probability `1/k`, or when the
language's own class is never produced. -/
theorem constant_or_zero_iff (P : Measure (Fin n)) [IsProbabilityMeasure P] {ε : ℝ} (hk : 2 ≤ k)
    (hm : m ≠ 0) (h₀ : 0 ≤ ε) (h₁ : ε ≤ 1) :
    (∀ (d : Fin m → Fin n × Fin k) (h h' : Fin n → Fin k), produce P ε h {d} ≠ 0 →
      produce P ε h' {d} ≠ 0 → produce P ε h {d} = produce P ε h' {d}) ↔
      ε = 0 ∨ ε = (k - 1) / k ∨ ε = 1 := by
  refine ⟨fun hc ↦ ?_, fun hε d h h' hh hh' ↦ by
    rw [produce_eq_of_ne_zero P hk hε hh, produce_eq_of_ne_zero P hk hε hh']⟩
  by_contra hε
  simp only [not_or] at hε
  obtain ⟨hε₀, hεk, hε₁⟩ := hε
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨x, hx⟩ : ∃ x, P {x} ≠ 0 := by
    by_contra! h₀
    exact NeZero.ne P (Measure.ext_of_singleton fun x ↦ by simp [h₀ x])
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

-- The rising factorial `(x)_b` increases with `x`, strictly once `b ≠ 0`.
private theorem ascPochhammer_eval_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (b : ℕ) :
    (ascPochhammer ℝ b).eval x ≤ (ascPochhammer ℝ b).eval y := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (by linarith) (by positivity) (ascPochhammer_pos _ _ (hx.trans_le hxy)).le

private theorem ascPochhammer_eval_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) {b : ℕ} (hb : b ≠ 0) :
    (ascPochhammer ℝ b).eval x < (ascPochhammer ℝ b).eval y := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  exact mul_lt_mul' (ascPochhammer_eval_le hx hxy.le b) (by linarith) (by positivity)
    (ascPochhammer_pos _ _ (hx.trans hxy))

-- `(x)_a (x)_b ≤ (x)_(a + b)`, strictly when neither count is zero.
private theorem ascPochhammer_eval_mul_le {x : ℝ} (hx : 0 < x) (a b : ℕ) :
    (ascPochhammer ℝ a).eval x * (ascPochhammer ℝ b).eval x ≤
      (ascPochhammer ℝ (a + b)).eval x := by
  rw [← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
  exact mul_le_mul_of_nonneg_left (ascPochhammer_eval_le hx (by simp) b)
    (ascPochhammer_pos _ _ hx).le

private theorem ascPochhammer_eval_mul_lt {x : ℝ} (hx : 0 < x) {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (ascPochhammer ℝ a).eval x * (ascPochhammer ℝ b).eval x <
      (ascPochhammer ℝ (a + b)).eval x := by
  rw [← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
  exact mul_lt_mul_of_pos_left (ascPochhammer_eval_lt hx (by simp [Nat.pos_of_ne_zero ha]) hb)
    (ascPochhammer_pos _ _ hx)

private theorem prod_ascPochhammer_eval_le {x : ℝ} (hx : 0 < x) (c : Fin k → ℕ)
    (s : Finset (Fin k)) :
    ∏ j ∈ s, (ascPochhammer ℝ (c j)).eval x ≤ (ascPochhammer ℝ (∑ j ∈ s, c j)).eval x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    exact (mul_le_mul_of_nonneg_left ih (ascPochhammer_pos _ _ hx).le).trans
      (ascPochhammer_eval_mul_le hx _ _)

-- The modes of the prior (5) are the fully regular languages, which express every meaning by the
-- same class, whatever the bias strength `α`.
theorem argmax_prior [NeZero k] {α : ℝ} (hα : 0 < α) :
    univ.argmax (fun h : Fin n → Fin k ↦ prior α {h}) = univ.image fun j _ ↦ j := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hD : 0 < (ascPochhammer ℝ n).eval (k * α) := ascPochhammer_pos _ _ (mul_pos hk hα)
  have hF (h : Fin n → Fin k) : 0 < ∏ j, (ascPochhammer ℝ (countVec h j)).eval α :=
    prod_pos fun _ _ ↦ ascPochhammer_pos _ _ hα
  have hmass (h : Fin n → Fin k) : prior α {h} = ENNReal.ofReal
      ((∏ j, (ascPochhammer ℝ (countVec h j)).eval α) / (ascPochhammer ℝ n).eval (k * α)) := by
    rw [prior, polyaUrn_singleton (fun _ ↦ hα), polyaUrnProb, sum_countVec, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hconst (j : Fin k) :
      ∏ c, (ascPochhammer ℝ (countVec (fun _ : Fin n ↦ j) c)).eval α =
        (ascPochhammer ℝ n).eval α := by
    rw [prod_eq_single j (fun c _ hc ↦ by simp [countVec, Ne.symm hc]) (by simp)]
    simp [countVec]
  have hlt (h : Fin n → Fin k) {i₁ i₂ : Fin n} (hne : h i₁ ≠ h i₂) :
      ∏ j, (ascPochhammer ℝ (countVec h j)).eval α < (ascPochhammer ℝ n).eval α := by
    have hc₁ : countVec h (h i₁) ≠ 0 := card_ne_zero.2 ⟨i₁, by simp⟩
    have hS : ∑ j ∈ univ.erase (h i₁), countVec h j ≠ 0 :=
      (Nat.pos_of_ne_zero (card_ne_zero.2 ⟨i₂, by simp⟩ : countVec h (h i₂) ≠ 0)).trans_le
        (single_le_sum (f := fun j ↦ countVec h j) (fun _ _ ↦ Nat.zero_le _)
          (mem_erase.2 ⟨hne.symm, mem_univ _⟩)) |>.ne'
    calc ∏ j, (ascPochhammer ℝ (countVec h j)).eval α
        = (ascPochhammer ℝ (countVec h (h i₁))).eval α *
            ∏ j ∈ univ.erase (h i₁), (ascPochhammer ℝ (countVec h j)).eval α :=
          (mul_prod_erase univ _ (mem_univ _)).symm
      _ ≤ (ascPochhammer ℝ (countVec h (h i₁))).eval α *
            (ascPochhammer ℝ (∑ j ∈ univ.erase (h i₁), countVec h j)).eval α :=
          mul_le_mul_of_nonneg_left (prod_ascPochhammer_eval_le hα _ _)
            (ascPochhammer_pos _ _ hα).le
      _ < (ascPochhammer ℝ (countVec h (h i₁) + ∑ j ∈ univ.erase (h i₁), countVec h j)).eval α :=
          ascPochhammer_eval_mul_lt hα hc₁ hS
      _ = (ascPochhammer ℝ n).eval α := by rw [add_sum_erase _ _ (mem_univ _), sum_countVec]
  ext h
  simp only [mem_argmax, mem_univ, true_and, mem_image]
  refine ⟨fun hmax ↦ ?_, ?_⟩
  · by_contra hnc
    obtain ⟨i₁, i₂, hne⟩ : ∃ i₁ i₂, h i₁ ≠ h i₂ := by
      by_contra! hall
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
      · exact hnc ⟨0, funext fun i ↦ isEmptyElim i⟩
      · exact hnc ⟨h i₀, funext fun i ↦ hall i₀ i⟩
    have := hmax (fun _ ↦ h i₁) trivial
    rw [hmass, hmass, ENNReal.ofReal_le_ofReal_iff (div_pos (hF h) hD).le,
      div_le_div_iff_of_pos_right hD, hconst] at this
    exact (hlt h hne).not_ge this
  · rintro ⟨j, rfl⟩ h' _
    rw [hmass, hmass, hconst]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (by simpa [sum_countVec] using prod_ascPochhammer_eval_le hα (countVec h') univ) hD.le)

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
  have : IsProbabilityMeasure (prior (n := n) (k := k) α) :=
    isProbabilityMeasure_polyaUrn (fun _ ↦ hα) n
  have h := invariant_mapLearner (produce (m := m) P 0) (prior α) fun d h h' hh hh' ↦ by
    rw [produce_eq_of_ne_zero P hk (Or.inl rfl) hh, produce_eq_of_ne_zero P hk (Or.inl rfl) hh']
  rwa [argmax_prior hα, coe_image, coe_univ, Set.image_univ] at h

-- Errata: without noise each fully regular language is a sink of the MAP chain, so its
-- stationary distribution is not unique and the chain is not ergodic.
theorem invariant_mapLearner_dirac (P : Measure (Fin n)) [IsProbabilityMeasure P] (hk : 2 ≤ k)
    (hm : m ≠ 0) {α : ℝ} (hα : 0 < α) (j : Fin k) :
    (mapLearner (produce (m := m) P 0) (prior α) ∘ₖ produce P 0).Invariant
      (Measure.dirac fun _ : Fin n ↦ j) := by
  have : NeZero k := ⟨by omega⟩
  have := isMarkovKernel_produce (m := m) P hk le_rfl zero_le_one
  have : IsProbabilityMeasure (prior (n := n) (k := k) α) :=
    isProbabilityMeasure_polyaUrn (fun _ ↦ hα) n
  set a : Fin n → Fin k := fun _ ↦ j
  refine invariant_comp_of_ae_eq_posterior _ _ (ae_iff_of_countable.2 fun d hd ↦
    Measure.ext_of_singleton fun h ↦ ?_)
  obtain ⟨h₀, hδ, ha⟩ := exists_of_comp_apply_ne_zero _ hd
  obtain rfl : h₀ = a := by
    by_contra hne
    exact hδ (by simp [Measure.dirac_apply', hne])
  have haM : a ∈ univ.argmax fun h ↦ prior α {h} := by
    rw [argmax_prior hα]
    exact mem_image.2 ⟨j, mem_univ _, rfl⟩
  have hfilter : (univ.argmax fun h ↦ prior α {h}).filter (produce P 0 · {d} ≠ 0) = {a} := by
    ext h
    rw [argmax_prior hα, mem_filter, mem_image, mem_singleton]
    refine ⟨fun ⟨⟨j', _, hj'⟩, hh⟩ ↦ ?_, fun hh ↦ ⟨⟨j, mem_univ _, hh.symm⟩, hh ▸ ha⟩⟩
    subst hj'
    have i₀ : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    have h₁ := eq_of_produce_zero_apply_ne_zero P hh i₀
    have h₂ := eq_of_produce_zero_apply_ne_zero P ha i₀
    funext i
    exact h₁.symm.trans h₂
  have hcomp : (produce P 0 ∘ₘ Measure.dirac a) {d} = produce P 0 a {d} := by
    rw [Measure.comp_apply_singleton, sum_eq_single a (fun h _ hh ↦ by simp [hh])
      (by simp), Measure.dirac_apply_of_mem (Set.mem_singleton a), one_mul]
  rw [mapLearner_apply, argmax_eq_filter _ _ (fun d h h' hh hh' ↦ by
      rw [produce_eq_of_ne_zero P hk (Or.inl rfl) hh,
        produce_eq_of_ne_zero P hk (Or.inl rfl) hh']) haM ha, hfilter,
    posterior_apply_singleton _ _ hd, hcomp, uniformOn_finset_apply_singleton]
  by_cases hh : h = a
  · subst hh
    simp [ENNReal.div_self ha (measure_ne_top _ _)]
  · simp [hh, Measure.dirac_apply', Ne.symm hh]

/-- With two meanings and two classes, MAP learning gives each fully regular language
probability `1/2`. -/
example : uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j) {fun _ ↦ 0} = 2⁻¹ := by
  have hmem : (fun _ : Fin 2 ↦ (0 : Fin 2)) ∈ univ.image fun j (_ : Fin 2) ↦ j := by decide
  have hcard : #(univ.image fun j (_ : Fin 2) ↦ (j : Fin 2)) = 2 := by decide
  rw [← Set.image_univ, ← coe_univ, ← coe_image, uniformOn_finset_apply_singleton]
  simp [hmem, hcard]

/-- The irregular language that gives each meaning its own class has positive prior probability,
but probability zero in the MAP chain's stationary distribution, which is therefore not the
prior. -/
example {α : ℝ} (hα : 0 < α) :
    uniformOn (Set.range fun j : Fin 2 ↦ fun _ : Fin 2 ↦ j) {fun i ↦ i} = 0 ∧
      prior α {fun i : Fin 2 ↦ i} ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have hmem : (fun i : Fin 2 ↦ i) ∉ univ.image fun j (_ : Fin 2) ↦ j := by decide
    rw [← Set.image_univ, ← coe_univ, ← coe_image, uniformOn_finset_apply_singleton]
    simp [hmem]
  · rw [prior, polyaUrn_singleton (fun _ ↦ hα)]
    exact (ENNReal.ofReal_pos.2 (polyaUrnProb_pos (fun _ ↦ hα) _)).ne'

/-- The condition of `invariant_exponentiatedPosterior` is met without noise, so learners with
exponent `2` keep the squared prior stationary. -/
example (P : Measure (Fin 2)) [IsProbabilityMeasure P] {α : ℝ} (hα : 0 < α) :
    (exponentiatedPosterior (produce (k := 2) (m := 3) P 0) (prior α) 2 ∘ₖ produce P 0).Invariant
      (exponentiatedPrior (prior α) 2) := by
  have := isMarkovKernel_produce (k := 2) (m := 3) P le_rfl le_rfl zero_le_one
  have : IsProbabilityMeasure (prior (n := 2) (k := 2) α) :=
    isProbabilityMeasure_polyaUrn (fun _ ↦ hα) 2
  exact invariant_exponentiatedPosterior _ _ (fun d h h' hh hh' ↦ by
    rw [produce_eq_of_ne_zero P le_rfl (Or.inl rfl) hh,
      produce_eq_of_ne_zero P le_rfl (Or.inl rfl) hh']) two_pos

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
    ¬ (∀ (d : Fin 1 → Fin 2 × Fin 4) (h h' : Fin 2 → Fin 4), produce P (1 / 10) h {d} ≠ 0 →
        produce P (1 / 10) h' {d} ≠ 0 → produce P (1 / 10) h {d} = produce P (1 / 10) h' {d}) ∧
      ∀ (d : Fin 1 → Fin 2 × Fin 4) (h h' : Fin 2 → Fin 4), produce P (3 / 4) h {d} ≠ 0 →
        produce P (3 / 4) h' {d} ≠ 0 → produce P (3 / 4) h {d} = produce P (3 / 4) h' {d} := by
  refine ⟨fun h ↦ ?_, (constant_or_zero_iff P (k := 4) (m := 1) (ε := 3 / 4) (by norm_num)
    one_ne_zero (by norm_num) (by norm_num)).2 (Or.inr (Or.inl (by norm_num)))⟩
  rcases (constant_or_zero_iff P (k := 4) (m := 1) (ε := 1 / 10) (by norm_num) one_ne_zero
    (by norm_num) (by norm_num)).1 h with h | h | h <;> norm_num at h

/-- With two meanings, two classes and `α = 1`, the prior makes a fully regular language twice as
likely as the language giving each meaning its own class; squaring makes it four times as likely. -/
example : (exponentiatedPrior (prior (n := 2) (k := 2) 1) 2).real {fun i ↦ i} /
    (exponentiatedPrior (prior (n := 2) (k := 2) 1) 2).real {fun _ ↦ 0} = (1 / 2) ^ (2 : ℝ) := by
  have : IsProbabilityMeasure (prior (n := 2) (k := 2) (1 : ℝ)) :=
    isProbabilityMeasure_polyaUrn (fun _ ↦ one_pos) 2
  have h₁ : countVec (fun i : Fin 2 ↦ i) = fun _ ↦ 1 := by decide
  have h₂ : countVec (fun _ : Fin 2 ↦ (0 : Fin 2)) = fun j ↦ if j = 0 then 2 else 0 := by decide
  rw [exponentiatedPrior_real_div _ two_pos, prior, polyaUrn_real_singleton (fun _ ↦ one_pos),
    polyaUrn_real_singleton (fun _ ↦ one_pos), h₁, h₂]
  simp [polyaUrnProb, Fin.prod_univ_two, ascPochhammer_succ_eval]
  norm_num

end MeaningClass

end KirbyDowmanGriffiths2007
