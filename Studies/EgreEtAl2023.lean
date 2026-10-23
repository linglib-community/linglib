module

public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.Probability.Kernel.Module
public import Linglib.Pragmatics.RSA.Belief
public import Mathlib.Data.Nat.Dist
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Égré, Spector, Mortier and Verheyen (2023): On the Optimality of Vagueness: "Around", "Between" and the Gricean Maxims

Égré, Spector, Mortier and Verheyen give a Bayesian account of the approximator "around n" and of
why a partially informed speaker may prefer it to a precise "between a and b". "Around n" has an
open radius: "x is around n" at radius `y` means `|n − x| ≤ y`. The listener's information state
is a joint distribution over the value and the radius, and accepting the sentence conditions it
on that event and marginalizes the radius (`bir`). The speaker chooses the message whose literal
posterior is closest to her belief in Kullback–Leibler divergence, and the full model iterates
speakers and joint listeners from the literal listener (`listener`). Appendix A treats the
lexical uncertainty model of Bergen, Levy and Goodman (`luSpeaker`), and Appendix B a weighted
interpretation rule (`wir`).

## Main statements

* `bir_eq_ofDensity`, `bir_unif_apply_singleton`, `ratio_inequality`: the interpretation
  rule is the literal listener at the graded meaning "the prior mass of the radii reaching x",
  under uniform priors its posterior is the triangle `(n − |n − k| + 1) / (n + 1)²`, and whatever
  the priors it raises the odds of a closer value against a farther one, where "between" leaves
  them unchanged.
* `table1_prefers_around`: with a belief peaked at 4 with support `[1, 7]` the speaker prefers
  "around 4" to "between 1 and 7".
* `luSpeaker_eq_of_sameSupport`: in the lexical uncertainty model, beliefs with the same support
  yield the same speaker at every level.
* `bir_eq_bind_radiusPosterior`, `wir_ne_bir`: the Bayesian rule is the weighted rule with the
  posterior over radii in place of the prior, and the two rules differ.

## Implementation notes

* Values are a countable measurable type with a distance `d : X → ℕ` to the target, so one
  development serves the scale `ℕ` of §3–4, where the message "around n" is `Nat.dist n`, and
  the nine values of §5–7. Priors are finite measures rather than probability measures: every
  stage renormalizes, so the uniform priors of §3.2.2 are the counting measures `unif` and the
  uniform prior on the nine values is `Measure.count`.
* Speakers are `RSA.speaker` at a belief, which for probability beliefs is the softmax of
  `−λ · D(belief ‖ listener)` (`RSA.speaker_eq_softmax_klDiv`). A message that excludes
  a value the speaker deems possible has zero probability, footnote 17's Quality. In the full
  model the belief is the joint prior conditioned on the observation and marginalized to the
  value; in the lexical uncertainty model, whose speaker addresses the listener's joint state,
  it is that conditioned prior itself.
* Pragmatic listeners are `RSA.listener` at the joint prior of the speaker read at the
  observation. A message no observation produces gets the zero measure, the `0 / 0` convention
  of footnote 28, and on messages heard with positive probability the listener is the posterior
  kernel (`RSA.listener_apply_eq_posterior`).
* The lexical uncertainty model is stated over arbitrary finite types of worlds, observations,
  interpretations and messages. Appendix A's two steps are general:
  `RSA.speaker_cond_listener_truthful_apply_eq`, that against a literal listener the speaker
  depends on what she knows only through the messages it entails, and
  `RSA.speaker_cond_ofDensity_apply_eq`, that the prior cancels against a reweighted prior.

## TODO

* The amplification across recursion levels reported in Tables 7–10 (a level-5 speaker
  preferring "around 4" for the peaked belief on `[2, 6]`, which the level-1 speaker does not)
  is a numerical simulation at `λ = 10` and is not represented.

## References

* [egre-etal-2023]
* [bergen-levy-goodman-2016]
* [lassiter-goodman-2017]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

namespace EgreEtAl2023

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ### The semantics of "around" and the Bayesian interpretation rule (§3.2) -/

section Around

variable {X : Type*}

/-- "x is around n" at radius `y` is `|n − x| ≤ y` (5), as an event over the joint state of value
and radius; `d` is the distance to the target. -/
def AroundEvent (d : X → ℕ) : Set (X × ℕ) := {p | d p.1 ≤ p.2}

/-- The graded meaning of "around" is the prior mass of the radii reaching the value. -/
noncomputable def aroundWeight (ν : Measure ℕ) (d : X → ℕ) (x : X) : ℝ≥0∞ := ν (Set.Ici (d x))

/-- The closer a value is to the target, the likelier "around" is true of it (§3.2.1). -/
theorem aroundWeight_le_of_le (ν : Measure ℕ) (d : X → ℕ) {x x' : X} (h : d x ≤ d x') :
    aroundWeight ν d x' ≤ aroundWeight ν d x :=
  measure_mono (Set.Ici_subset_Ici.mpr h)

variable [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] (μ : Measure X)
  (ν : Measure ℕ) (d : X → ℕ)

/-- The Bayesian interpretation rule (§3.2.1) conditions the joint prior over value and radius on
the value being around the target and marginalizes to the value. -/
noncomputable def bir : Measure X := ((μ.prod ν)[|AroundEvent d]).map Prod.fst

variable [SFinite ν]

theorem measurableSet_aroundEvent : MeasurableSet (AroundEvent d) :=
  (Set.to_countable _).measurableSet

theorem prod_apply_aroundEvent : (μ.prod ν) (AroundEvent d) = ∫⁻ x, aroundWeight ν d x ∂μ := by
  rw [Measure.prod_apply (measurableSet_aroundEvent d)]
  rfl

theorem bir_apply_singleton (x : X) :
    bir μ ν d {x} = μ {x} * aroundWeight ν d x / ∫⁻ x', aroundWeight ν d x' ∂μ := by
  rw [bir, Measure.map_apply measurable_fst (.singleton x),
    cond_apply' (measurable_fst (.singleton x)), prod_apply_aroundEvent, ENNReal.div_eq_inv_mul,
    show AroundEvent d ∩ Prod.fst ⁻¹' {x} = {x} ×ˢ Set.Ici (d x) from ?_, Measure.prod_prod]
  · rfl
  · ext ⟨x', y⟩
    simp only [AroundEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_prod, Set.mem_Ici]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨h, rfl⟩

theorem bir_eq_ofDensity {U : Type*} [MeasurableSpace U] [Countable U]
    [MeasurableSingletonClass U] {m : U → X → ℝ≥0∞} {u : U} (hm : m u = aroundWeight ν d) :
    bir μ ν d = Kernel.ofDensity μ m u :=
  Measure.ext_of_singleton fun x ↦ by
    rw [bir_apply_singleton, Kernel.ofDensity_apply_singleton', hm, mul_comm]

end Around

/-! ### Uniform priors and the triangular posterior (§3.2.2) -/

/-- The counting measure on `{0, …, N}` is the uniform prior on the range up to the normalizing
constant, which conditioning absorbs. -/
noncomputable def unif (N : ℕ) : Measure ℕ := ∑ k ∈ Finset.range (N + 1), Measure.dirac k

theorem unif_apply_singleton (N k : ℕ) : unif N {k} = if k ≤ N then 1 else 0 := by
  simp only [unif, Measure.finsetSum_apply, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

theorem unif_apply_Ici (N d : ℕ) : unif N (Set.Ici d) = (N + 1 - d : ℕ) := by
  simp only [unif, Measure.finsetSum_apply, Measure.dirac_apply, Set.indicator_apply, Set.mem_Ici,
    Pi.one_apply, Finset.sum_boole]
  rw [show (Finset.range (N + 1)).filter (fun i ↦ d ≤ i) = Finset.Ico d (N + 1) from by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega, Nat.card_Ico]

theorem unif_apply_Icc {N a b : ℕ} (hb : b ≤ N) : unif N (Set.Icc a b) = (b + 1 - a : ℕ) := by
  simp only [unif, Measure.finsetSum_apply, Measure.dirac_apply, Set.indicator_apply, Set.mem_Icc,
    Pi.one_apply, Finset.sum_boole]
  rw [show (Finset.range (N + 1)).filter (fun i ↦ a ≤ i ∧ i ≤ b) = Finset.Icc a b from by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega, Nat.card_Icc]

theorem lintegral_unif (N : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k ∂unif N = ∑ k ∈ Finset.range (N + 1), f k := by
  simp only [unif, lintegral_finsetSum_measure, lintegral_dirac]

theorem aroundWeight_unif (n k : ℕ) :
    aroundWeight (unif n) (Nat.dist n) k = (n + 1 - Nat.dist n k : ℕ) :=
  unif_apply_Ici n _

theorem sum_range_sub_dist (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), (n + 1 - Nat.dist n k) = (n + 1) ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsum : ∑ k ∈ Finset.range (2 * n + 1), (n + 1 + 1 - Nat.dist (n + 1) (k + 1)) =
        ∑ k ∈ Finset.range (2 * n + 1), (n + 1 - Nat.dist n k) + (2 * n + 1) := by
      rw [Finset.sum_congr rfl (g := fun k ↦ (n + 1 - Nat.dist n k) + 1) fun k hk ↦ ?_,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      rw [Nat.dist_add_add_right]
      have := Finset.mem_range.mp hk
      unfold Nat.dist
      omega
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ',
      Finset.sum_range_succ, hsum, ih, Nat.dist_zero_right,
      show Nat.dist (n + 1) (2 * n + 1 + 1) = n + 1 by unfold Nat.dist; omega,
      Nat.add_sub_cancel_left]
    ring

/-- Under uniform priors on the values `[0, 2n]` and on the radii `[0, n]` the posterior is
triangular (§3.2.2), `P(x = k | around n) = (n − |n − k| + 1) / (n + 1)²`. -/
theorem bir_unif_apply_singleton (n k : ℕ) :
    bir (unif (2 * n)) (unif n) (Nat.dist n) {k} =
      (n + 1 - Nat.dist n k : ℕ) / ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 := by
  rw [bir_apply_singleton, unif_apply_singleton, aroundWeight_unif, lintegral_unif]
  simp only [aroundWeight_unif]
  rw [← Nat.cast_sum, sum_range_sub_dist, Nat.cast_pow]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, ENNReal.zero_div, Nat.sub_eq_zero_of_le (by unfold Nat.dist; omega),
      Nat.cast_zero, ENNReal.zero_div]

/-- The posterior is symmetric about the target (§3.2.2 (i)). -/
theorem bir_unif_symm {n j : ℕ} (h : j ≤ n) :
    bir (unif (2 * n)) (unif n) (Nat.dist n) {n + j} =
      bir (unif (2 * n)) (unif n) (Nat.dist n) {n - j} := by
  rw [bir_unif_apply_singleton, bir_unif_apply_singleton,
    show Nat.dist n (n + j) = Nat.dist n (n - j) by unfold Nat.dist; omega]

/-- The farther a value from the target, the less probable it has become (§3.2.2 (i)). -/
theorem bir_unif_antitone {n k k' : ℕ} (h : Nat.dist n k ≤ Nat.dist n k') :
    bir (unif (2 * n)) (unif n) (Nat.dist n) {k'} ≤
      bir (unif (2 * n)) (unif n) (Nat.dist n) {k} := by
  rw [bir_unif_apply_singleton, bir_unif_apply_singleton]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.sub_le_sub_left h _)) _

/-- "Between a and b", the crisp interval meaning (§3.1), as a message indexed by its endpoints. -/
noncomputable def betweenMeaning (p : ℕ × ℕ) : ℕ → ℝ≥0∞ := (Set.Icc p.1 p.2).indicator 1

theorem ofDensity_betweenMeaning (μ : Measure ℕ) :
    Kernel.ofDensity μ betweenMeaning =
      RSA.listener μ (RSA.truthful (fun p : ℕ × ℕ ↦ Set.Icc p.1 p.2)) :=
  (RSA.listener_truthful_eq_ofDensity μ _).symm

/-- Under a uniform prior "between" gives the step function uniform on its interval and zero
outside it (§3.2.2 (ii)). -/
theorem listener_truthful_unif_betweenMeaning {N a b : ℕ} (hb : b ≤ N) (k : ℕ) :
    Kernel.ofDensity (unif N) betweenMeaning (a, b) {k} =
      if k ∈ Set.Icc a b then ((b + 1 - a : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  rw [ofDensity_betweenMeaning]
  split_ifs with h
  · refine (RSA.listener_truthful_apply_singleton (unif N)
      (fun p : ℕ × ℕ ↦ Set.Icc p.1 p.2) h).trans ?_
    rw [unif_apply_Icc hb, unif_apply_singleton, ite_eq_left (h.2.trans hb), mul_one]
  · exact RSA.listener_truthful_apply_singleton_of_notMem _
      (fun p : ℕ × ℕ ↦ Set.Icc p.1 p.2) h

/-! ### The ratio inequality (§4) -/

section Ratio

variable {μ : Measure ℕ} [IsFiniteMeasure μ] {ν : Measure ℕ} [IsFiniteMeasure ν] {n : ℕ}

theorem lintegral_aroundWeight_ne_top : ∫⁻ x, aroundWeight ν (Nat.dist n) x ∂μ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top μ _))
    ((lintegral_mono fun _ ↦ measure_mono (Set.subset_univ _)).trans (lintegral_const _).le)

theorem ratio_inequality {k₁ k₂ : ℕ} (h : k₁ < k₂) (hk : k₂ ≤ n) (hμ₁ : μ {n - k₁} ≠ 0)
    (hμ₂ : μ {n - k₂} ≠ 0) (hν : ν (Set.Ico k₁ k₂) ≠ 0) (hν₂ : ν (Set.Ici k₂) ≠ 0) :
    μ.real {n - k₁} / μ.real {n - k₂} <
      (bir μ ν (Nat.dist n)).real {n - k₁} / (bir μ ν (Nat.dist n)).real {n - k₂} := by
  have hw₁ : aroundWeight ν (Nat.dist n) (n - k₁) = ν (Set.Ici k₁) := by
    rw [aroundWeight, show Nat.dist n (n - k₁) = k₁ by unfold Nat.dist; omega]
  have hw₂ : aroundWeight ν (Nat.dist n) (n - k₂) = ν (Set.Ici k₂) := by
    rw [aroundWeight, show Nat.dist n (n - k₂) = k₂ by unfold Nat.dist; omega]
  have hZ : (∫⁻ x, aroundWeight ν (Nat.dist n) x ∂μ).toReal ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ lintegral_aroundWeight_ne_top).ne'
    refine ne_of_gt (lt_of_lt_of_le ?_ (setLIntegral_le_lintegral {n - k₂} _))
    rw [lintegral_singleton, hw₂]
    exact ENNReal.mul_pos hν₂ hμ₂
  have hw : (ν (Set.Ici k₂)).toReal < (ν (Set.Ici k₁)).toReal := by
    rw [← Set.Ico_union_Ici_eq_Ici h.le, measure_union (s₁ := Set.Ico k₁ k₂) (s₂ := Set.Ici k₂)
      (Set.disjoint_left.mpr fun x hx hx' ↦ (Set.mem_Ico.mp hx).2.not_ge (Set.mem_Ici.mp hx'))
      .of_discrete, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact lt_add_of_pos_left _ (ENNReal.toReal_pos hν (measure_ne_top _ _))
  have h₁ := ENNReal.toReal_pos hμ₁ (measure_ne_top μ _)
  have h₂ := ENNReal.toReal_pos hμ₂ (measure_ne_top μ _)
  have h₃ := ENNReal.toReal_pos hν₂ (measure_ne_top ν _)
  simp only [measureReal_def, bir_apply_singleton, hw₁, hw₂, ENNReal.toReal_div,
    ENNReal.toReal_mul, div_div_div_cancel_right₀ hZ]
  rw [div_lt_div_iff₀ h₂ (mul_pos h₂ h₃)]
  nlinarith [mul_pos h₁ h₂]

/-- "Between" leaves the odds unchanged, since for two values in its interval the ratio of
posteriors is the ratio of priors (§4). -/
theorem between_ratio {a b k₁ k₂ : ℕ} (hk₁ : k₁ ∈ Set.Icc a b) (hk₂ : k₂ ∈ Set.Icc a b)
    (hab : μ (Set.Icc a b) ≠ 0) :
    (Kernel.ofDensity μ betweenMeaning (a, b)).real {k₁} /
        (Kernel.ofDensity μ betweenMeaning (a, b)).real {k₂} =
      μ.real {k₁} / μ.real {k₂} := by
  have h₁ := RSA.listener_truthful_apply_singleton μ (fun p : ℕ × ℕ ↦ Set.Icc p.1 p.2)
    (u := (a, b)) hk₁
  have h₂ := RSA.listener_truthful_apply_singleton μ (fun p : ℕ × ℕ ↦ Set.Icc p.1 p.2)
    (u := (a, b)) hk₂
  rw [ofDensity_betweenMeaning, measureReal_def, measureReal_def, h₁, h₂, ENNReal.toReal_mul,
    ENNReal.toReal_mul, mul_div_mul_left _ _ (ENNReal.toReal_ne_zero.mpr
      ⟨ENNReal.inv_ne_zero.mpr (measure_ne_top _ _), ENNReal.inv_ne_top.mpr hab⟩)]
  rfl

end Ratio

/-! ### A case where the speaker prefers "around" (§5.2) -/

/-- The six messages of §6.1, all centred on 4; "exactly 4" is "between 4 and 4". -/
inductive Msg
  | between0_8 | between1_7 | between2_6 | between3_5 | exactly4 | around4
  deriving DecidableEq, Fintype

instance : MeasurableSpace Msg := ⊤
instance : DiscreteMeasurableSpace Msg := ⟨fun _ ↦ trivial⟩

/-- The graded meaning (12) gives crisp intervals for "between" and "exactly", and the
radius-marginal weight of "around 4" at the radius prior `ν`. -/
noncomputable def Msg.meaning (ν : Measure ℕ) : Msg → Fin 9 → ℝ≥0∞
  | .between0_8 => (Set.Icc 0 8).indicator 1
  | .between1_7 => (Set.Icc 1 7).indicator 1
  | .between2_6 => (Set.Icc 2 6).indicator 1
  | .between3_5 => (Set.Icc 3 5).indicator 1
  | .exactly4 => ({4} : Set (Fin 9)).indicator 1
  | .around4 => aroundWeight ν fun x ↦ Nat.dist 4 x

/-- The radius prior of §7.2 is uniform on `[0, 4]`. -/
noncomputable def radiusPrior : Measure ℕ := unif 4

/-- The literal listener of §5.2 has a uniform prior on the nine values. -/
noncomputable def L0 : Kernel Msg (Fin 9) :=
  Kernel.ofDensity Measure.count (Msg.meaning radiusPrior)

instance (m : Msg) : IsZeroOrProbabilityMeasure (L0 m) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.ofDensity _ _ m))

theorem L0_around4 : L0 .around4 = bir Measure.count radiusPrior (fun x : Fin 9 ↦ Nat.dist 4 x) :=
  (bir_eq_ofDensity _ _ _ rfl).symm

theorem meaning_around4 (y : Fin 9) :
    Msg.meaning radiusPrior .around4 y = ((5 - Nat.dist 4 y : ℕ) : ℝ≥0∞) :=
  unif_apply_Ici 4 _

theorem L0_around4_apply_singleton (x : Fin 9) :
    L0 .around4 {x} = (5 - Nat.dist 4 x : ℕ) / 25 := by
  have hsum : ∑ y : Fin 9, ((5 - Nat.dist 4 y : ℕ) : ℝ≥0∞) = 25 := by
    rw [← Nat.cast_sum, show ∑ y : Fin 9, (5 - Nat.dist 4 y) = 25 by decide]
    rfl
  rw [L0, Kernel.ofDensity_apply_singleton]
  simp only [meaning_around4, Measure.count_singleton, mul_one, hsum]

theorem L0_between1_7_apply_singleton (x : Fin 9) :
    L0 .between1_7 {x} = if x ∈ Set.Icc 1 7 then 7⁻¹ else 0 := by
  have h : L0 .between1_7 = RSA.listener Measure.count
      (RSA.truthful (fun _ : Msg ↦ Set.Icc (1 : Fin 9) 7)) .between1_7 := by
    rw [RSA.listener_truthful_eq_ofDensity]; rfl
  rw [h]
  split_ifs with hx
  · rw [RSA.listener_truthful_apply_singleton Measure.count
      (fun _ : Msg ↦ Set.Icc (1 : Fin 9) 7) hx, Measure.count_singleton, mul_one, ← Finset.coe_Icc,
      Measure.count_apply_finset, show (Finset.Icc (1 : Fin 9) 7).card = 7 by decide]
    rfl
  · exact RSA.listener_truthful_apply_singleton_of_notMem Measure.count
      (fun _ : Msg ↦ Set.Icc (1 : Fin 9) 7) hx

theorem L0_exactly4_apply_singleton (x : Fin 9) : L0 .exactly4 {x} = if x = 4 then 1 else 0 := by
  have h : L0 .exactly4 =
      RSA.listener Measure.count (RSA.truthful (fun _ : Msg ↦ ({4} : Set (Fin 9)))) .exactly4 := by
    rw [RSA.listener_truthful_eq_ofDensity]; rfl
  rw [h]
  split_ifs with hx
  · rw [RSA.listener_truthful_apply_singleton Measure.count
      (fun _ : Msg ↦ ({4} : Set (Fin 9))) (Set.mem_singleton_iff.mpr hx), Measure.count_singleton,
      Measure.count_singleton, inv_one, mul_one]
  · exact RSA.listener_truthful_apply_singleton_of_notMem Measure.count
      (fun _ : Msg ↦ ({4} : Set (Fin 9))) (fun h ↦ hx (Set.mem_singleton_iff.mp h))

/-- The speaker's belief of Table 1 has these weights, peaked at 4 with support `[1, 7]`. -/
def table1Weight : Fin 9 → ℕ := ![0, 1, 1, 16, 64, 16, 1, 1, 0]

/-- The speaker's belief of Table 1. -/
noncomputable def table1 : Measure (Fin 9) :=
  (100 : ℝ≥0∞)⁻¹ • ∑ x, (table1Weight x : ℝ≥0∞) • Measure.dirac x

theorem table1_apply_singleton (x : Fin 9) : table1 {x} = (100 : ℝ≥0∞)⁻¹ * table1Weight x := by
  rw [table1, Measure.smul_apply, smul_eq_mul, Measure.sum_smul_dirac_apply_singleton]

theorem table1_real_singleton (x : Fin 9) : table1.real {x} = table1Weight x / 100 := by
  rw [measureReal_def, table1_apply_singleton, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, inv_mul_eq_div]

instance : IsProbabilityMeasure table1 := by
  constructor
  rw [table1, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← Nat.cast_sum, show ∑ x : Fin 9, table1Weight x = 100 by decide]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem lintegral_count_meaning_around4 :
    ∫⁻ x, Msg.meaning radiusPrior .around4 x ∂Measure.count = 25 := by
  rw [lintegral_fintype]
  simp only [meaning_around4, Measure.count_singleton, mul_one]
  rw [← Nat.cast_sum, show ∑ y : Fin 9, (5 - Nat.dist 4 y) = 25 by decide]
  rfl

theorem lintegral_count_meaning_between1_7 :
    ∫⁻ x, Msg.meaning radiusPrior .between1_7 x ∂Measure.count = 7 := by
  rw [show Msg.meaning radiusPrior .between1_7 = (Set.Icc (1 : Fin 9) 7).indicator 1 from rfl,
    lintegral_indicator_one .of_discrete, ← Finset.coe_Icc, Measure.count_apply_finset,
    show (Finset.Icc (1 : Fin 9) 7).card = 7 by decide]
  rfl

instance : IsProbabilityMeasure (L0 .around4) :=
  Kernel.isProbabilityMeasure_ofDensity _ _ _
    (by rw [lintegral_count_meaning_around4]; norm_num)
    (by rw [lintegral_count_meaning_around4]; norm_num)

instance : IsProbabilityMeasure (L0 .between1_7) :=
  Kernel.isProbabilityMeasure_ofDensity _ _ _
    (by rw [lintegral_count_meaning_between1_7]; norm_num)
    (by rw [lintegral_count_meaning_between1_7]; norm_num)

theorem L0_around4_real_singleton (x : Fin 9) :
    (L0 .around4).real {x} = (5 - Nat.dist 4 x : ℕ) / 25 := by
  rw [measureReal_def, L0_around4_apply_singleton, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]

theorem L0_between1_7_real_singleton (x : Fin 9) :
    (L0 .between1_7).real {x} = if x ∈ Set.Icc 1 7 then 1 / 7 else 0 := by
  rw [measureReal_def, L0_between1_7_apply_singleton]
  split_ifs <;> simp

theorem table1_ac_around4 : table1 ≪ L0 .around4 :=
  Measure.absolutelyContinuous_of_forall_singleton fun x hx ↦ by
    rw [L0_around4_apply_singleton] at hx
    rcases ENNReal.div_eq_zero_iff.mp hx with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) (by have := x.isLt; unfold Nat.dist; omega)
    · exact absurd h (by norm_num)

/-- "Between 1 and 7" excludes only values the belief of Table 1 excludes. -/
theorem table1_ac_between1_7 : table1 ≪ L0 .between1_7 :=
  Measure.absolutelyContinuous_of_forall_singleton fun x hx ↦ by
    rw [L0_between1_7_apply_singleton] at hx
    rw [table1_apply_singleton]
    fin_cases x <;> simp_all +decide [table1Weight]

/-- "Exactly 4" excludes values the belief of Table 1 leaves possible, so the speaker never uses
it (footnote 17). -/
theorem table1_speaker_exactly4 {lam : ℝ} (hlam : 0 < lam) :
    RSA.speaker lam 0 L0 (fun _ : Unit ↦ table1) () {.exactly4} = 0 :=
  (RSA.speaker_apply_singleton_eq_zero_iff_not_ac hlam).2 fun h ↦ by
    have h3 := h (show L0 .exactly4 {3} = 0 by
      rw [L0_exactly4_apply_singleton, ite_eq_right (by decide)])
    rw [table1_apply_singleton] at h3
    simp [table1Weight] at h3

/-- With the belief of Table 1 the speaker prefers "around 4" to the best "between" (§5.2). At
every rationality she uses it more than "between 1 and 7", the triangular posterior being closer
to her belief than the flat one. -/
theorem table1_prefers_around {lam : ℝ} (hlam : 0 < lam) :
    (RSA.speaker lam 0 L0 (fun _ : Unit ↦ table1) ()).real {.between1_7} <
      (RSA.speaker lam 0 L0 (fun _ : Unit ↦ table1) ()).real {.around4} := by
  rw [RSA.speaker_zero_real_singleton_lt_iff_klDiv hlam
      ⟨.around4, klDiv_ne_top table1_ac_around4 .of_finite⟩,
    ← ENNReal.toReal_lt_toReal (klDiv_ne_top table1_ac_around4 .of_finite)
      (klDiv_ne_top table1_ac_between1_7 .of_finite),
    toReal_klDiv_eq_sum_log_div table1_ac_around4, toReal_klDiv_eq_sum_log_div table1_ac_between1_7]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, table1_real_singleton, L0_around4_real_singleton,
    L0_between1_7_real_singleton, table1Weight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Set.mem_Icc, Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_zero]
  norm_num [Nat.dist]
  have key : Real.log ((1 / 8 : ℝ) ^ 2 * (1 / 12) ^ 2 * (16 / 5) ^ 64) <
      Real.log ((7 / 100 : ℝ) ^ 4 * (28 / 25) ^ 32 * (112 / 25) ^ 64) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at key
  push_cast at key
  linarith

/-! ### The full model (§6): joint listeners and score speakers -/

section Recursion

variable {X O M : Type*} [MeasurableSpace X] [MeasurableSpace O] [MeasurableSpace M]
  (P : Measure (X × O))

/-- The speaker's belief after observation `o` (§6.1) conditions the joint prior on `o` and
marginalizes to the value, `P(x = k | o)`. -/
noncomputable def belief (o : O) : Measure X := (P[|Prod.snd ⁻¹' {o}]).map Prod.fst

theorem belief_apply_singleton [MeasurableSingletonClass X] (o : O) (x : X) :
    belief P o {x} = P {(x, o)} / P (Prod.snd ⁻¹' {o}) := by
  rw [belief, Measure.map_apply measurable_fst (.singleton x),
    cond_apply' (measurable_fst (.singleton x)), ENNReal.div_eq_inv_mul,
    show Prod.snd ⁻¹' {o} ∩ Prod.fst ⁻¹' {x} = {(x, o)} from ?_]
  ext ⟨x', o'⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, and_comm]

theorem isProbabilityMeasure_belief [IsFiniteMeasure P] {o : O} (ho : P (Prod.snd ⁻¹' {o}) ≠ 0) :
    IsProbabilityMeasure (belief P o) := by
  have := cond_isProbabilityMeasure (μ := P) ho
  unfold belief; infer_instance

variable [Fintype X] [MeasurableSingletonClass X] [Fintype M] [MeasurableSingletonClass M]
  (meaning : M → X → ℝ≥0∞)

/-- The literal listener over value and observation (12) reweights the joint prior by the
meaning, which constrains the value alone. -/
noncomputable def jointL0 : Kernel M (X × O) := Kernel.ofDensity P fun m p ↦ meaning m p.1

/-- The value-marginal of the joint literal listener is the literal listener on the
value-marginal prior, so eq. (BIR) is recovered inside the full model (footnote 23). -/
theorem jointL0_map_fst (m : M) :
    (jointL0 P meaning m).map Prod.fst = Kernel.ofDensity (P.map Prod.fst) meaning m :=
  Kernel.ofDensity_map P (measurable_of_countable _).aemeasurable measurable_fst.aemeasurable

variable [Fintype O] [MeasurableSingletonClass O] [IsFiniteMeasure P] (lam : ℝ)

/-- To the speaker answering a joint listener (13) only the listener's value-marginal
matters. -/
noncomputable def jointSpeaker (L : Kernel M (X × O)) : Kernel O M :=
  RSA.speaker lam 0 (L.map Prod.fst) (belief P)

/-- In the recursion (16)–(17), `listener n` is the paper's `Lⁿ`, and
`jointSpeaker P lam (listener n)` its `Sⁿ⁺¹`. The pragmatic listener answering a speaker, (15) and
(17), reweights the joint prior by the speaker's probability of the message given the
observation. -/
noncomputable def listener : ℕ → Kernel M (X × O)
  | 0 => jointL0 P meaning
  | n + 1 => RSA.listener P fun p ↦ jointSpeaker P lam (listener n) p.2

end Recursion

/-! ### Appendix A: the lexical uncertainty model and its limitation -/

section LexicalUncertainty

variable {W O I M : Type*} [MeasurableSpace W] [MeasurableSpace O] (P : Measure (W × O))

/-- Two observations have the same support when their beliefs leave the same worlds possible. -/
def SameSupport (o₁ o₂ : O) : Prop := ∀ w, P {(w, o₁)} = 0 ↔ P {(w, o₂)} = 0

variable (sem : I → M → Set W)

/-- A message satisfies Quality (A.2) when it is true under the interpretation at every world
the observation leaves possible. -/
def Quality (o : O) (i : I) (m : M) : Prop := ∀ w, P {(w, o)} ≠ 0 → w ∈ sem i m

theorem quality_iff_of_sameSupport {o₁ o₂ : O} (hs : SameSupport P o₁ o₂) {i : I} {m : M} :
    Quality P sem o₁ i m ↔ Quality P sem o₂ i m :=
  forall_congr' fun w ↦ imp_congr_left (not_congr (hs w))

variable [Fintype W] [Fintype O]

theorem snd_preimage_ae_le_iff_quality {o : O} {i : I} {m : M} :
    Prod.snd ⁻¹' {o} ≤ᵐ[P] sem i m ×ˢ Set.univ ↔ Quality P sem o i m := by
  refine ae_iff_of_countable.trans ⟨fun h w hw ↦ (h (w, o) hw rfl).1, ?_⟩
  rintro h ⟨w, o'⟩ hp hpo
  obtain rfl : o' = o := hpo
  exact ⟨h w hp, Set.mem_univ _⟩

variable [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass W]
  [MeasurableSingletonClass O] [MeasurableSingletonClass M] [IsFiniteMeasure P] (cost : M → ℝ)
  (lam : ℝ)

/-- The level-1 speaker (eq. 3), relativized to an interpretation, answers the literal listener
(A.1, eq. 1), who conditions the joint prior on the message's extension under the interpretation.
After an observation she believes the joint prior conditioned on it, so her utility (A.1, eqs. 2
and 5) is the expected log of the listener's joint cell under her belief, less the message
cost. -/
noncomputable def luS1 (i : I) : Kernel O M :=
  RSA.speaker lam cost (RSA.listener P (RSA.truthful fun m ↦ sem i m ×ˢ Set.univ)) fun o ↦
    P[|Prod.snd ⁻¹' {o}]

theorem luS1_apply_singleton_eq_zero_iff (hlam : 0 < lam) {o : O} {i : I} {m : M} :
    luS1 P sem cost lam i o {m} = 0 ↔ ¬ Quality P sem o i m := by
  rw [luS1, RSA.speaker_cond_listener_truthful_apply_singleton_eq_zero_iff hlam,
    snd_preimage_ae_le_iff_quality]

theorem luS1_eq_of_sameSupport (hlam : 0 < lam) {o₁ o₂ : O} (hs : SameSupport P o₁ o₂)
    (ho₁ : P (Prod.snd ⁻¹' {o₁}) ≠ 0) (ho₂ : P (Prod.snd ⁻¹' {o₂}) ≠ 0) (i : I) :
    luS1 P sem cost lam i o₂ = luS1 P sem cost lam i o₁ :=
  RSA.speaker_cond_listener_truthful_apply_eq hlam.le ho₁ ho₂ fun m ↦ by
    rw [snd_preimage_ae_le_iff_quality, snd_preimage_ae_le_iff_quality,
      quality_iff_of_sameSupport P sem hs]

theorem speaker_ofDensity_snd_eq (hlam : 0 ≤ lam) {o₁ o₂ : O}
    (ho₁ : P (Prod.snd ⁻¹' {o₁}) ≠ 0) (ho₂ : P (Prod.snd ⁻¹' {o₂}) ≠ 0) (G : O → M → ℝ≥0∞)
    (hG : ∀ m, G o₂ m = G o₁ m) :
    RSA.speaker lam cost (Kernel.ofDensity P fun m p ↦ G p.2 m)
        (fun o ↦ P[|Prod.snd ⁻¹' {o}]) o₂ =
      RSA.speaker lam cost (Kernel.ofDensity P fun m p ↦ G p.2 m)
        (fun o ↦ P[|Prod.snd ⁻¹' {o}]) o₁ :=
  RSA.speaker_cond_ofDensity_apply_eq hlam ho₁ ho₂ (g := G o₁)
    (fun m p (hp : p.2 = o₁) _ ↦ congrArg (G · m) hp)
    fun m p (hp : p.2 = o₂) _ ↦ (congrArg (G · m) hp).trans (hG m)

variable [Fintype I] [MeasurableSpace I] (PI : Measure I)

/-- The listeners `Lⁿ⁺¹`. The level-1 listener (eq. 4) reweights the joint prior by the level-1
speaker's use of the message, averaged over interpretations, and each later one (eqs. 5–7) by the
previous speaker's. -/
noncomputable def luListener : ℕ → Kernel M (W × O)
  | 0 => RSA.listener P fun p ↦ (∑ i, PI {i} • luS1 P sem cost lam i) p.2
  | n + 1 => RSA.listener P fun p ↦
      RSA.speaker lam cost (luListener n) (fun o ↦ P[|Prod.snd ⁻¹' {o}]) p.2

/-- The speaker `Sⁿ⁺²` (eq. 6), answering `luListener n`. -/
noncomputable def luSpeaker (n : ℕ) : Kernel O M :=
  RSA.speaker lam cost (luListener P sem cost lam PI n) fun o ↦ P[|Prod.snd ⁻¹' {o}]

/-- In the lexical uncertainty model, observations with the same support yield the same speaker
at every level, so the choice of message depends on the support of the speaker's belief and not
on its shape ((A-8), the limitation (18)). -/
theorem luSpeaker_eq_of_sameSupport (hlam : 0 < lam) {o₁ o₂ : O} (hs : SameSupport P o₁ o₂)
    (ho₁ : P (Prod.snd ⁻¹' {o₁}) ≠ 0) (ho₂ : P (Prod.snd ⁻¹' {o₂}) ≠ 0) (n : ℕ) :
    luSpeaker P sem cost lam PI n o₂ = luSpeaker P sem cost lam PI n o₁ := by
  induction n with
  | zero =>
    exact speaker_ofDensity_snd_eq P cost lam hlam.le ho₁ ho₂
      (fun o m ↦ (∑ i, PI {i} • luS1 P sem cost lam i) o {m}) fun m ↦ by
        simp only [sum_apply, smul_apply, luS1_eq_of_sameSupport P sem cost lam hlam hs ho₁ ho₂]
  | succ n ih =>
    exact speaker_ofDensity_snd_eq P cost lam hlam.le ho₁ ho₂
      (fun o m ↦ luSpeaker P sem cost lam PI n o {m}) fun m ↦ by rw [ih]

end LexicalUncertainty

/-! ### Appendix B: the weighted interpretation rule -/

section WIR

variable {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
  (μ : Measure X) (ν : Measure ℕ) (d : X → ℕ)

/-- The values within radius `y` of the target. -/
def within (d : X → ℕ) (y : ℕ) : Set X := {x | d x ≤ y}

/-- The weighted rule (WIR) mixes the prior conditioned on each interval by the prior over
radii. -/
noncomputable def wir : Measure X := ν.bind fun y ↦ μ[|within d y]

/-- The posterior over radii after "around". -/
noncomputable def radiusPosterior : Measure ℕ := ((μ.prod ν)[|AroundEvent d]).map Prod.snd

variable [SFinite ν]

theorem radiusPosterior_apply_singleton (y : ℕ) :
    radiusPosterior μ ν d {y} = μ (within d y) * ν {y} / ∫⁻ x, aroundWeight ν d x ∂μ := by
  rw [radiusPosterior, Measure.map_apply measurable_snd (.singleton y),
    cond_apply' (measurable_snd (.singleton y)), prod_apply_aroundEvent, ENNReal.div_eq_inv_mul,
    show AroundEvent d ∩ Prod.snd ⁻¹' {y} = within d y ×ˢ {y} from ?_, Measure.prod_prod]
  ext ⟨x', y'⟩
  simp only [AroundEvent, within, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_prod]
  constructor <;> rintro ⟨h, rfl⟩ <;> exact ⟨h, rfl⟩

theorem within_dist (n y : ℕ) : within (Nat.dist n) y = Set.Icc (n - y) (n + y) :=
  Set.ext fun x ↦ by simp only [within, Set.mem_ofPred_eq, Set.mem_Icc]; unfold Nat.dist; omega

variable [IsFiniteMeasure μ]

theorem bir_eq_bind_radiusPosterior :
    bir μ ν d = (radiusPosterior μ ν d).bind fun y ↦ μ[|within d y] :=
  Measure.ext_of_singleton fun x ↦ by
    have hcond : ∀ y, μ[|within d y] {x} * radiusPosterior μ ν d {y} =
        μ {x} / (∫⁻ x', aroundWeight ν d x' ∂μ) * (Set.Ici (d x)).indicator (fun y ↦ ν {y}) y := by
      intro y
      rw [radiusPosterior_apply_singleton, cond_apply' (.singleton x)]
      by_cases hy : d x ≤ y
      · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy),
          Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (show x ∈ within d y from hy))]
        rcases eq_or_ne (μ (within d y)) 0 with h0 | h0
        · rw [measure_mono_null (Set.singleton_subset_iff.mpr (show x ∈ within d y from hy)) h0,
            mul_zero, zero_mul,
            ENNReal.zero_div, zero_mul]
        · rw [div_eq_mul_inv, div_eq_mul_inv, show (μ (within d y))⁻¹ * μ {x} *
              (μ (within d y) * ν {y} * (∫⁻ x', aroundWeight ν d x' ∂μ)⁻¹) =
              μ {x} * (∫⁻ x', aroundWeight ν d x' ∂μ)⁻¹ * ν {y} *
                ((μ (within d y))⁻¹ * μ (within d y)) by ring,
            ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), mul_one]
      · rw [Set.indicator_of_notMem (fun h ↦ hy (Set.mem_Ici.mp h)),
          Set.inter_singleton_eq_empty.mpr (show x ∉ within d y from hy), measure_empty, mul_zero,
          zero_mul, mul_zero]
    rw [bir_apply_singleton, Measure.bind_apply (.singleton x) measurable_from_nat.aemeasurable]
    conv_rhs => rw [lintegral_countable']
    simp only [hcond]
    rw [ENNReal.tsum_mul_left, Measure.tsum_indicator_apply_singleton ν _ .of_discrete,
      aroundWeight, ENNReal.mul_div_right_comm]

/-- At `n = 1` with uniform priors the weighted rule puts `2/3` on the target where the Bayesian
rule puts `1/2`, so the two rules differ (Figure 2 against Figure 5). -/
theorem wir_ne_bir :
    wir (unif 2) ((2 : ℝ≥0∞)⁻¹ • unif 1) (Nat.dist 1) ≠
      bir (unif 2) ((2 : ℝ≥0∞)⁻¹ • unif 1) (Nat.dist 1) := by
  intro h
  have hc : ∀ y ≤ 1,
      (unif 2)[|within (Nat.dist 1) y] {1} = ((1 + y + 1 - (1 - y) : ℕ) : ℝ≥0∞)⁻¹ := by
    intro y hy
    rw [cond_apply' (.singleton 1), within_dist,
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (Set.mem_Icc.mpr ⟨by omega, by omega⟩)),
      unif_apply_Icc (by omega), unif_apply_singleton, ite_eq_left (by norm_num), mul_one]
  have hw : (wir (unif 2) ((2 : ℝ≥0∞)⁻¹ • unif 1) (Nat.dist 1)).real {1} = 2 / 3 := by
    rw [measureReal_def, wir, Measure.bind_apply (.singleton 1) measurable_from_nat.aemeasurable,
      lintegral_smul_measure, lintegral_unif, Finset.sum_range_succ, Finset.sum_range_one,
      hc 0 (by norm_num), hc 1 le_rfl, smul_eq_mul]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_inv]
  have hb : (bir (unif 2) ((2 : ℝ≥0∞)⁻¹ • unif 1) (Nat.dist 1)).real {1} = 1 / 2 := by
    rw [measureReal_def, bir_apply_singleton, lintegral_unif, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, unif_apply_singleton, ite_eq_left (by norm_num),
      one_mul]
    simp only [aroundWeight, Measure.smul_apply, smul_eq_mul, unif_apply_Ici, Nat.dist]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]
  rw [h, hb] at hw
  norm_num at hw

end WIR

end EgreEtAl2023
