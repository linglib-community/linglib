/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.Independence.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Weight of evidence

Bayes' theorem in odds form says that conditioning on an event `t` multiplies the odds of an event
`s` by the likelihood ratio of `s` on `t`:
`μ[s | t] / μ[sᶜ | t] = μ s / μ sᶜ * (μ[t | s] / μ[t | sᶜ])`. We define the weight of evidence that
`t` provides for `s` as the logarithm of that ratio,
`weightOfEvidence μ s t = log (μ[t | s] / μ[t | sᶜ])`, so that conditioning on `t` adds it to the
logarithm of the odds of `s`. It is an extended real, `⊤` when `t` is possible only given `s` and
`⊥` when it is possible only given `sᶜ`.

The weight is positive exactly when `s` makes `t` more probable than `sᶜ` does, which for a
probability measure is when `s` raises the probability of `t`, and it is zero exactly when the two
conditional probabilities agree, which is when the events are independent. Replacing `s` by its
complement negates the weight, and the weight of a conjunction of two events that are independent
given `s` and given `sᶜ` is the sum of their weights. Two such events have covariance
`μ s * μ sᶜ * (μ[a | s] - μ[a | sᶜ]) * (μ[b | s] - μ[b | sᶜ])`, so they are negatively correlated
exactly when they bear on `s` with opposite signs.

## Main definitions

* `weightOfEvidence μ s t`: the logarithm of `μ[t | s] / μ[t | sᶜ]`, and `0` when `μ t = 0`.

## Main results

* `cond_div_cond_compl`: Bayes' theorem in odds form.
* `log_cond_div_cond_compl`: conditioning on `t` adds its weight to the logarithm of the odds.
* `weightOfEvidence_pos_iff`: the weight is positive exactly when `μ[t | sᶜ] < μ[t | s]`.
* `weightOfEvidence_compl`: the weight for `sᶜ` is the negative of the weight for `s`.
* `weightOfEvidence_inter`: the weight is additive over events independent given `s` and given
  `sᶜ`.
* `weightOfEvidence_eq_zero_iff_indepSet`: the weight vanishes exactly at independence.
* `measureReal_inter_sub_mul_of_indepSet_cond`: the covariance of two events independent given
  `s` and given `sᶜ`.
* `sign_weightOfEvidence_count`: under the counting measure the sign of the weight compares
  cross-products of counts.

## Implementation notes

The weight is valued in `EReal` through `ENNReal.log`, which is strictly monotone and takes `0` to
`⊥` and `⊤` to `⊤`, so the infinite cases need no hypotheses. An event of measure zero is given
weight `0`, where the ratio `0 / 0` would give `⊥`. Independence given `s` and given `sᶜ` is
`IndepSet` at the two conditioned measures. The odds form of Bayes' theorem is an `[UPSTREAM]`
candidate for `Mathlib/Probability/ConditionalProbability.lean`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t a b : Set Ω}

/-! ### Odds -/

/-- **Bayes' theorem in odds form**: conditioning on `t` multiplies the odds of `s` by the
likelihood ratio of `s` on `t`. -/
theorem cond_div_cond_compl [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ[s | t] / μ[sᶜ | t] = μ s / μ sᶜ * (μ[t | s] / μ[t | sᶜ]) := by
  rcases eq_or_ne (μ t) 0 with h0 | h0
  · simp [cond_eq_zero_of_meas_eq_zero h0, (cond_absolutelyContinuous h0 : μ[t | s] = 0)]
  rw [cond_apply ht, cond_apply ht, ENNReal.mul_div_mul_left _ _
    (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) (ENNReal.inv_ne_top.2 h0), cond_apply hs,
    cond_apply hs.compl, inter_comm t, inter_comm t]
  rcases eq_or_ne (μ s) 0 with hs0 | hs0
  · simp [hs0, measure_mono_null inter_subset_left hs0]
  rcases eq_or_ne (μ sᶜ) 0 with hc0 | hc0
  · simp [hc0, measure_mono_null inter_subset_left hc0, ENNReal.div_zero hs0]
    rcases eq_or_ne (μ (s ∩ t)) 0 with h | h
    · simp [h]
    · simp [ENNReal.div_zero h, ENNReal.div_zero (mul_ne_zero
        (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) h)]
  · rw [ENNReal.mul_div_mul_comm (.inl (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)))
        (.inl (ENNReal.inv_ne_top.2 hc0)), ← mul_assoc, ← ENNReal.mul_div_mul_comm
        (.inl hc0) (.inl (measure_ne_top _ _)), ENNReal.mul_inv_cancel hs0 (measure_ne_top _ _),
      ENNReal.mul_inv_cancel hc0 (measure_ne_top _ _), div_one, one_mul]

/-- An event is more probable given `s` than given `sᶜ` exactly when `s` raises its
probability. -/
theorem cond_compl_lt_cond_iff [IsProbabilityMeasure μ] (hs : MeasurableSet s)
    (hcs' : μ sᶜ ≠ 0) : μ[t | sᶜ] < μ[t | s] ↔ μ t < μ[t | s] := by
  rw [← cond_add_cond_compl_eq hs μ]
  conv_rhs => rhs; rw [← mul_one (μ[t | s]), ← prob_add_prob_compl (μ := μ) hs, mul_add]
  rw [ENNReal.add_lt_add_iff_left (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.mul_lt_mul_iff_left hcs' (measure_ne_top _ _)]

/-- A possible event is possible given `s` or given `sᶜ`. -/
theorem cond_compl_ne_zero_or_cond_ne_zero [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (ht : μ t ≠ 0) : μ[t | sᶜ] ≠ 0 ∨ μ[t | s] ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not, cond_apply hs.compl, cond_apply hs, mul_eq_zero, mul_eq_zero,
    ENNReal.inv_eq_zero, ENNReal.inv_eq_zero] at h
  refine ht ?_
  rw [← measure_inter_add_sdiff t hs, inter_comm, sdiff_eq, inter_comm t,
    h.2.resolve_left (measure_ne_top _ _), h.1.resolve_left (measure_ne_top _ _), add_zero]

/-! ### Independence given an event and given its complement -/

/-- An event is as probable given `s` as given `sᶜ` exactly when it is independent of `s`. -/
theorem cond_eq_cond_compl_iff_indepSet [IsProbabilityMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hcs : μ s ≠ 0) (hcs' : μ sᶜ ≠ 0) :
    μ[t | s] = μ[t | sᶜ] ↔ IndepSet s t μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hc : μ[t | s] = μ t := by
      have := cond_add_cond_compl_eq (t := t) hs μ
      rwa [← h, ← mul_add, measure_add_measure_compl hs, measure_univ, mul_one] at this
    rw [indepSet_iff_measure_inter_eq_mul hs ht μ, ← cond_mul_eq_inter hs, hc, mul_comm]
  · rw [h.cond_apply hs hcs, h.compl_left.cond_apply hs.compl hcs']

/-- Two events that are independent given `s` and given `sᶜ` have covariance
`μ s * μ sᶜ * (μ[a | s] - μ[a | sᶜ]) * (μ[b | s] - μ[b | sᶜ])`. -/
theorem measureReal_inter_sub_mul_of_indepSet_cond [IsProbabilityMeasure μ]
    (hs : MeasurableSet s) (hcs : μ s ≠ 0) (hcs' : μ sᶜ ≠ 0) (h : IndepSet a b μ[|s])
    (h' : IndepSet a b μ[|sᶜ]) :
    μ.real (a ∩ b) - μ.real a * μ.real b =
      μ.real s * μ.real sᶜ * (μ[|s].real a - μ[|sᶜ].real a) *
        (μ[|s].real b - μ[|sᶜ].real b) := by
  have hsplit (e : Set Ω) : μ.real e = μ.real (s ∩ e) + μ.real (sᶜ ∩ e) := by
    rw [← measureReal_inter_add_sdiff (s := e) hs, sdiff_eq, inter_comm e, inter_comm e]
  have hp : μ.real s ≠ 0 := (ENNReal.toReal_pos hcs (measure_ne_top μ _)).ne'
  have hn : μ.real sᶜ ≠ 0 := (ENNReal.toReal_pos hcs' (measure_ne_top μ _)).ne'
  have hsum : μ.real s + μ.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs, probReal_univ]
  have h₁ := h.measureReal_inter_eq_mul
  have h₂ := h'.measureReal_inter_eq_mul
  rw [cond_real_apply μ hs, cond_real_apply μ hs, cond_real_apply μ hs] at h₁
  rw [cond_real_apply μ hs.compl, cond_real_apply μ hs.compl, cond_real_apply μ hs.compl] at h₂
  rw [cond_real_apply μ hs, cond_real_apply μ hs, cond_real_apply μ hs.compl,
    cond_real_apply μ hs.compl, hsplit a, hsplit b, hsplit (a ∩ b)]
  field_simp at h₁ h₂ ⊢
  linear_combination μ.real sᶜ * h₁ + μ.real s * h₂ -
    (μ.real (s ∩ a) * μ.real (s ∩ b) * μ.real sᶜ +
      μ.real (sᶜ ∩ a) * μ.real (sᶜ ∩ b) * μ.real s) * hsum

/-! ### Weight of evidence -/

open Classical in
/-- The weight of evidence that `t` provides for `s` is the logarithm of the likelihood ratio
`μ[t | s] / μ[t | sᶜ]`, and `0` for a `t` of measure zero. -/
noncomputable def weightOfEvidence (μ : Measure Ω) (s t : Set Ω) : EReal :=
  if μ t = 0 then 0 else ENNReal.log (μ[t | s] / μ[t | sᶜ])

theorem weightOfEvidence_of_measure_eq_zero (h : μ t = 0) : weightOfEvidence μ s t = 0 := by
  simp [weightOfEvidence, h]

theorem weightOfEvidence_of_measure_ne_zero (h : μ t ≠ 0) :
    weightOfEvidence μ s t = ENNReal.log (μ[t | s] / μ[t | sᶜ]) := by
  simp [weightOfEvidence, h]

theorem weightOfEvidence_congr {u : Set Ω} (h : t =ᵐ[μ] u) :
    weightOfEvidence μ s t = weightOfEvidence μ s u := by
  simp only [weightOfEvidence, measure_congr h,
    measure_congr (h.filter_mono cond_absolutelyContinuous.ae_le)]

/-- Conditioning on a possible event adds its weight of evidence to the logarithm of the odds. -/
theorem log_cond_div_cond_compl [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : μ t ≠ 0) :
    ENNReal.log (μ[s | t] / μ[sᶜ | t]) = ENNReal.log (μ s / μ sᶜ) + weightOfEvidence μ s t := by
  rw [weightOfEvidence_of_measure_ne_zero h, ← ENNReal.log_mul_add, cond_div_cond_compl hs ht]

/-- The weight of evidence is positive exactly when `s` makes `t` more probable than `sᶜ`
does. -/
theorem weightOfEvidence_pos_iff : 0 < weightOfEvidence μ s t ↔ μ[t | sᶜ] < μ[t | s] := by
  by_cases h : μ t = 0
  · simp [weightOfEvidence_of_measure_eq_zero h, (cond_absolutelyContinuous h : μ[t | s] = 0)]
  · rw [weightOfEvidence_of_measure_ne_zero h, ENNReal.zero_lt_log_iff,
      ENNReal.lt_div_iff_mul_lt (.inr ENNReal.one_ne_top) (.inr one_ne_zero), one_mul]

/-- The weight of evidence is negative exactly when `sᶜ` makes `t` more probable than `s`
does. -/
theorem weightOfEvidence_neg_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) :
    weightOfEvidence μ s t < 0 ↔ μ[t | s] < μ[t | sᶜ] := by
  by_cases h : μ t = 0
  · simp [weightOfEvidence_of_measure_eq_zero h, (cond_absolutelyContinuous h : μ[t | sᶜ] = 0)]
  · rw [weightOfEvidence_of_measure_ne_zero h, ENNReal.log_lt_zero_iff,
      ENNReal.div_lt_iff (cond_compl_ne_zero_or_cond_ne_zero hs h) (.inl (measure_ne_top _ _)),
      one_mul]

theorem weightOfEvidence_eq_zero_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) :
    weightOfEvidence μ s t = 0 ↔ μ[t | s] = μ[t | sᶜ] := by
  rw [le_antisymm_iff, le_antisymm_iff, ← not_lt, ← not_lt, weightOfEvidence_pos_iff,
    weightOfEvidence_neg_iff hs, not_lt, not_lt]

/-- The weight of evidence is `⊤` exactly when `t` is possible given `s` and impossible given
`sᶜ`. -/
theorem weightOfEvidence_eq_top_iff :
    weightOfEvidence μ s t = ⊤ ↔ μ[t | s] ≠ 0 ∧ μ[t | sᶜ] = 0 := by
  by_cases ht : μ t = 0
  · simp [weightOfEvidence_of_measure_eq_zero ht, (cond_absolutelyContinuous ht : μ[t | s] = 0)]
  · rw [weightOfEvidence_of_measure_ne_zero ht, ENNReal.log_eq_top_iff, ENNReal.div_eq_top]
    simp [measure_ne_top]

theorem weightOfEvidence_lt_top (h : μ[t | sᶜ] ≠ 0) : weightOfEvidence μ s t < ⊤ := by
  by_cases ht : μ t = 0
  · simp [weightOfEvidence_of_measure_eq_zero ht]
  · rw [weightOfEvidence_of_measure_ne_zero ht, ENNReal.log_lt_top_iff]
    exact ENNReal.div_lt_top (measure_ne_top _ _) h

theorem bot_lt_weightOfEvidence (h : μ[t | s] ≠ 0) : ⊥ < weightOfEvidence μ s t := by
  by_cases ht : μ t = 0
  · simp [weightOfEvidence_of_measure_eq_zero ht]
  · rw [weightOfEvidence_of_measure_ne_zero ht, ENNReal.bot_lt_log_iff]
    exact ENNReal.div_pos h (measure_ne_top _ _)

/-- A finite weight of evidence is the real logarithm of the ratio of the two conditional
probabilities. -/
theorem weightOfEvidence_eq_coe_log (h : μ[t | s] ≠ 0) (h' : μ[t | sᶜ] ≠ 0) :
    weightOfEvidence μ s t = (Real.log (μ[|s].real t / μ[|sᶜ].real t) : ℝ) := by
  rw [weightOfEvidence_of_measure_ne_zero fun h₀ ↦ h (cond_absolutelyContinuous h₀),
    ENNReal.log_pos_real (ENNReal.div_ne_zero.2 ⟨h, measure_ne_top _ _⟩)
      (ENNReal.div_ne_top (measure_ne_top _ _) h'),
    ENNReal.toReal_div, measureReal_def, measureReal_def]

/-- Between possible events, weights of evidence compare as the likelihood ratios do. -/
theorem weightOfEvidence_lt_weightOfEvidence_iff {u : Set Ω} (ht : μ t ≠ 0) (hu : μ u ≠ 0) :
    weightOfEvidence μ s t < weightOfEvidence μ s u ↔
      μ[t | s] / μ[t | sᶜ] < μ[u | s] / μ[u | sᶜ] := by
  rw [weightOfEvidence_of_measure_ne_zero ht, weightOfEvidence_of_measure_ne_zero hu,
    ENNReal.log_lt_log_iff]

/-- The sign of the weight of evidence is the sign of the difference of the two conditional
probabilities. -/
theorem sign_weightOfEvidence [IsFiniteMeasure μ] (hs : MeasurableSet s) :
    SignType.sign (weightOfEvidence μ s t) =
      SignType.sign (μ[|s].real t - μ[|sᶜ].real t) := by
  have hlt (u v : Set Ω) : μ[|u].real t < μ[|v].real t ↔ μ[t | u] < μ[t | v] :=
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)
  rcases lt_trichotomy (μ[t | sᶜ]) (μ[t | s]) with h | h | h
  · rw [sign_pos (weightOfEvidence_pos_iff.2 h), sign_pos (sub_pos.2 ((hlt _ _).2 h))]
  · rw [(weightOfEvidence_eq_zero_iff hs).2 h.symm, measureReal_def, measureReal_def, h, sub_self,
      sign_zero, sign_zero]
  · rw [sign_neg ((weightOfEvidence_neg_iff hs).2 h), sign_neg (sub_neg.2 ((hlt _ _).2 h))]

/-- A possible event that entails `s` has positive weight of evidence for it. -/
theorem weightOfEvidence_pos_of_subset [IsFiniteMeasure μ] (hs : MeasurableSet s) (h : t ⊆ s)
    (ht : μ t ≠ 0) : 0 < weightOfEvidence μ s t := by
  rw [weightOfEvidence_pos_iff, cond_apply hs.compl,
    (disjoint_compl_left_iff_subset.2 h).inter_eq, measure_empty, mul_zero]
  exact cond_pos_of_inter_ne_zero hs (by rwa [inter_eq_right.2 h])

/-- A possible event that entails `sᶜ` has negative weight of evidence for `s`. -/
theorem weightOfEvidence_neg_of_subset_compl [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (h : t ⊆ sᶜ) (ht : μ t ≠ 0) : weightOfEvidence μ s t < 0 := by
  rw [weightOfEvidence_neg_iff hs, cond_apply hs,
    (subset_compl_iff_disjoint_left.1 h).inter_eq, measure_empty, mul_zero]
  exact cond_pos_of_inter_ne_zero hs.compl (by rwa [inter_eq_right.2 h])

/-- The weight of evidence for `sᶜ` is the negative of the weight of evidence for `s`. -/
theorem weightOfEvidence_compl [IsFiniteMeasure μ] (hs : MeasurableSet s) :
    weightOfEvidence μ sᶜ t = -weightOfEvidence μ s t := by
  by_cases h : μ t = 0
  · simp [weightOfEvidence_of_measure_eq_zero h]
  · rw [weightOfEvidence_of_measure_ne_zero h, weightOfEvidence_of_measure_ne_zero h, compl_compl,
      ← ENNReal.log_inv, ENNReal.inv_div (.inl (measure_ne_top _ _))
        (cond_compl_ne_zero_or_cond_ne_zero hs h)]

/-- The weight of evidence is additive over events that are independent given `s` and given
`sᶜ`. -/
theorem weightOfEvidence_inter (h : IndepSet a b μ[|s]) (h' : IndepSet a b μ[|sᶜ])
    (hab : μ (a ∩ b) ≠ 0) :
    weightOfEvidence μ s (a ∩ b) = weightOfEvidence μ s a + weightOfEvidence μ s b := by
  rw [weightOfEvidence_of_measure_ne_zero hab,
    weightOfEvidence_of_measure_ne_zero fun h₀ ↦ hab (measure_mono_null inter_subset_left h₀),
    weightOfEvidence_of_measure_ne_zero fun h₀ ↦ hab (measure_mono_null inter_subset_right h₀),
    h.measure_inter_eq_mul, h'.measure_inter_eq_mul,
    ENNReal.mul_div_mul_comm (.inr (measure_ne_top _ _)) (.inl (measure_ne_top _ _)),
    ENNReal.log_mul_add]

/-- For a probability measure and an `s` of probability strictly between zero and one, the weight
of evidence that `t` provides for `s` is zero exactly when the two are independent. -/
theorem weightOfEvidence_eq_zero_iff_indepSet [IsProbabilityMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hcs : μ s ≠ 0) (hcs' : μ sᶜ ≠ 0) :
    weightOfEvidence μ s t = 0 ↔ IndepSet s t μ :=
  (weightOfEvidence_eq_zero_iff hs).trans (cond_eq_cond_compl_iff_indepSet hs ht hcs hcs')

/-! ### The counting measure -/

/-- Under the counting measure on a finite type the sign of the weight of evidence compares
cross-products of counts. -/
theorem sign_weightOfEvidence_count [Fintype Ω] [MeasurableSingletonClass Ω] (hs : s.Nonempty)
    (hs' : sᶜ.Nonempty) (t : Set Ω) :
    SignType.sign (weightOfEvidence .count s t) =
      SignType.sign ((s ∩ t).ncard * sᶜ.ncard - (sᶜ ∩ t).ncard * s.ncard : ℤ) := by
  have h₁ : (0 : ℝ) < s.ncard := by exact_mod_cast (ncard_pos s.toFinite).2 hs
  have h₂ : (0 : ℝ) < sᶜ.ncard := by exact_mod_cast (ncard_pos sᶜ.toFinite).2 hs'
  rw [sign_weightOfEvidence s.toFinite.measurableSet,
    show (Measure.count[|s]).real t = _ from uniformOn_real_apply s t,
    show (Measure.count[|sᶜ]).real t = _ from uniformOn_real_apply sᶜ t,
    div_sub_div _ _ h₁.ne' h₂.ne', div_eq_mul_inv, sign_mul,
    sign_pos (inv_pos.2 (mul_pos h₁ h₂)), mul_one, ← sign_intCast (α := ℝ)]
  push_cast
  ring_nf

end ProbabilityTheory
