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

For a measure `μ` and events `s` and `t`, the weight of evidence that `t` provides for `s` is the
logarithm of the likelihood ratio, `log (μ[t | s] / μ[t | sᶜ])`. By Bayes' theorem in odds form,
`μ[s | t] / μ[sᶜ | t] = μ s / μ sᶜ * (μ[t | s] / μ[t | sᶜ])`, it is the amount that conditioning
on a possible `t` adds to the logarithm of the odds of `s`.

## Main statements

* `cond_div_cond_compl`: Bayes' theorem in odds form.
* `weightOfEvidence_pos_iff`: the weight is positive if and only if `μ[t | sᶜ] < μ[t | s]`.
* `weightOfEvidence_compl`: the weight of `t` for `sᶜ` is the negative of its weight for `s`.
* `weightOfEvidence_inter`: weights add over events independent given `s` and given `sᶜ`
  whose intersection is possible.
* `weightOfEvidence_eq_zero_iff_indepSet`: for a probability measure and `0 < μ s < 1`, the
  weight is zero if and only if `s` and `t` are independent.

## Implementation notes

The weight is an extended real, `⊤` when `t` is possible only given `s` and `⊥` when it is
possible only given `sᶜ`. When `t` is possible given neither, the weight is `0` and not the
logarithm `⊥` of `0 / 0`, so that the weight for `sᶜ` is the negative of the weight for `s` with
no hypothesis. For a finite measure this is the case `μ t = 0`.

`[UPSTREAM]` The lemmas of the first section are candidates for
`Mathlib/Probability/ConditionalProbability.lean`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s t a b : Set Ω}

/-! ### Odds -/

/-- **Bayes' theorem in odds form**: conditioning on `t` multiplies the odds of `s` by the
likelihood ratio of `s` on `t`. -/
theorem cond_div_cond_compl [IsFiniteMeasure μ] (hs : MeasurableSet s) :
    μ[s | t] / μ[sᶜ | t] = μ s / μ sᶜ * (μ[t | s] / μ[t | sᶜ]) := by
  rw [← ENNReal.mul_div_mul_comm (.inr (measure_ne_top _ _)) (.inl (measure_ne_top _ _)),
    mul_comm (μ s), mul_comm (μ sᶜ), cond_mul_eq_inter hs, cond_mul_eq_inter hs.compl]
  rcases eq_or_ne (μ t) 0 with h0 | h0
  · simp [cond_eq_zero_of_meas_eq_zero h0, measure_mono_null inter_subset_right h0]
  · rw [cond_apply' hs, cond_apply' hs.compl, ENNReal.mul_div_mul_left _ _
      (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) (ENNReal.inv_ne_top.2 h0), inter_comm t,
      inter_comm t]

private theorem measure_inter_eq_zero_of_cond_eq_zero [IsFiniteMeasure μ] (h : μ[t | s] = 0) :
    μ (t ∩ s) = 0 := by
  rw [cond, smul_apply, smul_eq_mul, mul_eq_zero, ENNReal.inv_eq_zero] at h
  exact le_antisymm ((Measure.le_restrict_apply _ _).trans
    (h.resolve_left (measure_ne_top _ _)).le) zero_le

/-- A possible event is possible given `s` or given `sᶜ`. -/
theorem cond_ne_zero_or_cond_compl_ne_zero [IsFiniteMeasure μ] (hct : μ t ≠ 0) :
    μ[t | s] ≠ 0 ∨ μ[t | sᶜ] ≠ 0 := by
  by_contra! h
  refine hct (measure_mono_null (fun x hx ↦ ?_) (measure_union_null
    (measure_inter_eq_zero_of_cond_eq_zero h.1) (measure_inter_eq_zero_of_cond_eq_zero h.2)))
  by_cases hx' : x ∈ s
  exacts [.inl ⟨hx, hx'⟩, .inr ⟨hx, hx'⟩]

/-! ### Independence given an event and given its complement -/

/-- An event is as probable given `s` as given `sᶜ` exactly when it is independent of `s`. -/
theorem cond_eq_cond_compl_iff_indepSet [IsProbabilityMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hcs : μ s ≠ 0) (hcsc : μ sᶜ ≠ 0) :
    μ[t | s] = μ[t | sᶜ] ↔ IndepSet s t μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hc : μ[t | s] = μ t := by
      have := cond_add_cond_compl_eq (t := t) hs μ
      rwa [← h, ← mul_add, measure_add_measure_compl hs, measure_univ, mul_one] at this
    rw [indepSet_iff_measure_inter_eq_mul hs ht μ, ← cond_mul_eq_inter hs, hc, mul_comm]
  · rw [h.cond_apply hs hcs, h.compl_left.cond_apply hs.compl hcsc]

/-- Two events that are independent given `s` and given `sᶜ` have covariance
`μ s * μ sᶜ * (μ[a | s] - μ[a | sᶜ]) * (μ[b | s] - μ[b | sᶜ])`. -/
theorem measureReal_inter_sub_mul_of_indepSet_cond [IsProbabilityMeasure μ]
    (hs : MeasurableSet s) (hcs : μ s ≠ 0) (hcsc : μ sᶜ ≠ 0) (h : IndepSet a b μ[|s])
    (h' : IndepSet a b μ[|sᶜ]) :
    μ.real (a ∩ b) - μ.real a * μ.real b =
      μ.real s * μ.real sᶜ * (μ[|s].real a - μ[|sᶜ].real a) *
        (μ[|s].real b - μ[|sᶜ].real b) := by
  have hsplit (e : Set Ω) : μ.real e = μ.real (s ∩ e) + μ.real (sᶜ ∩ e) := by
    rw [← measureReal_inter_add_sdiff (s := e) hs, sdiff_eq, inter_comm e, inter_comm e]
  have hp : μ.real s ≠ 0 := (ENNReal.toReal_pos hcs (measure_ne_top μ _)).ne'
  have hn : μ.real sᶜ ≠ 0 := (ENNReal.toReal_pos hcsc (measure_ne_top μ _)).ne'
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

/-- The weight of evidence that `t` provides for `s` is the logarithm of the likelihood ratio
`μ[t | s] / μ[t | sᶜ]`, and `0` when both conditional probabilities are zero. -/
noncomputable def weightOfEvidence (μ : Measure Ω) (s t : Set Ω) : EReal :=
  if μ[t | s] = 0 ∧ μ[t | sᶜ] = 0 then 0 else ENNReal.log (μ[t | s] / μ[t | sᶜ])

theorem weightOfEvidence_of_ne_zero (h : μ[t | s] ≠ 0 ∨ μ[t | sᶜ] ≠ 0) :
    weightOfEvidence μ s t = ENNReal.log (μ[t | s] / μ[t | sᶜ]) :=
  ite_eq_right (by tauto)

theorem weightOfEvidence_of_measure_eq_zero (h : μ t = 0) : weightOfEvidence μ s t = 0 :=
  ite_eq_left ⟨cond_absolutelyContinuous h, cond_absolutelyContinuous h⟩

theorem weightOfEvidence_of_measure_ne_zero [IsFiniteMeasure μ] (h : μ t ≠ 0) :
    weightOfEvidence μ s t = ENNReal.log (μ[t | s] / μ[t | sᶜ]) :=
  weightOfEvidence_of_ne_zero (cond_ne_zero_or_cond_compl_ne_zero h)

theorem weightOfEvidence_congr {u : Set Ω} (h : t =ᵐ[μ] u) :
    weightOfEvidence μ s t = weightOfEvidence μ s u := by
  simp only [weightOfEvidence, measure_congr (h.filter_mono cond_absolutelyContinuous.ae_le)]

/-- Conditioning on a possible event adds its weight of evidence to the logarithm of the odds. -/
theorem log_cond_div_cond_compl [IsFiniteMeasure μ] (hs : MeasurableSet s) (hct : μ t ≠ 0) :
    ENNReal.log (μ[s | t] / μ[sᶜ | t]) = ENNReal.log (μ s / μ sᶜ) + weightOfEvidence μ s t := by
  rw [weightOfEvidence_of_measure_ne_zero hct, ← ENNReal.log_mul_add, cond_div_cond_compl hs]

/-- The weight of evidence is positive exactly when `s` makes `t` more probable than `sᶜ`
does. -/
theorem weightOfEvidence_pos_iff : 0 < weightOfEvidence μ s t ↔ μ[t | sᶜ] < μ[t | s] := by
  unfold weightOfEvidence
  split_ifs with h
  · simp [h.1, h.2]
  · rw [ENNReal.zero_lt_log_iff,
      ENNReal.lt_div_iff_mul_lt (.inr ENNReal.one_ne_top) (.inr one_ne_zero), one_mul]

/-- The weight of evidence is negative exactly when `sᶜ` makes `t` more probable than `s`
does. -/
theorem weightOfEvidence_neg_iff : weightOfEvidence μ s t < 0 ↔ μ[t | s] < μ[t | sᶜ] := by
  unfold weightOfEvidence
  split_ifs with h
  · simp [h.1, h.2]
  · rw [ENNReal.log_lt_zero_iff, ENNReal.div_lt_iff (by tauto) (.inl (measure_ne_top _ _)),
      one_mul]

theorem weightOfEvidence_eq_zero_iff : weightOfEvidence μ s t = 0 ↔ μ[t | s] = μ[t | sᶜ] := by
  rw [le_antisymm_iff, le_antisymm_iff, ← not_lt, ← not_lt, weightOfEvidence_pos_iff,
    weightOfEvidence_neg_iff, not_lt, not_lt]

/-- The weight of evidence for `sᶜ` is the negative of the weight of evidence for `s`. -/
theorem weightOfEvidence_compl : weightOfEvidence μ sᶜ t = -weightOfEvidence μ s t := by
  unfold weightOfEvidence
  rw [compl_compl]
  by_cases h : μ[t | s] = 0 ∧ μ[t | sᶜ] = 0
  · rw [ite_eq_left h, ite_eq_left h.symm, neg_zero]
  · rw [ite_eq_right h, ite_eq_right (mt And.symm h), ← ENNReal.log_inv,
      ENNReal.inv_div (.inl (measure_ne_top _ _)) (by tauto)]

/-- The weight of evidence is `⊤` exactly when `t` is possible given `s` and impossible given
`sᶜ`. -/
theorem weightOfEvidence_eq_top_iff :
    weightOfEvidence μ s t = ⊤ ↔ μ[t | s] ≠ 0 ∧ μ[t | sᶜ] = 0 := by
  unfold weightOfEvidence
  split_ifs with h
  · simp [h.1]
  · rw [ENNReal.log_eq_top_iff, ENNReal.div_eq_top]
    simp [measure_ne_top]

/-- The weight of evidence is `⊥` exactly when `t` is impossible given `s` and possible given
`sᶜ`. -/
theorem weightOfEvidence_eq_bot_iff :
    weightOfEvidence μ s t = ⊥ ↔ μ[t | s] = 0 ∧ μ[t | sᶜ] ≠ 0 := by
  rw [← EReal.neg_eq_top_iff, ← weightOfEvidence_compl, weightOfEvidence_eq_top_iff, compl_compl,
    and_comm]

theorem weightOfEvidence_lt_top (h : μ[t | sᶜ] ≠ 0) : weightOfEvidence μ s t < ⊤ :=
  lt_top_iff_ne_top.2 fun h' ↦ h (weightOfEvidence_eq_top_iff.1 h').2

/-- A finite weight of evidence is the real logarithm of the ratio of the two conditional
probabilities. -/
theorem weightOfEvidence_eq_coe_log (h : μ[t | s] ≠ 0) (h' : μ[t | sᶜ] ≠ 0) :
    weightOfEvidence μ s t = (Real.log (μ[|s].real t / μ[|sᶜ].real t) : ℝ) := by
  rw [weightOfEvidence_of_ne_zero (.inl h),
    ENNReal.log_pos_real (ENNReal.div_ne_zero.2 ⟨h, measure_ne_top _ _⟩)
      (ENNReal.div_ne_top (measure_ne_top _ _) h'),
    ENNReal.toReal_div, measureReal_def, measureReal_def]

/-- A weight of evidence whose ratio of real conditional probabilities is positive is the
logarithm of that ratio. -/
theorem weightOfEvidence_eq_coe_log_of_pos (h : 0 < μ[|s].real t / μ[|sᶜ].real t) :
    weightOfEvidence μ s t = (Real.log (μ[|s].real t / μ[|sᶜ].real t) : ℝ) := by
  have hne {u : Set Ω} (hu : μ[|u].real t ≠ 0) : μ[t | u] ≠ 0 := fun h₀ ↦
    hu (by rw [measureReal_def, h₀, ENNReal.toReal_zero])
  rcases (div_pos_iff.1 h) with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
  · exact weightOfEvidence_eq_coe_log (hne h₁.ne') (hne h₂.ne')
  · exact absurd h₁ measureReal_nonneg.not_gt

/-- The weight of evidence is positive exactly when the real conditional probability given `s`
exceeds the one given `sᶜ`. -/
theorem weightOfEvidence_pos_iff_real :
    0 < weightOfEvidence μ s t ↔ μ[|sᶜ].real t < μ[|s].real t := by
  rw [weightOfEvidence_pos_iff, measureReal_def, measureReal_def,
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)]

/-- Between events each possible given `s` or given `sᶜ`, weights of evidence compare as the
likelihood ratios do. -/
theorem weightOfEvidence_lt_weightOfEvidence_iff {u : Set Ω}
    (ht : μ[t | s] ≠ 0 ∨ μ[t | sᶜ] ≠ 0) (hu : μ[u | s] ≠ 0 ∨ μ[u | sᶜ] ≠ 0) :
    weightOfEvidence μ s t < weightOfEvidence μ s u ↔
      μ[t | s] / μ[t | sᶜ] < μ[u | s] / μ[u | sᶜ] := by
  rw [weightOfEvidence_of_ne_zero ht, weightOfEvidence_of_ne_zero hu, ENNReal.log_lt_log_iff]

/-- Between events possible given `sᶜ`, weights of evidence compare as the ratios of the real
conditional probabilities do. -/
theorem weightOfEvidence_lt_weightOfEvidence_iff_real {u : Set Ω} (ht : μ[|sᶜ].real t ≠ 0)
    (hu : μ[|sᶜ].real u ≠ 0) :
    weightOfEvidence μ s t < weightOfEvidence μ s u ↔
      μ[|s].real t / μ[|sᶜ].real t < μ[|s].real u / μ[|sᶜ].real u := by
  have hne {v : Set Ω} (hv : μ[|sᶜ].real v ≠ 0) : μ[v | sᶜ] ≠ 0 := fun h₀ ↦
    hv (by rw [measureReal_def, h₀, ENNReal.toReal_zero])
  rw [weightOfEvidence_lt_weightOfEvidence_iff (.inr (hne ht)) (.inr (hne hu)),
    ← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (measure_ne_top _ _) (hne ht))
      (ENNReal.div_ne_top (measure_ne_top _ _) (hne hu)),
    ENNReal.toReal_div, ENNReal.toReal_div, measureReal_def, measureReal_def, measureReal_def,
    measureReal_def]

/-- The sign of the weight of evidence is the sign of the difference of the two conditional
probabilities. -/
theorem sign_weightOfEvidence :
    SignType.sign (weightOfEvidence μ s t) =
      SignType.sign (μ[|s].real t - μ[|sᶜ].real t) := by
  have hlt (u v : Set Ω) : μ[|u].real t < μ[|v].real t ↔ μ[t | u] < μ[t | v] :=
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)
  rcases lt_trichotomy (μ[t | sᶜ]) (μ[t | s]) with h | h | h
  · rw [sign_pos (weightOfEvidence_pos_iff.2 h), sign_pos (sub_pos.2 ((hlt _ _).2 h))]
  · rw [weightOfEvidence_eq_zero_iff.2 h.symm, measureReal_def, measureReal_def, h, sub_self,
      sign_zero, sign_zero]
  · rw [sign_neg (weightOfEvidence_neg_iff.2 h), sign_neg (sub_neg.2 ((hlt _ _).2 h))]

/-- A possible event that entails `s` has positive weight of evidence for it. -/
theorem weightOfEvidence_pos_of_subset [IsFiniteMeasure μ] (hs : MeasurableSet s) (h : t ⊆ s)
    (hct : μ t ≠ 0) : 0 < weightOfEvidence μ s t := by
  rw [weightOfEvidence_pos_iff, cond_apply hs.compl,
    (disjoint_compl_left_iff_subset.2 h).inter_eq, measure_empty, mul_zero]
  exact cond_pos_of_inter_ne_zero hs (by rwa [inter_eq_right.2 h])

/-- A possible event that entails `sᶜ` has negative weight of evidence for `s`. -/
theorem weightOfEvidence_neg_of_subset_compl [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (h : t ⊆ sᶜ) (hct : μ t ≠ 0) : weightOfEvidence μ s t < 0 := by
  rw [weightOfEvidence_neg_iff, cond_apply hs,
    (subset_compl_iff_disjoint_left.1 h).inter_eq, measure_empty, mul_zero]
  exact cond_pos_of_inter_ne_zero hs.compl (by rwa [inter_eq_right.2 h])

/-- The weight of evidence is additive over events that are independent given `s` and given
`sᶜ` and whose intersection is possible. -/
theorem weightOfEvidence_inter [IsFiniteMeasure μ] (h : IndepSet a b μ[|s])
    (h' : IndepSet a b μ[|sᶜ]) (hab : μ (a ∩ b) ≠ 0) :
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
    (ht : MeasurableSet t) (hcs : μ s ≠ 0) (hcsc : μ sᶜ ≠ 0) :
    weightOfEvidence μ s t = 0 ↔ IndepSet s t μ :=
  weightOfEvidence_eq_zero_iff.trans (cond_eq_cond_compl_iff_indepSet hs ht hcs hcsc)

/-! ### The counting measure -/

/-- Under the counting measure on a finite type the sign of the weight of evidence compares
cross-products of counts. -/
theorem sign_weightOfEvidence_count [Finite Ω] [MeasurableSingletonClass Ω] (hs : s.Nonempty)
    (hs' : sᶜ.Nonempty) (t : Set Ω) :
    SignType.sign (weightOfEvidence .count s t) =
      SignType.sign ((s ∩ t).ncard * sᶜ.ncard - (sᶜ ∩ t).ncard * s.ncard : ℤ) := by
  have h₁ : (0 : ℝ) < s.ncard := by exact_mod_cast (ncard_pos s.toFinite).2 hs
  have h₂ : (0 : ℝ) < sᶜ.ncard := by exact_mod_cast (ncard_pos sᶜ.toFinite).2 hs'
  rw [sign_weightOfEvidence,
    show (Measure.count[|s]).real t = _ from uniformOn_real_apply s t,
    show (Measure.count[|sᶜ]).real t = _ from uniformOn_real_apply sᶜ t,
    div_sub_div _ _ h₁.ne' h₂.ne', div_eq_mul_inv, sign_mul,
    sign_pos (inv_pos.2 (mul_pos h₁ h₂)), mul_one, ← sign_intCast (α := ℝ)]
  push_cast
  ring_nf

end ProbabilityTheory
