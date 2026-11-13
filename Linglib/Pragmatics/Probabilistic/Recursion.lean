module

public import Linglib.Pragmatics.Probabilistic.Basic

/-!
# The recursion

A speaker at recursion level `n` addresses the listener at level `n - 1`, and the listener at level
`n` addresses the speaker at level `n`, grounding out in a listener at level `0`. A level is
therefore an iterate of one map, [`RSA.recurse`](##RSA.recurse), which replaces a listener by the
listener of the speaker who addresses her. Along the iterates [utterances read alike stay
alike](##RSA.iterate_recurse_apply_eq_of_apply_eq), whatever their costs.
When the speaker knows the state, a listener keeps [exactly the states the listener she started
from allows](##RSA.iterate_recurse_id_dirac_apply_singleton_ne_zero_iff), so that [no finite level
excludes a state where an utterance is
true](##RSA.iterate_recurse_listener_truthful_apply_singleton_ne_zero_iff): the recursion sharpens
preferences among those states without making any of them impossible.

## References

* [bergen-levy-goodman-2016]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U O : Type*} [MeasurableSpace W] [Fintype W] [MeasurableSpace U] [Fintype U]
  [MeasurableSingletonClass U] [MeasurableSpace O] [Countable O] [MeasurableSingletonClass O]

/-- One level of recursion replaces a listener by the listener of the speaker who addresses her.
The speaker observes the state through `κ`, believes `b o` at an observation `o`, and has
rationality `α` and cost `C`; the listener holds the prior `μ`. -/
noncomputable def recurse (μ : Measure W) (κ : Kernel W O) (b : O → Measure W) (α : ℝ) (C : U → ℝ)
    (L : Kernel U W) : Kernel U W :=
  listener μ (speaker α C L b ∘ₖ κ)

variable {μ : Measure W} {κ : Kernel W O} {b : O → Measure W} {α : ℝ} {C : U → ℝ} {L : Kernel U W}
  {u u' : U} {w : W}

instance (μ : Measure W) (κ : Kernel W O) (b : O → Measure W) (α : ℝ) (C : U → ℝ) (L : Kernel U W) :
    IsFiniteKernel (recurse μ κ b α C L) :=
  inferInstanceAs (IsFiniteKernel (listener _ _))

instance (μ : Measure W) (κ : Kernel W O) (b : O → Measure W) (α : ℝ) (C : U → ℝ) (L : Kernel U W)
    (u : U) : IsZeroOrProbabilityMeasure (recurse μ κ b α C L u) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (listener _ _ u))

instance (μ : Measure W) (κ : Kernel W O) (b : O → Measure W) (α : ℝ) (C : U → ℝ) (L : Kernel U W)
    [IsFiniteKernel L] (n : ℕ) : IsFiniteKernel ((recurse μ κ b α C)^[n] L) := by
  cases n with
  | zero => assumption
  | succ n =>
    rw [Function.iterate_succ_apply']
    infer_instance

instance (μ : Measure W) (κ : Kernel W O) (b : O → Measure W) (α : ℝ) (C : U → ℝ) (L : Kernel U W)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] (n : ℕ) (u : U) :
    IsZeroOrProbabilityMeasure ((recurse μ κ b α C)^[n] L u) := by
  cases n with
  | zero => exact inferInstanceAs (IsZeroOrProbabilityMeasure (L u))
  | succ n =>
    rw [Function.iterate_succ_apply']
    infer_instance

/-- **Synonyms stay synonyms.** Two utterances that a listener interprets alike are interpreted
alike one level up, whatever their costs, the speaker's beliefs and the prior: the speaker weighs
them by their costs alone, a constant factor that the listener's normalization cancels. -/
theorem recurse_apply_eq_of_apply_eq (h : L u = L u') :
    recurse μ κ b α C L u' = recurse μ κ b α C L u :=
  listener_apply_eq_of_apply_singleton_eq_mul (c := ENNReal.ofReal (Real.exp (α * (C u - C u'))))
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top fun w ↦ by
      rw [Kernel.comp_apply' _ _ _ (.singleton u'), Kernel.comp_apply' _ _ _ (.singleton u),
        ← lintegral_const_mul _ (Kernel.measurable_coe _ (.singleton u))]
      exact lintegral_congr fun o ↦ speaker_apply_singleton_eq_mul_of_apply_eq h

/-- [bergen-levy-goodman-2016]'s Lemma 2: utterances a listener interprets alike are interpreted
alike at every level of the recursion. -/
theorem iterate_recurse_apply_eq_of_apply_eq (h : L u = L u') (n : ℕ) :
    (recurse μ κ b α C)^[n] L u' = (recurse μ κ b α C)^[n] L u := by
  induction n with
  | zero => exact h.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact recurse_apply_eq_of_apply_eq ih.symm

/-- When the speaker knows the state, one level of recursion is the listener of the speaker who
addresses `L`. -/
theorem recurse_id_dirac [MeasurableSingletonClass W] (μ : Measure W) (α : ℝ) (C : U → ℝ)
    (L : Kernel U W) :
    recurse μ Kernel.id Measure.dirac α C L = listener μ (speaker α C L Measure.dirac) := by
  rw [recurse, Kernel.comp_id]

section Support

variable [MeasurableSingletonClass W]

/-- A state the listener rules out stays ruled out, when the speaker entertains every state of
positive prior that could have given her observation. -/
theorem recurse_apply_singleton_eq_zero [Fintype O] [∀ u, IsFiniteMeasure (L u)]
    [∀ o, IsFiniteMeasure (b o)] (hα : 0 < α)
    (hb : ∀ o, μ {w} ≠ 0 → κ w {o} ≠ 0 → b o {w} ≠ 0) (h : L u {w} = 0) :
    recurse μ κ b α C L u {w} = 0 := by
  by_contra hne
  obtain ⟨hμ, hS⟩ := ne_zero_of_listener_apply_singleton_ne_zero hne
  rw [Kernel.comp_apply_singleton] at hS
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  exact right_ne_zero_of_mul ho ((speaker_apply_singleton_eq_zero_iff hα).2
    ⟨w, hb o hμ (left_ne_zero_of_mul ho), h⟩)

theorem iterate_recurse_id_dirac_apply_singleton_eq_zero (hα : 0 < α) (h : L u {w} = 0) (n : ℕ) :
    (recurse μ Kernel.id Measure.dirac α C)^[n] L u {w} = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', recurse_id_dirac]
    exact listener_apply_singleton_eq_zero (speaker_dirac_apply_singleton_eq_zero hα ih)

variable [IsFiniteMeasure μ]

theorem iterate_recurse_id_dirac_apply_singleton_ne_zero [IsFiniteKernel L] (hα : 0 ≤ α)
    (hμ : μ {w} ≠ 0) (h : L u {w} ≠ 0) (n : ℕ) :
    (recurse μ Kernel.id Measure.dirac α C)^[n] L u {w} ≠ 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', recurse_id_dirac]
    exact listener_apply_singleton_ne_zero hμ (speaker_dirac_apply_singleton_ne_zero hα ih)

/-- When the speaker knows the state, a listener at any level takes a state to be possible exactly
when the listener she started from does. -/
theorem iterate_recurse_id_dirac_apply_singleton_ne_zero_iff [IsFiniteKernel L] (hα : 0 < α)
    (hL : ∀ u w, L u {w} ≠ 0 → μ {w} ≠ 0) (n : ℕ) :
    (recurse μ Kernel.id Measure.dirac α C)^[n] L u {w} ≠ 0 ↔ L u {w} ≠ 0 :=
  ⟨mt fun h ↦ iterate_recurse_id_dirac_apply_singleton_eq_zero hα h n,
    fun h ↦ iterate_recurse_id_dirac_apply_singleton_ne_zero hα.le (hL u w h) h n⟩

/-- When the speaker knows the state and the recursion starts from the literal listener, no level
excludes a state of positive prior where the utterance is true, or admits any other. -/
theorem iterate_recurse_listener_truthful_apply_singleton_ne_zero_iff {sem : U → Set W} (hα : 0 < α)
    (n : ℕ) :
    (recurse μ Kernel.id Measure.dirac α C)^[n] (listener μ (truthful sem)) u {w} ≠ 0 ↔
      w ∈ sem u ∧ μ {w} ≠ 0 := by
  rw [iterate_recurse_id_dirac_apply_singleton_ne_zero_iff hα fun u w h ↦
    ((listener_truthful_apply_singleton_ne_zero_iff μ sem u w).1 h).2,
    listener_truthful_apply_singleton_ne_zero_iff]

end Support

end RSA
