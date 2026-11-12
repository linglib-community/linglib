module

public import Linglib.Core.Analysis.SpecialFunctions.SoftmaxCharacterization
public import Linglib.Pragmatics.RSA.Basic

/-!
# Conditions that determine the speaker

The speaker of the Rational Speech Act model soft-maximizes her utility. That decision rule is the
only one, up to the rationality, under which the odds of two utterances depend on their utilities
alone, through the difference, and rise with it: a rule with that property [produces as the speaker
does](##RSA.exists_speaker_real_singleton_eq) at some rationality, against every listener who rules
out no state the speaker entertains.

## TODO

* A listener who rules out a state the speaker entertains gives an utterance utility `⊥`, outside
  the real-valued rules treated here. [luce-1959]'s choice axiom covers alternatives that are never
  chosen by deleting them.
* The utility itself, the listener's log-probability of the state, is the only local proper score
  for the listener, by a theorem of Bernardo that is not formalized here.

## References

* [luce-1959]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RSA

variable {W U O : Type*} [MeasurableSpace W] [Fintype W] [MeasurableSpace U] [Fintype U]
  [MeasurableSingletonClass U] [MeasurableSpace O] [Countable O] [MeasurableSingletonClass O]

/-- A decision rule under which the odds of two utterances depend on the utilities only through
the difference of the two, and rise with it, is the speaker at some rationality: with at least
three utterances, it gives each utterance the probability the speaker does, whatever the cost, the
beliefs and the listener, so long as the listener rules out no state the speaker entertains. -/
theorem exists_speaker_real_singleton_eq (hU : 2 < Fintype.card U) {ρ : (U → ℝ) → U → ℝ}
    {F : ℝ → ℝ} (hpos : ∀ s u, 0 < ρ s u) (hsum : ∀ s, ∑ u, ρ s u = 1) (hF : Monotone F)
    (h : ∀ s u u', ρ s u / ρ s u' = F (s u - s u')) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (C : U → ℝ) (L : U → Measure W) [∀ u, IsFiniteMeasure (L u)]
      (b : O → Measure W), (∀ o u, b o ≪ L u) → ∀ o u, (speaker α C L b o).real {u} =
        ρ (fun u ↦ ∑ w, (b o).real {w} * Real.log ((L u).real {w}) - C u) u := by
  obtain ⟨α, hα, hρ⟩ := Real.exists_eq_softmax_of_div_eq hU hpos hsum hF h
  refine ⟨α, hα, fun C L _ b hb o u ↦ ?_⟩
  rw [speaker_eq_softmax_sum_log hb, Kernel.softmax_coe_real_singleton, hρ]
  rfl

end RSA
