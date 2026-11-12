module

public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Pragmatics.Probabilistic.Basic

/-!
# Speakers who address a question

A question under discussion is a function `q : W → X` from states to answers. In the models of
Kao and colleagues the speaker knows the answer `q w` at her state and is informative about the
answer alone: she addresses the pushforward `L.map q` of the listener's belief about the state.
Under a literal listener this pushforward gives an answer [the prior's share of the states with
that answer where the utterance is true](##listener_truthful_map_apply_singleton), so the speaker
[produces an utterance exactly when it is true at a state of positive prior with her
answer](##speaker_listener_truthful_map_dirac_apply_singleton_ne_zero_iff), whether or not it is
true at hers. A listener unsure of the question holds it as a latent coordinate of the state, as
in lexical uncertainty, and such an utterance leads her to states where it is false, which is how
the models derive hyperbole, metaphor and irony.

## References

* [kao-etal-2014-hyperbole]
* [kao-etal-2014-metaphor]
* [kao-goodman-2015]
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U X : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A literal listener's probability of an answer is the prior mass of the states with that
answer where the utterance is true, over the prior mass of the states where it is true. -/
theorem listener_truthful_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] (μ : Measure W) (sem : U → Set W) (q : W → X) (u : U) (x : X) :
    (listener μ (truthful sem)).map q u {x} = μ (sem u ∩ q ⁻¹' {x}) / μ (sem u) := by
  rw [Kernel.map_apply_singleton, listener_truthful_apply, cond_apply .of_discrete,
    ENNReal.div_eq_inv_mul]

/-- Within a finite context set, a literal listener's probability of an answer is the prior mass
of the states of the set where the utterance is true and that have the answer, over the prior
mass of the states of the set where it is true. -/
theorem listener_restrict_truthful_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] [DecidableEq X] (μ : Measure W) (C : Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (q : W → X) (u : U) (x : X) :
    (listener (μ.restrict ↑C) (truthful sem)).map q u {x} =
      μ ↑((C.filter (· ∈ sem u)).filter (q · = x)) / μ ↑(C.filter (· ∈ sem u)) := by
  rw [listener_truthful_map_apply_singleton, Measure.restrict_apply .of_discrete,
    Measure.restrict_apply .of_discrete]
  congr 2 <;> ext <;> simp [and_comm, and_left_comm]

variable [Fintype W] [Fintype U] [Fintype X] {α : ℝ}

/-- **Nonliteral production.** The speaker who addresses a question to a literal listener
produces an utterance exactly when it is true at a state of positive prior with the same answer as
hers, whether or not it is true at her own state. -/
theorem speaker_listener_truthful_map_dirac_apply_singleton_ne_zero_iff
    [DiscreteMeasurableSpace W] (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (q : W → X) (w : W) (u : U) :
    speaker α C ((listener μ (truthful sem)).map q) Measure.dirac (q w) {u} ≠ 0 ↔
      ∃ w', q w' = q w ∧ w' ∈ sem u ∧ μ {w'} ≠ 0 := by
  simp only [speaker_dirac_apply_singleton_ne_zero_iff hα, Kernel.map_apply_singleton_ne_zero_iff,
    listener_truthful_apply_singleton_ne_zero_iff]

end RSA
