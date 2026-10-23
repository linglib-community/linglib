module

public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Pragmatics.RSA.Basic

/-!
# Speakers who address a question

A question under discussion is a function `q : W → X` from states to answers. Kao and colleagues
let the speaker be informative about the answer alone: the listener's belief about the answer is
the pushforward `L.map q` of his belief about the state, and the speaker, who knows the answer
`q w` at her state, is `RSA.speaker α C (L.map q) Measure.dirac (q w)`. With the question as a
coordinate of the state, the listener who does not know which question she addresses is
`RSA.listener` over pairs of a state and a question.

An utterance that is false at a state can then be produced there, when it is true at a state with
the same answer, which is how the model derives hyperbole, metaphor and irony.

## Main results

* `RSA.listener_truthful_map_apply_singleton`: a literal listener's probability of an answer is
  the prior mass of the states with that answer where the utterance is true, over the prior mass
  of the states where it is true.
* `RSA.speaker_map_dirac_apply_singleton_ne_zero_iff`: the speaker produces an utterance exactly
  when its listener gives mass to a state with the same answer as hers.
* `RSA.listener_prod_speaker_map_dirac_fst_apply_singleton_ne_zero_iff`: the listener takes a
  state to be possible exactly when it has positive prior and, under some question of positive
  prior, shares its answer with a state the literal listener gives mass.

## References

* [kao-etal-2014-hyperbole]
* [kao-etal-2014-metaphor]
* [kao-goodman-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U X G : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace X] [MeasurableSingletonClass X]

theorem listener_truthful_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] (μ : Measure W) (sem : U → Set W) (q : W → X) (u : U) (x : X) :
    (listener μ (truthful sem)).map q u {x} = μ (sem u ∩ q ⁻¹' {x}) / μ (sem u) := by
  rw [Kernel.map_apply_singleton, listener_truthful_apply, cond_apply .of_discrete,
    ENNReal.div_eq_inv_mul]

variable [Fintype W] [MeasurableSingletonClass W] [Fintype U] [Fintype X] {α : ℝ}

theorem speaker_map_dirac_apply_singleton_ne_zero_iff (hα : 0 < α) (C : U → ℝ) (L : Kernel U W)
    [IsFiniteKernel L] (q : W → X) (w : W) (u : U) :
    speaker α C (L.map q) Measure.dirac (q w) {u} ≠ 0 ↔ ∃ w', q w' = q w ∧ L u {w'} ≠ 0 := by
  rw [speaker_dirac_apply_singleton_ne_zero_iff hα, Kernel.map_apply_singleton_ne_zero_iff]

variable [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem listener_prod_speaker_map_dirac_fst_apply_singleton_ne_zero_iff (hα : 0 < α)
    (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L] (q : G → W → X) (μ : Measure W)
    [IsFiniteMeasure μ] (ν : Measure G) [IsFiniteMeasure ν] (u : U) (w : W) :
    (listener (μ.prod ν) (fun p ↦ speaker α C (L.map (q p.2)) Measure.dirac (q p.2 p.1))
        u).fst {w} ≠ 0 ↔
      μ {w} ≠ 0 ∧ ∃ g, ν {g} ≠ 0 ∧ ∃ w', q g w' = q g w ∧ L u {w'} ≠ 0 := by
  rw [listener_fst_apply_singleton_ne_zero_iff]
  simp only [speaker_map_dirac_apply_singleton_ne_zero_iff hα, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff]
  exact ⟨fun ⟨g, ⟨hw, hg⟩, h⟩ ↦ ⟨hw, g, hg, h⟩, fun ⟨hw, g, hg, h⟩ ↦ ⟨g, ⟨hw, hg⟩, h⟩⟩

end RSA
