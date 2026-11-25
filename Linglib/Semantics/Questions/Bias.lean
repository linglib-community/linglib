module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Prod
public import Linglib.Discourse.Bias

/-!
# Polar question bias

A polar question can be biased toward one of its answers. Two bodies of information in the
context bear on this: the evidence available, and what the speaker believed beforehand. Each has
a bias on the prejacent `p`, the sign `Filter.bias` of `Discourse/Bias.lean`, and a situation is
the pair of the two.

Following [sudo-2013], a bias value is a set of signs, the ones that a question form is
compatible with: the value [+s] holds of a consistent body of information when it supports the
`s` proposition, and [−s] when it does not. A `BiasProfile` gives one bias value for the evidence
and one for the prior belief, and its `felicity` is the set of situations in which the form can
be used.

## Main definitions

* `Question.BiasValue.plus`, `Question.BiasValue.minus`, `Question.BiasValue.neutral`: the values
  [+s], [−s] and [neutral].
* `Question.BiasProfile`: an evidential and an epistemic bias value.
* `Question.BiasProfile.felicity`: the situations a profile admits.

## Main results

* `Question.bias_mem_plus_iff`, `Question.bias_mem_minus_iff`: the values [+s] and [−s] hold of a
  consistent body when it supports, or does not support, the `s` proposition.

## References

* [buring-gunlogson-2000]
* [ladd-1981]
* [romero-han-2004]
* [sudo-2013]
-/

@[expose] public section

namespace Question

/-- A situation: the states of the contextual evidence and of the speaker's prior belief. -/
abbrev Situation := SignType × SignType

/-- A bias value ([sudo-2013]): the states of a body of information, the sign of the prejacent
it supports, that a question is compatible with. -/
abbrev BiasValue := Finset SignType

namespace BiasValue

/-- The value [+s] admits only a body of information supporting the `s` proposition. -/
def plus (s : Polarity) : BiasValue := {(s : SignType)}

/-- The value [−s] admits any body of information not supporting the `s` proposition. -/
def minus (s : Polarity) : BiasValue := (plus s)ᶜ

/-- The value [neutral] admits only a body of information supporting neither. -/
def neutral : BiasValue := {0}

variable {s : Polarity} {x : SignType}

@[simp] theorem mem_plus : x ∈ plus s ↔ x = s := Finset.mem_singleton

@[simp] theorem mem_minus : x ∈ minus s ↔ x ≠ s := by simp [minus]

@[simp] theorem mem_neutral : x ∈ neutral ↔ x = 0 := Finset.mem_singleton

@[simp] theorem compl_minus (s : Polarity) : (minus s)ᶜ = plus s := compl_compl _

end BiasValue

/-- A bias profile, the contextual evidence and the prior beliefs of the speaker a question is
compatible with. -/
structure BiasProfile where
  /-- The contextual evidence the question is compatible with. -/
  evidential : BiasValue
  /-- The prior beliefs of the speaker the question is compatible with. -/
  epistemic : BiasValue
  deriving DecidableEq

/-- The situations a profile admits, as pairs of contextual evidence and prior belief. -/
def BiasProfile.felicity (b : BiasProfile) : Finset Situation :=
  b.evidential ×ˢ b.epistemic

@[simp]
theorem BiasProfile.mem_felicity {b : BiasProfile} {s : Situation} :
    s ∈ b.felicity ↔ s.1 ∈ b.evidential ∧ s.2 ∈ b.epistemic :=
  Finset.mem_product

/-! ### Bias values of a body of information -/

section Bias

variable {W : Type*} {F : Filter W} [F.NeBot] {p : Set W}

/-- The value [+s] holds of a consistent body of information that supports the `s`
proposition. -/
theorem bias_mem_plus_iff (s : Polarity) : F.bias p ∈ BiasValue.plus s ↔ s • p ∈ F := by
  cases s
  · simp [Filter.bias_eq_one_iff]
  · simpa using Filter.bias_eq_neg_one_iff

/-- The value [−s] holds of a consistent body of information that does not support the `s`
proposition. -/
theorem bias_mem_minus_iff (s : Polarity) : F.bias p ∈ BiasValue.minus s ↔ s • p ∉ F := by
  rw [BiasValue.mem_minus, Ne, ← BiasValue.mem_plus, bias_mem_plus_iff]

end Bias

end Question
