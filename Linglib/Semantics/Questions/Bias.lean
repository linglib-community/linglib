module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Prod
public import Linglib.Semantics.Negation.Polarity

/-!
# Polar question bias

A polar question can be biased toward one of its answers. Two kinds of information bear on this: the
evidence available in the context, and what the speaker believed beforehand. Each of them supports
the prejacent `p`, supports `¬p`, or supports neither. We record this as a sign, `1`, `-1` or `0`.

Following [sudo-2013], a bias value is a set of such signs, the ones that a question form is
compatible with. A `BiasProfile` gives one bias value for the evidence and one for the prior belief.
Its `felicity` is the set of situations in which the form can be used.

## Main definitions

* `Question.BiasValue.plus`, `Question.BiasValue.minus`, `Question.BiasValue.neutral`: the values
  [+s], [−s] and [neutral].
* `Question.BiasProfile`: an evidential and an epistemic bias value.
* `Question.BiasProfile.felicity`: the situations a profile admits.

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

end Question
