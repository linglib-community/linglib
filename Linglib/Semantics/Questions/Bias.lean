module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Prod
public import Linglib.Semantics.Negation.Polarity

/-!
# Polar question bias

A polar question is sensitive to two bodies of information bearing on its prejacent `p`: the
contextual evidence available in the discourse, as Büring and Gunlogson put it, and the prior
belief of the speaker, the original bias of Ladd and of Romero and Han. Each supports `p`,
supports `¬p`, or neither, so its state is a sign, `1`, `-1` or `0`, and reading it relative to
`¬p` negates it. Under a prior the state is the relevance sign of the body of information for
`p` in Merin's decision-theoretic semantics, `DTS.relevanceSign`, which swapping `p` for `¬p`
negates.

A bias value in Sudo's scheme is the set of states a question is compatible with:
[+s] (`BiasValue.plus`), its complement [−s] (`BiasValue.minus`) and [neutral]. A `BiasProfile`
pairs an evidential and an epistemic value, and its `felicity` is the set of situations, pairs
of the two states (`Situation`), that it admits.
The forms and readings of polar questions are `Negation.Position` and
`Option Polarity`.

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
