module

public import Linglib.Languages.Japanese.Morphs
public import Linglib.Syntax.Category.Coordinator

/-!
# Japanese coordinators

Japanese coordinates noun phrases with enclitic particles: *to* 'and', on the first conjunct,
which is also the comitative marker;
*mo* 'and', on each conjunct, which is also the additive particle 'too' and the universal
particle of the indeterminate quantifiers (*dare-mo* 'everyone'); and *ka* 'or', which is also
the question particle and the existential particle of the indeterminate quantifiers (*dare-ka*
'someone'); the indeterminate quantifiers built on *mo* and *ka* are in
`Languages/Japanese/Determiners.lean`.

## Main definitions

* `Japanese.Coordination.to_`, `Japanese.Coordination.mo`, `Japanese.Coordination.ka`: the
  three particles.

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
* [stassen-2000]
-/

@[expose] public section

namespace Japanese.Coordination

/-- *to* 'and', enclitic on the first conjunct, also the comitative postposition 'with',
`Japanese.Adpositions.«to»`. -/
def to_ : Coordinator :=
  { morph := .encl "to", role := .conjunctive }

/-- *mo* 'and', enclitic on each conjunct, also the additive particle `Japanese.FocusParticles.mo`
and the universal particle of the indeterminates, `Japanese.Determiners.dareMo`. -/
def mo : Coordinator :=
  { morph := Morphs.mo, role := .conjunctive }

/-- *ka* 'or', enclitic, also the question particle and the existential particle of the
indeterminates, `Japanese.Determiners.dareKa`. -/
def ka : Coordinator :=
  { morph := Morphs.ka, role := .disjunctive }

end Japanese.Coordination
