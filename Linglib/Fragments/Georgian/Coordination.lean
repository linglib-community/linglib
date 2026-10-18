module

public import Linglib.Syntax.Category.Coordinator

/-!
# Georgian coordinators

Georgian conjoins noun phrases with the free word *da* 'and' before the second coordinand, with
the enclitic *-c* 'also, too' on each coordinand, or with both, the enclitic on each coordinand
and *da* between them: in the examples of Bill and colleagues, *vashl-i da banan-i*,
*vashl-i-c, banan-i-c* and *vashl-i-c da banan-i-c* all mean 'the apple and the banana'.
Disjunction is *an* 'or' and the adversative coordinator is *magram* 'but', as Hewitt lists them
with *da*.

## Main definitions

* `Georgian.Coordination.da`, `Georgian.Coordination.c`: the conjunctive coordinator and the
  additive enclitic that conjoins when repeated.
* `Georgian.Coordination.an`, `Georgian.Coordination.magram`: the disjunctive and the
  adversative coordinator.

## References

* [bill-etal-2025]
* [hewitt-1995]
-/

@[expose] public section

namespace Georgian.Coordination

/-- *da* 'and'. -/
def da : Coordinator :=
  { morph := .free "da", gloss := "and", role := .conjunctive }

/-- *-c* 'and', enclitic on each coordinand, also the additive particle
`Georgian.FocusParticles.c`. -/
def c : Coordinator :=
  { morph := .encl "c", gloss := "and", role := .conjunctive }

/-- *an* 'or'. -/
def an : Coordinator :=
  { morph := .free "an", gloss := "or", role := .disjunctive }

/-- *magram* 'but'. -/
def magram : Coordinator :=
  { morph := .free "magram", gloss := "but", role := .adversative }

end Georgian.Coordination
