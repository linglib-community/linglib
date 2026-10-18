module

public import Linglib.Syntax.Category.Coordinator

/-!
# Yakut coordinators

Yakut coordinates clauses and the constituents of phrases with the free word *uonna* 'and', as
Stachowski and Menz describe it (p. 432). Two noun phrases are also coordinated by the comitative
suffix *-LĪn* on the second: with a plural verb the pair reads 'a Yakut and a Russian came', with
a singular verb the comitative proper 'my grandmother came with children', and the suffix can
mark every member of a collective, 'crows and ducks and geese' (p. 429).

## Main definitions

* `Yakut.Coordination.uonna`, `Yakut.Coordination.lin`: the conjunctive coordinators.

## References

* [stachowski-menz-1998]
-/

@[expose] public section

namespace Yakut.Coordination

/-- *uonna* 'and', between clauses and between the constituents of phrases. -/
def uonna : Coordinator :=
  { morph := .free "uonna", gloss := "and", role := .conjunctive }

/-- *-LĪn* 'and', on the second coordinand, with a plural verb; also the comitative of
`Yakut.Case.com`. -/
def lin : Coordinator :=
  { morph := .suff "LĪn", gloss := "and", role := .conjunctive }

end Yakut.Coordination
