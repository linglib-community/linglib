module

public import Linglib.Syntax.Category.Coordinator

/-!
# Yoruba coordinators

Yoruba conjoins noun phrases with the free word *àti* before the second coordinand, *èmi àti
Kẹ́hìndé* 'Kehinde and I'. Repeated before each coordinand, *àti A àti B*, it gives the emphatic
'both … and', and in a list every *àti* but the last may be deleted. Other coordinand types
conjoin with other words, *tí* for relative clauses and *sì* for main clauses, the three-way
contrast Haspelmath cites from Rowlands.

## Main definitions

* `Yoruba.Coordination.ati`, `Yoruba.Coordination.atiAti`: noun-phrase *àti* and the emphatic
  *àti … àti*.
* `Yoruba.Coordination.ti`, `Yoruba.Coordination.si`: the relative-clause and main-clause
  coordinators.

## References

* [haspelmath-2007]
* [rowlands-1969]
-/

@[expose] public section

namespace Yoruba.Coordination

/-- *àti* 'and', conjoining noun phrases; repeated for 'both … and', and in a list deleted from
every coordinand but the last. -/
def ati : Coordinator :=
  { morph := .free "àti", gloss := "and", role := .conjunctive }

/-- *tí* 'and', conjoining relative clauses: the form of the relative introducer
`Yoruba.relTi`. -/
def ti : Coordinator :=
  { morph := .free "tí", gloss := "and", role := .conjunctive }

/-- *sì* 'and', conjoining main clauses, before the verb of the second clause. -/
def si : Coordinator :=
  { morph := .free "sì", gloss := "and", role := .conjunctive }

/-- *àti … àti* 'both … and'. -/
def atiAti : Coordinator.Correlative := ⟨[ati.morph], [ati.morph], ati⟩

end Yoruba.Coordination
