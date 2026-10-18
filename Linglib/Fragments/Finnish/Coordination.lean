module

public import Linglib.Syntax.Category.Coordinator

/-!
# Finnish coordinators

Finnish coordinates with free words that stand before the second coordinand. Conjunction is
*ja* 'and', with the emphatic *sekä … että* 'both … and', neither member of which is the plain
coordinator. Disjunction distinguishes standard *tai* 'or', with the emphatic *joko … tai*
'either … or', from interrogative *vai*, which asks the hearer to choose between the
alternatives.

## Main definitions

* `Finnish.Coordination.ja`: the conjunctive coordinator.
* `Finnish.Coordination.tai`, `Finnish.Coordination.vai`: the standard and the interrogative
  disjunctive coordinator.
* `Finnish.Coordination.sekaEtta`, `Finnish.Coordination.jokoTai`: the emphatic constructions.

## References

* [haspelmath-2007]
-/

@[expose] public section

namespace Finnish.Coordination

/-- *ja* 'and'. -/
def ja : Coordinator :=
  { morph := .free "ja", gloss := "and", role := .conjunctive }

/-- *tai* 'or'. -/
def tai : Coordinator :=
  { morph := .free "tai", gloss := "or", role := .disjunctive }

/-- *vai* 'or' of alternative questions. -/
def vai : Coordinator :=
  { morph := .free "vai", gloss := "or", role := .disjunctive }

/-- *sekä … että* 'both … and'. -/
def sekaEtta : Coordinator.Correlative := ⟨[.free "sekä"], [.free "että"], ja⟩

/-- *joko … tai* 'either … or'. -/
def jokoTai : Coordinator.Correlative := ⟨[.free "joko"], [tai.morph], tai⟩

end Finnish.Coordination
