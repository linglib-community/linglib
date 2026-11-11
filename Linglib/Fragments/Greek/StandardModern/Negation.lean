module

public import Linglib.Syntax.Negation
public import Linglib.Syntax.Clause.Complementation

/-!
# Greek negation

Standard Modern Greek has two sentential negation markers in complementary distribution by
mood: *dhen* (δεν) negates indicative clauses, and *min* (μην) negates the subjunctive clauses of
non-veridical environments, among them the negative imperative, which Greek forms with a
subjunctive verb. The analysis of the two as standard and modal negation, and of their
non-negative uses, is [tsiakmakis-2025]'s and lives in that study.

## References

* [tsiakmakis-2025]
-/

@[expose] public section

open Negation

namespace Greek.StandardModern.Negation

/-- A Greek sentential negator is given by its exponent and the mood of the clauses it
negates. -/
structure Negator where
  /-- The exponent. -/
  marker : Marker
  /-- The mood of the clauses the negator negates. -/
  mood : Clause.ComplementType
  deriving DecidableEq, Repr

/-- *dhen* (δεν), the negator of indicative clauses. -/
def dhen : Negator := { marker := { pieces := [[.free "dhen"]] }, mood := .indicative }

/-- *min* (μην), the negator of subjunctive clauses and of the negative imperative. -/
def min : Negator := { marker := { pieces := [[.free "min"]] }, mood := .subjunctive }

/-- The sentential negators. -/
def negators : List Negator := [dhen, min]

/-- The standard negators. -/
def standard : List Marker := [dhen.marker]

end Greek.StandardModern.Negation
