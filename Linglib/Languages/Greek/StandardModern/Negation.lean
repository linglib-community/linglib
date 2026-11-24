module

public import Linglib.Syntax.Negation
public import Linglib.Syntax.Clause.Complementation

/-!
# Greek negation

Standard Modern Greek forms sentence negation differently in the indicative and the subjunctive.
*dhen* (δεν) negates an indicative clause, standing before the verb and its particles. *min* (μην)
negates a subjunctive clause, standing after the subjunctive marker *na* or *as*, and *na* may be
left out, as in *Min tu dhosis ala lefta* 'Do not give him any more money'. A verb in the
imperative cannot be negated, so a prohibition is a negative subjunctive. The analysis of the two
as standard and modal negation, and of their non-negative uses, is [tsiakmakis-2025]'s and lives
in that study.

## References

* [holton-mackridge-philippaki-warburton-spyropoulos-2012]
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

/-- *min* (μην), the negator of subjunctive clauses, among them prohibitions. -/
def min : Negator := { marker := { pieces := [[.free "min"]] }, mood := .subjunctive }

/-- The sentential negators. -/
def negators : List Negator := [dhen, min]

/-- The standard negators. -/
def standard : List Marker := [dhen.marker]

end Greek.StandardModern.Negation
