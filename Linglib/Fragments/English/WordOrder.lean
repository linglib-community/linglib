module

public import Linglib.Syntax.Clause.Basic

/-!
# English word order

This file records where the finite verb of Standard English and of Belfast English moves to the
left periphery, as a distribution over sentence types and embedding contexts. Standard English
moves the verb, an auxiliary, only in matrix wh-questions and yes/no-questions, the
subject–auxiliary inversion; declaratives, exclamatives, imperatives and embedded clauses are
not verb second. Belfast English adds imperatives, *Bring you that with you!*, and embedded
root-like yes/no-questions, *They asked me was I going to the party*, the examples Henry
reports; Westergaard notes that the imperative movement may target a lower head.

## References

* [westergaard-2009]
* [henry-1997]
-/

@[expose] public section

namespace English

open Clause

/-- In Standard English the auxiliary moves in root wh-questions and yes/no-questions and
nowhere else. -/
def verbSecond : Distribution
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .declarative, .matrix => some .excluded
  | .exclamative, .matrix => some .excluded
  | .imperative, .matrix => some .excluded
  | .declarative, .subordinated => some .excluded
  | .polar, .subordinated => some .excluded
  | .constituent, .subordinated => some .excluded
  | _, _ => none

/-- Belfast English is Standard English with verb movement in imperatives and in embedded
root-like yes/no-questions. -/
def Belfast.verbSecond : Distribution
  | .imperative, .matrix => some .obligatory
  | .polar, .quasiSubordinated => some .obligatory
  | t, e => English.verbSecond t e

end English
