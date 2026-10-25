module

public import Linglib.Syntax.Clause.Basic

/-!
# German word order

This file records where the finite verb of German moves to the left periphery, as a
distribution over sentence types and embedding contexts. German is verb second in root
declaratives, wh-questions and yes/no-questions, and in an embedded declarative without a
complementizer, *Sie sagte, sie würde kommen*, where the verb fills the position the
complementizer *dass* otherwise occupies; with the complementizer the clause is verb final, as
are embedded questions. The yes/no-question setting records verb fronting that surfaces as V1,
with an empty specifier. Exclamatives and imperatives are not verb second. A subordinate form
used as a root utterance keeps the verb last: the *dass*-clause in isolation that Durrell
records as a command, wish or exclamation, and the deliberative *ob*- or wh-question of
Gutzmann's minimal pairs.

## References

* [westergaard-2009]
* [durrell-2011]
* [gutzmann-2015]
-/

@[expose] public section

namespace German

open Clause

/-- German has obligatory verb second in the three root clause types and in a
complementizer-less embedded declarative, none in a subordinate form used as a root utterance,
and none elsewhere. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .excluded
  | .imperative, .matrix => some .excluded
  | .declarative, .quasiSubordinated => some .obligatory
  | .declarative, .subordinated => some .excluded
  | .polar, .subordinated => some .excluded
  | .constituent, .subordinated => some .excluded
  | .declarative, .insubordinated => some .excluded
  | .polar, .insubordinated => some .excluded
  | .constituent, .insubordinated => some .excluded
  | _, _ => none

end German
