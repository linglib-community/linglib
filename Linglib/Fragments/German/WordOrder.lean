module

public import Linglib.Syntax.Clause.Basic

/-!
# German word order

This file records where the finite verb of German moves to the left periphery, as
distributions over sentence types and embedding contexts. German is verb second in root
declaratives, wh-questions and yes/no-questions; the yes/no-question setting records verb
fronting that surfaces as V1, with an empty specifier. Exclamatives and imperatives are not verb
second. Embedded verb second is limited by the matrix verb: the complement of a bridge verb such
as *behaupten* 'claim' or *sagen* 'say' may be verb second, while that of *beweisen* 'prove' or
*bedauern* 'regret' is verb final, as are embedded questions. Within a bridge complement verb
second and the complementizer *dass* exclude each other, and one of them must be present: the
clause is verb second exactly when it has no complementizer, *Sie sagte, sie würde kommen* beside
*Sie sagte, daß sie kommen würde*. Verb second is therefore optional in the complement of a
bridge verb and required in one without a complementizer. A subordinate form used as a root
utterance keeps the verb last: the *dass*-clause in isolation that Durrell records as a command,
wish or exclamation, and the deliberative *ob*- or wh-question of Gutzmann's minimal pairs.

## Implementation notes

The comments locate the embedded cells: V cites Vikner by numbered example or page, W cites the
second chapter of Westergaard by example.

## References

* [westergaard-2009]
* [vikner-1995]
* [durrell-2011]
* [gutzmann-2015]
-/

@[expose] public section

namespace German

open Clause

/-- German requires verb second in the three root clause types and allows it in the complement
of a bridge verb; it excludes it in exclamatives, imperatives, embedded questions, other
subordinate declaratives, and a subordinate form used as a root utterance. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .excluded
  | .imperative, .matrix => some .excluded
  | .declarative, .quasiSubordinated => some .optional  -- V (13b), (14b), list (17); W (17)
  | .declarative, .subordinated => some .excluded  -- V (15b), (16b), list (18)
  | .polar, .subordinated => some .excluded  -- V p. 84
  | .constituent, .subordinated => some .excluded  -- V p. 84
  | .declarative, .insubordinated => some .excluded
  | .polar, .insubordinated => some .excluded
  | .constituent, .insubordinated => some .excluded
  | _, _ => none

/-- Without *dass* the complement of a bridge verb must be verb second,
*Sie sagte, sie würde kommen* against **Sie sagte, sie kommen würde*. -/
def verbSecondWithoutComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .obligatory  -- W (17b); V (52)
  | _, _ => none

end German
