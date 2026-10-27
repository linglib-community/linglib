module

public import Linglib.Syntax.Clause.Basic

/-!
# German word order

German is a verb-second language in main clauses: the finite verb follows exactly one constituent
in a declarative or a wh-question, *Die Kinder haben diesen Film gesehen* 'The children have seen
this film', *Was haben die Kinder gesehen?* 'What have the children seen?', and comes first in a
yes/no-question. In a subordinate clause it comes last, *Er sagt, daß die Kinder diesen Film
gesehen haben* 'He says that the children have seen this film'. Exclamatives and imperatives are
not verb second.

Verb second in a subordinate clause depends on the matrix verb: the complement of a *bridge verb*
such as *behaupten* 'claim' or *sagen* 'say' may be verb second, that of *beweisen* 'prove' or
*bedauern* 'regret' may not, and embedded questions never are. In a bridge complement verb second
and the complementizer *dass* exclude each other, and one of them must be present, so the clause is
verb second exactly when it lacks a complementizer: *Sie sagte, sie würde kommen* beside *Sie
sagte, daß sie kommen würde* 'She said (that) she would come'.

A subordinate form used as a root utterance keeps the verb last: the *dass*-clause in isolation,
which Durrell records as a command, wish or exclamation, and the deliberative *ob*- or wh-question
of Gutzmann's minimal pairs.

## Implementation notes

Verb second is a `Clause.Distribution` over sentence types and embedding contexts. The complement
of a bridge verb is the quasi-subordinated context, whose cell combines the clauses with and
without *dass*, and a subordinate form used as a root utterance is insubordinated. The
yes/no-question cell records verb fronting that surfaces as V1, with an empty specifier. The
comments locate the embedded cells: V cites Vikner by numbered example or page, W cites the second
chapter of Westergaard by example.

## References

* [westergaard-2009]
* [vikner-1995]
* [durrell-2011]
* [gutzmann-2015]
-/

@[expose] public section

namespace German

open Clause

/-- Verb second in a subordinate clause introduced by *dass*: excluded after a bridge verb. -/
def verbSecondWithComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .excluded  -- W (17a); V (13b), (52b)
  | _, _ => none

/-- Verb second in a subordinate clause without a complementizer: required after a bridge verb,
*Sie sagte, sie würde kommen* against *\*Sie sagte, sie kommen würde*. -/
def verbSecondWithoutComplementizer : Distribution
  | .declarative, .quasiSubordinated => some .obligatory  -- W (17b); V (52)
  | _, _ => none

/-- Verb second in German: required in root declaratives and questions, optional after a bridge
verb, and excluded in the other clauses recorded. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .excluded
  | .imperative, .matrix => some .excluded
  | t, .quasiSubordinated =>  -- V list (17)
    verbSecondWithComplementizer.union verbSecondWithoutComplementizer t .quasiSubordinated
  | .declarative, .subordinated => some .excluded  -- V (15b), (16b), list (18)
  | .polar, .subordinated => some .excluded  -- V p. 84
  | .constituent, .subordinated => some .excluded  -- V p. 84
  | .declarative, .insubordinated => some .excluded
  | .polar, .insubordinated => some .excluded
  | .constituent, .insubordinated => some .excluded
  | _, _ => none

end German
