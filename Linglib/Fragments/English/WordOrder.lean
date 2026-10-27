module

public import Linglib.Syntax.Clause.Basic

/-!
# English word order

English has *residual verb second*: an auxiliary precedes the subject in a main-clause wh-question,
*What will you bring to the party?*, and in a yes/no-question, *Have you seen her today?*, while
declaratives, exclamatives, imperatives and subordinate clauses keep the subject first. Belfast
English also inverts in imperatives, where a lexical verb too precedes the subject, *Bring you that
with you!*, and in an embedded yes/no-question without a complementizer, *They asked me was I going
to the party*. These are Henry's examples; Westergaard suggests that the imperative verb moves to a
lower head than the auxiliary of a question.

## Implementation notes

Verb second is a `Clause.Distribution` over sentence types and embedding contexts, the complement
of a rogative verb such as *ask* being the quasi-subordinated context. Belfast English's embedded
inversion is recorded for the clause without a complementizer only, since the sources give no
example with *if* or *whether*.

## References

* [westergaard-2009]
* [henry-1997]
-/

@[expose] public section

namespace English

open Clause

/-- Verb second in Standard English: the auxiliary precedes the subject in root wh-questions
and yes/no-questions, and in none of the other clauses recorded. -/
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

/-- Verb second in Belfast English: as in Standard English, and in imperatives as well. -/
def Belfast.verbSecond : Distribution
  | .imperative, .matrix => some .obligatory
  | t, e => English.verbSecond t e

/-- Verb second in a subordinate clause without a complementizer in Belfast English: required in
the complement of a rogative verb such as *ask*. -/
def Belfast.verbSecondWithoutComplementizer : Distribution
  | .polar, .quasiSubordinated => some .obligatory
  | _, _ => none

end English
