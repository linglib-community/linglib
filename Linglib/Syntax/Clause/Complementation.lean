module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Complement codings

Noonan's cross-linguistic survey of complementation sorts complement clauses into six types by
the part of speech of the predicate, the relation of the subject to the predicate, and the
inflectional categories the clause carries (`Complement.Coding`). An argument frame records the
coding of its clausal position (`ArgumentFrame.Position.clausal`), and a complementizer the coding
of the clause it introduces (`Complementizer.coding`).

## Main definitions

* `Complement.Coding`: the six complement types.
* `Complement.Coding.IsFinite`: the coding is a clause whose verb can agree with its subject.
* `Complement.Coding.IsSLike`: the coding is sentence-like, its predicate related to its
  arguments as in a main clause.

## Implementation notes

A complement type is reduced when it has fewer syntactic and inflectional possibilities than an
indicative main clause. That is a fact about a language's complement types rather than about the
six labels, since the subjunctive is typically reduced but need not be, so no predicate on
`Coding` states it; the predicate that is a fact about the labels is `Coding.IsSLike`.

## References

* [noonan-2007]
-/

@[expose] public section

namespace Complement

/-- The six complement types of [noonan-2007]'s survey, in the order of its summary table. -/
inductive Coding where
  /-- A clause whose form is (nearly) that of a declarative main clause. -/
  | indicative
  /-- A sentence-like clause in a mood opposed to the indicative, whose inflectional range is
  typically reduced. -/
  | subjunctive
  /-- A fully inflected clause juxtaposed to the matrix as a separate assertion, neither
  subordinate nor introduced by a complementizer. -/
  | paratactic
  /-- A clause whose verb does not form a constituent with its subject or agree with it. -/
  | infinitive
  /-- A clause whose predicate is a noun, its subject related to it as a genitive. -/
  | nominalized
  /-- A clause whose predicate is an adjective or adverb modifying its subject. -/
  | participle
  deriving DecidableEq, Repr, Fintype

namespace Coding

/-- The finite codings are the indicative, the subjunctive and the paratactic, whose verb can
agree with its subject as an infinitive's cannot. -/
def IsFinite : Coding → Prop
  | indicative | subjunctive | paratactic => True
  | infinitive | nominalized | participle => False

instance : DecidablePred IsFinite := fun c ↦ by cases c <;> unfold IsFinite <;> infer_instance

/-- A coding is sentence-like when its predicate stands in the relation to its subject and other
arguments that it has in a main clause ([noonan-2007] §1.3.1), as in the indicative and the
subjunctive. A paratactic clause is fully inflected but does not form a constituent with its
subject. -/
def IsSLike : Coding → Prop
  | indicative | subjunctive => True
  | paratactic | infinitive | nominalized | participle => False

instance : DecidablePred IsSLike := fun c ↦ by cases c <;> unfold IsSLike <;> infer_instance

end Coding

end Complement
