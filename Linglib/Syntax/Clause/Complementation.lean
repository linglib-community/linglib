module

public import Linglib.Syntax.Case.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Complement clauses

Besides the sentence types it selects (`Clause.Selection`), a clausal argument position records
three properties of its complement clause. Noonan's cross-linguistic survey of complementation
sorts complement clauses into six complement types by the part of speech of the predicate, the
relation of the subject to the predicate, and the inflectional categories the clause carries. The
subject of a complement is obligatorily null, as under control, or overt. The size of a complement
is the semantic sort it denotes, which fixes the structure it needs.

## Main definitions

* `Clause.ComplementType`: the six complement types.
* `Clause.ComplementType.IsFinite`: the complement type is a clause whose verb can agree with its
  subject.
* `Clause.ComplementType.IsSentenceLike`: the complement type is sentence-like, its predicate
  related to its arguments as in a main clause.
* `Clause.EmbeddedSubject`: the subject requirement of a complement clause.
* `Clause.Size`: the semantic size of a complement clause, ordered by containment.

## Implementation notes

A complement type is reduced when it has fewer syntactic and inflectional possibilities than an
indicative main clause. That is a fact about a language's complement types rather than about the
six labels, since the subjunctive is typically reduced but need not be, so no predicate on
`ComplementType` states it; the predicate that is a fact about the labels is
`ComplementType.IsSentenceLike`.

## References

* [noonan-2007]
* [bondarenko-2022]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
-/

@[expose] public section

namespace Clause

/-! ### Complement types -/

/-- The six complement types of [noonan-2007]'s survey, in the order of its summary table. -/
inductive ComplementType where
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

namespace ComplementType

/-- The finite complement types are the indicative, the subjunctive and the paratactic, whose verb
can agree with its subject as an infinitive's cannot. -/
def IsFinite : ComplementType → Prop
  | indicative | subjunctive | paratactic => True
  | infinitive | nominalized | participle => False

instance : DecidablePred IsFinite := fun c ↦ by cases c <;> unfold IsFinite <;> infer_instance

/-- A complement type is sentence-like when its predicate stands in the relation to its subject
and other arguments that it has in a main clause ([noonan-2007] §1.3.1), as in the indicative and
the subjunctive. A paratactic clause is fully inflected but does not form a constituent with its
subject. -/
def IsSentenceLike : ComplementType → Prop
  | indicative | subjunctive => True
  | paratactic | infinitive | nominalized | participle => False

instance : DecidablePred IsSentenceLike := fun c ↦ by
  cases c <;> unfold IsSentenceLike <;> infer_instance

end ComplementType

/-! ### Subject and size -/

/-- The subject of an embedded clause is obligatorily null, as in control complements, or
overt, optionally with a fixed case. Genitive marking on the subject is [noonan-2007]'s criterion
for the nominalized complement type, and the genitive subjects of Buryat nominalized clauses are
a modern instance ([bondarenko-2022]). -/
inductive EmbeddedSubject where
  | obligatorilyNull
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr

/-- The semantic sort of a complement clause, which fixes the minimal structure it needs in
[wurmbrand-lohninger-2023]'s implicational complementation hierarchy. An event needs only the
thematic domain, a situation adds the tense–mood–aspect domain, and a proposition adds the
operator domain. Ordered by containment. -/
inductive Size where
  | event
  | situation
  | proposition
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder Size := .lift' Size.ctorIdx (by decide)

end Clause
