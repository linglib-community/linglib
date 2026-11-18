module

public import Linglib.Core.Order.PartialUnify
public import Linglib.Core.Relation.SetRel
public import Linglib.Syntax.Obligatoriness
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Basic
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.DeriveFintype

/-!
# Sentence types and their distribution

A sentence type is the grammatical kind of a clause, such as the declarative or the polar
interrogative, and an embedding context is where a clause token occurs, as a root or under
subordination. A distribution records, for each sentence type in each embedding context, whether
some element or process is obligatory, optional or excluded there. A selection is the set of
sentence types a complementizer types or a clausal argument position selects. The other properties
of a complement clause are in `Syntax/Clause/Complementation.lean`.

## Main definitions

* `Clause.SentenceType`, `Clause.SentenceType.IsInterrogative`: the sentence types.
* `Clause.EmbeddingContext`, `Clause.root`, `Clause.embedded`: the embedding contexts and the
  cells of root and subordinated clauses.
* `Clause.Distribution`: the `Obligatoriness` recorded in each cell.
* `Clause.Distribution.recorded`, `possible`, `required`: the relations a distribution
  determines.
* `Clause.LeftEdge`, `Clause.LeftEdge.Table`: whether a complementizer introduces a clause and
  whether its finite verb is fronted, and the left edges a language admits in each cell.
* `Clause.Selection`: the sentence types a clause-typer types or a clausal position selects.

## References

* [sadock-zwicky-1985]
* [zanuttini-pak-portner-2012]
* [bhatt-dayal-2020]
* [dayal-2025]
* [evans-2007]
* [hohle-1992]
* [faarlund-lie-vannebo-1997]
-/

@[expose] public section

namespace Clause

/-! ### Sentence types

The sentence types are Sadock and Zwicky's declarative, interrogative, imperative and exclamative,
with the interrogative subtyped as polar, alternative or constituent, and the promissive that
Korean grammaticalizes beside the imperative. A sentence type is a form; the speech act it
conventionally performs is its force, `SpeechAct.Force`. -/

/-- The sentence types, the grammatical kinds of clause a language distinguishes. -/
inductive SentenceType where
  | declarative
  /-- The polar, or yes/no, interrogative. -/
  | polar
  /-- The alternative interrogative, *p or q?*. -/
  | alternative
  /-- The constituent, or wh, interrogative. -/
  | constituent
  | imperative
  | exclamative
  /-- The promissive, which Korean grammaticalizes beside the imperative. -/
  | promissive
  deriving DecidableEq, Repr, Fintype

/-- A sentence type is interrogative when it is polar, alternative or constituent. -/
def SentenceType.IsInterrogative (t : SentenceType) : Prop :=
  t = .polar ∨ t = .alternative ∨ t = .constituent

instance : DecidablePred SentenceType.IsInterrogative :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-! ### Embedding contexts and cells

The embedding contexts are Bhatt and Dayal's four contexts of interrogative embedding together with
Evans's insubordination, the conventionalized root use of a subordinate form. A cell is a sentence
type in an embedding context. -/

/-- Where a clause token occurs, the interrogative-embedding contexts of Bhatt and Dayal and of
Dayal together with Evans's insubordination, a property of the token, not of the clause. -/
inductive EmbeddingContext where
  | matrix
  | subordinated
  /-- Embedded root-like clauses, as Hindi-Urdu *kya:* and Belfast English embedded inversion
  have them. -/
  | quasiSubordinated
  | quotation
  /-- A formally subordinate clause used as a root utterance, as the German command
  *Dass du nicht wieder die Schlüssel vergisst!* and the deliberative question *Ob er immer noch
  kubanische Zigarren mag?*. -/
  | insubordinated
  deriving DecidableEq, Repr, Fintype

/-- The cell of a root clause of sentence type `t`. -/
abbrev root (t : SentenceType) : SentenceType × EmbeddingContext := (t, .matrix)

/-- The cell of a subordinated clause of sentence type `t`. -/
abbrev embedded (t : SentenceType) : SentenceType × EmbeddingContext := (t, .subordinated)

/-! ### Distributions

A particle's licensing and a language's verb-second grammar are distributions. A distribution
determines two relations on cells, where the element or process is possible and where it is
required. -/

/-- A distribution records how far an element or process is required in each cell; `none` means
that the source records nothing for the cell, not that it is excluded. It is a `def`, as `Set` is,
so that it does not inherit the instances of functions into `Option`, whose `⊔` would keep a cell
only one of two distributions records. -/
def Distribution := SentenceType → EmbeddingContext → Option Obligatoriness

namespace Distribution

instance : DecidableEq Distribution :=
  inferInstanceAs (DecidableEq (SentenceType → EmbeddingContext → Option Obligatoriness))

variable (d : Distribution)

/-- The distribution recording no cell. -/
def empty : Distribution := fun _ _ ↦ none

/-- The cells the source records. -/
def recorded : SetRel SentenceType EmbeddingContext := {c | (d c.1 c.2).isSome}

/-- The cells where the element or process is required, the zone `Obligatoriness.required` of
`d` with an unrecorded cell read as excluded, which puts it in neither zone. -/
def required : SetRel SentenceType EmbeddingContext :=
  Obligatoriness.required fun c ↦ (d c.1 c.2).getD ⊥

/-- The cells where the element or process may occur, the zone `Obligatoriness.possible`. -/
def possible : SetRel SentenceType EmbeddingContext :=
  Obligatoriness.possible fun c ↦ (d c.1 c.2).getD ⊥

variable {d} {c : SentenceType × EmbeddingContext}

@[simp]
theorem mem_recorded : c ∈ d.recorded ↔ d c.1 c.2 ≠ none := by
  simp [recorded, Option.isSome_iff_ne_none]

@[simp]
theorem mem_required : c ∈ d.required ↔ d c.1 c.2 = some .obligatory := by
  simp only [required, Obligatoriness.mem_required]; cases d c.1 c.2 <;> simp

@[simp]
theorem mem_possible : c ∈ d.possible ↔ ∃ o ∈ d c.1 c.2, o ≠ .excluded := by
  simp only [possible, Obligatoriness.mem_possible]; cases d c.1 c.2 <;> simp

instance : DecidablePred (· ∈ d.recorded) := fun _ ↦ inferInstanceAs (Decidable (_ = true))

instance : DecidablePred (· ∈ d.required) :=
  inferInstanceAs (DecidablePred (· ∈ Obligatoriness.required _))

instance : DecidablePred (· ∈ d.possible) :=
  inferInstanceAs (DecidablePred (· ∈ Obligatoriness.possible _))

end Distribution

/-! ### Left edges

In the topological field model the finite verb of a clause either stands at its left edge, after
at most one constituent, or later, and a complementizer may introduce the clause. German has one
position for both, Höhle's Φ, which holds the complementizer or the fronted finite verb; in
Norwegian, Faarlund, Lie and Vannebo's connector field holds the complementizer, and schema A
fronts the verb after it, so that the two can co-occur. A language admits a set of left edges in
each cell, and the distributions of verb second and of the complementizer are read off it. -/

/-- The left edge of a clause, written `⟨complementizer, verbSecond⟩`: whether a complementizer
introduces it, and whether its finite verb is fronted. Verb second is meant broadly, as the verb
in C, so that the verb-first order of a yes/no-question counts. -/
structure LeftEdge where
  complementizer : Bool
  verbSecond : Bool
  deriving DecidableEq, Repr, Fintype

/-- The left edges a language admits in each cell; `none` means that the source records nothing
for the cell. -/
def LeftEdge.Table := SentenceType → EmbeddingContext → Option (Finset LeftEdge)

namespace LeftEdge.Table

variable (T : LeftEdge.Table)

/-- The distribution of a property of left edges: in a recorded cell, the obligatoriness allowing
the values the property takes on the edges admitted there. -/
def distribution (p : LeftEdge → Bool) : Distribution :=
  fun t e ↦ (T t e).map (Obligatoriness.of · p)

/-- The distribution of verb second. -/
def verbSecond : Distribution := T.distribution LeftEdge.verbSecond

/-- The distribution of the complementizer. -/
def complementizer : Distribution := T.distribution LeftEdge.complementizer

/-- The left edges with a complementizer, for `b = true`, or without one; a cell admitting none of
them is unrecorded. -/
def restrict (b : Bool) : LeftEdge.Table := fun t e ↦
  (T t e).bind fun s ↦ if (s.filter (·.complementizer = b)).Nonempty then
    some (s.filter (·.complementizer = b)) else none

end LeftEdge.Table

/-! ### Selections

*Whether* selects polar and alternative questions and *wonder* any question. Selections are
ordered by information, the smaller set of types the more specific, and two selections unify to
their intersection when it is nonempty, by the instances of `Core/Order/PartialUnify.lean`. -/

/-- A nonempty set of sentence types, the more specific selection being the smaller set. -/
abbrev Selection.Types := {s : Finset SentenceType // s.Nonempty}ᵒᵈ

/-- The sentence types a clause-typer types or a clausal position selects, `⊥` where nothing is
recorded. -/
abbrev Selection := WithBot Selection.Types

namespace Selection

/-- The selection of a nonempty set of types. -/
def of (s : Finset SentenceType) (h : s.Nonempty := by decide) : Selection :=
  ((OrderDual.toDual ⟨s, h⟩ : Types) : Selection)

/-- The selection of one type. -/
def only (t : SentenceType) : Selection := of {t} (Finset.singleton_nonempty t)

/-- The selection of the three interrogative types. -/
def interrogatives : Selection := of {.polar, .alternative, .constituent}

/-- The types a selection records; none when nothing is recorded. -/
def types : Selection → Finset SentenceType
  | ⊥ => ∅
  | (s : Types) => (OrderDual.ofDual s).1

instance : Membership SentenceType Selection := ⟨fun sel t ↦ t ∈ sel.types⟩

instance : Repr Selection :=
  ⟨fun sel _ ↦ repr (SentenceType.enumList.filter fun t ↦ decide (t ∈ sel.types))⟩

theorem mem_iff {sel : Selection} {t : SentenceType} : t ∈ sel ↔ t ∈ sel.types := Iff.rfl

instance (sel : Selection) (t : SentenceType) : Decidable (t ∈ sel) :=
  inferInstanceAs (Decidable (t ∈ sel.types))

@[simp] theorem types_bot : (⊥ : Selection).types = ∅ := rfl

@[simp] theorem types_of (s : Finset SentenceType) (h : s.Nonempty) : (of s h).types = s := rfl

@[simp] theorem types_only (t : SentenceType) : (only t).types = {t} := rfl

/-- A selection records some interrogative type. -/
def IsInterrogative (sel : Selection) : Prop := ∃ t ∈ sel, t.IsInterrogative

instance (sel : Selection) : Decidable sel.IsInterrogative :=
  inferInstanceAs (Decidable (∃ t ∈ sel.types, _))

end Selection

end Clause
