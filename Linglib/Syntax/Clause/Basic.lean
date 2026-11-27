/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.SetRel
public import Linglib.Syntax.Obligatoriness
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Sentence types and their distribution

A sentence type is the grammatical kind of a clause, such as the declarative or the polar
interrogative, and an embedding context is where a clause token occurs, as a root or under
subordination. A distribution records, for each sentence type in each embedding context, whether
some element or process is obligatory, optional or excluded there. What a predicate selects of a
complement clause, its sentence types among other properties, is in
`Syntax/Clause/Complementation.lean`.

## Main definitions

* `Clause.SentenceType`, `Clause.SentenceType.IsInterrogative`: the sentence types.
* `Clause.EmbeddingContext`, `Clause.Cell`, `Clause.root`, `Clause.embedded`: the embedding
  contexts, and the cells of root and subordinated clauses.
* `Clause.Distribution`: the `Obligatoriness` recorded in each cell.
* `Clause.Distribution.recorded`, `possible`, `required`: the relations a distribution
  determines.
* `Clause.Distribution.types`, `contexts`: the sentence types and the embedding contexts in which
  the element may occur.
* `Clause.LeftEdge`, `Clause.LeftEdge.Table`: whether a complementizer introduces a clause and
  whether its finite verb is fronted, and the left edges a language admits in each cell.

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

instance : Repr (Finset SentenceType) :=
  ⟨fun s _ ↦ repr (SentenceType.enumList.filter (· ∈ s))⟩

/-- The three interrogative sentence types. -/
def SentenceType.interrogatives : Finset SentenceType := {.polar, .alternative, .constituent}

@[simp] theorem SentenceType.mem_interrogatives {t : SentenceType} :
    t ∈ interrogatives ↔ t.IsInterrogative := by
  simp [interrogatives, IsInterrogative]

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

/-- A cell is a sentence type in an embedding context. -/
abbrev Cell := SentenceType × EmbeddingContext

/-- The cell of a root clause of sentence type `t`. -/
abbrev root (t : SentenceType) : Cell := (t, .matrix)

/-- The cell of a subordinated clause of sentence type `t`. -/
abbrev embedded (t : SentenceType) : Cell := (t, .subordinated)

/-! ### Distributions

A particle's licensing and a language's verb-second grammar are distributions. A distribution
determines two relations on cells, where the element or process is possible and where it is
required. -/

/-- A distribution records how far an element or process is required in each cell; `none` means
that the source records nothing for the cell, not that it is excluded. It is a `def`, as `Set` is,
so that it does not inherit the instances of functions into `Option`, whose `⊔` would keep a cell
only one of two distributions records. -/
def Distribution := Cell → Option Obligatoriness

namespace Distribution

instance : DecidableEq Distribution :=
  inferInstanceAs (DecidableEq (Cell → Option Obligatoriness))

/-- A distribution is shown as its recorded cells. -/
instance : Repr Distribution :=
  ⟨fun d _ ↦ repr <|
    (SentenceType.enumList.flatMap fun t ↦ EmbeddingContext.enumList.map (t, ·)).filterMap
      fun c ↦ (d c).map (c, ·)⟩

variable (d : Distribution)

/-- The distribution recording no cell. -/
def empty : Distribution := fun _ ↦ none

/-- The cells the source records. -/
def recorded : SetRel SentenceType EmbeddingContext := {c | (d c).isSome}

/-- The cells where the element or process is required, the zone `Obligatoriness.required` of
`d` with an unrecorded cell read as excluded, which puts it in neither zone. -/
def required : SetRel SentenceType EmbeddingContext :=
  Obligatoriness.required fun c ↦ (d c).getD ⊥

/-- The cells where the element or process may occur, the zone `Obligatoriness.possible`. -/
def possible : SetRel SentenceType EmbeddingContext :=
  Obligatoriness.possible fun c ↦ (d c).getD ⊥

variable {d} {c : Cell}

@[simp]
theorem mem_recorded : c ∈ d.recorded ↔ d c ≠ none := by
  simp [recorded, Option.isSome_iff_ne_none]

@[simp]
theorem mem_required : c ∈ d.required ↔ d c = some .obligatory := by
  simp only [required, Obligatoriness.mem_required]; cases d c <;> simp

@[simp]
theorem mem_possible : c ∈ d.possible ↔ ∃ o ∈ d c, o ≠ .excluded := by
  simp only [possible, Obligatoriness.mem_possible]; cases d c <;> simp

instance : DecidablePred (· ∈ d.recorded) := fun _ ↦ inferInstanceAs (Decidable (_ = true))

instance : DecidablePred (· ∈ d.required) :=
  inferInstanceAs (DecidablePred (· ∈ Obligatoriness.required _))

instance : DecidablePred (· ∈ d.possible) :=
  inferInstanceAs (DecidablePred (· ∈ Obligatoriness.possible _))

/-- The sentence types in which the element may occur in some embedding context. -/
def types (d : Distribution) : Finset SentenceType := {t | t ∈ d.possible.dom}

/-- The embedding contexts in which the element may occur with some sentence type. -/
def contexts (d : Distribution) : Finset EmbeddingContext := {e | e ∈ d.possible.cod}

@[simp] theorem mem_types {t : SentenceType} : t ∈ d.types ↔ ∃ e, (t, e) ∈ d.possible := by
  simp [types, SetRel.mem_dom]

@[simp] theorem mem_contexts {e : EmbeddingContext} :
    e ∈ d.contexts ↔ ∃ t, (t, e) ∈ d.possible := by
  simp [contexts, SetRel.mem_cod]

@[simp, norm_cast] theorem coe_types : (d.types : Set SentenceType) = d.possible.dom := by
  ext; simp [types]

@[simp, norm_cast] theorem coe_contexts : (d.contexts : Set EmbeddingContext) = d.possible.cod := by
  ext; simp [contexts]

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
def LeftEdge.Table := Cell → Option (Finset LeftEdge)

namespace LeftEdge.Table

variable (T : LeftEdge.Table)

/-- The distribution of a property of left edges: in a recorded cell, the obligatoriness allowing
the values the property takes on the edges admitted there. -/
def distribution (p : LeftEdge → Bool) : Distribution :=
  fun c ↦ (T c).map (Obligatoriness.of · p)

/-- The distribution of verb second. -/
def verbSecond : Distribution := T.distribution LeftEdge.verbSecond

/-- The distribution of the complementizer. -/
def complementizer : Distribution := T.distribution LeftEdge.complementizer

/-- The left edges with a complementizer, for `b = true`, or without one; a cell admitting none of
them is unrecorded. -/
def restrict (b : Bool) : LeftEdge.Table := fun c ↦
  (T c).bind fun s ↦ if (s.filter (·.complementizer = b)).Nonempty then
    some (s.filter (·.complementizer = b)) else none

end LeftEdge.Table

end Clause
