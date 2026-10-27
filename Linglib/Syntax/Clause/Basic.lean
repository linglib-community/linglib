module

public import Linglib.Core.Order.PartialUnify
public import Linglib.Core.Relation.SetRel
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
* `Clause.Occurrence`, `Clause.Distribution`: the value of a cell, ordered by how far it is
  required, and a table of cells.
* `Clause.Occurrence.allowed`, `Clause.Occurrence.ofAllowed`: the presence values an occurrence
  allows, and the occurrence allowing a set of them.
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
conventionally performs is its force, `Discourse.SpeechAct.Force`. -/

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

/-- An occurrence says whether an element or process is obligatory, optional or excluded in a
cell. -/
inductive Occurrence where
  | obligatory
  | optional
  | excluded
  deriving DecidableEq, Repr, Fintype

namespace Occurrence

/-- The rank of an occurrence, from excluded to obligatory. -/
def rank : Occurrence → ℕ
  | .excluded => 0
  | .optional => 1
  | .obligatory => 2

/-- Occurrences are ordered by how far the element is required. -/
instance : LinearOrder Occurrence := .lift' rank (by decide)

instance : BoundedOrder Occurrence where
  bot := .excluded
  bot_le o := by cases o <;> decide
  top := .obligatory
  le_top o := by cases o <;> decide

/-- The values an occurrence allows the presence of the element to take: presence where it is
obligatory, absence where it is excluded, either where it is optional. -/
def allowed : Occurrence → Finset Bool
  | .obligatory => {true}
  | .excluded => {false}
  | .optional => .univ

theorem allowed_injective : Function.Injective allowed := by decide

/-- The occurrence allowing exactly the presence values in `a`: obligatory for presence alone,
excluded for absence alone, optional for both, and excluded for the empty set. -/
def ofAllowed (a : Finset Bool) : Occurrence :=
  if true ∈ a then if false ∈ a then .optional else .obligatory else .excluded

@[simp] theorem ofAllowed_allowed (o : Occurrence) : ofAllowed o.allowed = o := by decide +revert

theorem allowed_ofAllowed {a : Finset Bool} (h : a.Nonempty) : (ofAllowed a).allowed = a := by
  obtain ⟨b, hb⟩ := h
  ext x
  by_cases ht : true ∈ a <;> by_cases hf : false ∈ a <;> cases x <;> cases b <;>
    simp_all [ofAllowed, allowed]

end Occurrence

/-- A distribution records the occurrence of an element or process in each cell; `none` means
that the source records nothing for the cell, not that it is excluded. It is a `def`, as `Set` is,
so that it does not inherit the instances of functions into `Option`, whose `⊔` would keep a cell
only one of two distributions records. -/
def Distribution := SentenceType → EmbeddingContext → Option Occurrence

namespace Distribution

instance : DecidableEq Distribution :=
  inferInstanceAs (DecidableEq (SentenceType → EmbeddingContext → Option Occurrence))

variable (d : Distribution)

/-- The distribution recording no cell. -/
def empty : Distribution := fun _ _ ↦ none

/-- The cells whose recorded occurrence lies in `s`, the preimage of `s` under `d` read as a
partial function on cells. -/
def preimage (s : Set Occurrence) : SetRel SentenceType EmbeddingContext :=
  {c | ∃ o ∈ s, o ∈ d c.1 c.2}

/-- The cells the source records. -/
def recorded : SetRel SentenceType EmbeddingContext := d.preimage .univ

/-- The cells where the element or process is possible, recorded as anything but excluded. -/
def possible : SetRel SentenceType EmbeddingContext := d.preimage {.excluded}ᶜ

/-- The cells where the element or process is required. -/
def required : SetRel SentenceType EmbeddingContext := d.preimage {.obligatory}

variable {d} {s t : Set Occurrence} {c : SentenceType × EmbeddingContext}

@[simp]
theorem mem_preimage : c ∈ d.preimage s ↔ ∃ o ∈ s, o ∈ d c.1 c.2 := .rfl

@[simp]
theorem mem_recorded : c ∈ d.recorded ↔ d c.1 c.2 ≠ none := by
  simp [recorded, Option.ne_none_iff_exists']

@[simp]
theorem mem_possible : c ∈ d.possible ↔ ∃ o ∈ d c.1 c.2, o ≠ .excluded := by
  simp [possible, and_comm]

@[simp]
theorem mem_required : c ∈ d.required ↔ d c.1 c.2 = some .obligatory := by
  simp [required]

@[gcongr]
theorem preimage_mono (h : s ⊆ t) : d.preimage s ⊆ d.preimage t :=
  fun _ ⟨o, hs, ho⟩ ↦ ⟨o, h hs, ho⟩

theorem preimage_subset_recorded (s : Set Occurrence) : d.preimage s ⊆ d.recorded :=
  preimage_mono (Set.subset_univ s)

theorem required_subset_possible : d.required ⊆ d.possible := preimage_mono (by simp)

instance [DecidablePred (· ∈ s)] : DecidablePred (· ∈ d.preimage s) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

instance : DecidablePred (· ∈ d.recorded) := inferInstanceAs (DecidablePred (· ∈ d.preimage _))

instance : DecidablePred (· ∈ d.possible) := inferInstanceAs (DecidablePred (· ∈ d.preimage _))

instance : DecidablePred (· ∈ d.required) := inferInstanceAs (DecidablePred (· ∈ d.preimage _))

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

/-- The distribution of a property of left edges: in a recorded cell, the occurrence allowing
the values the property takes on the edges admitted there. -/
def occurrence (p : LeftEdge → Bool) : Distribution :=
  fun t e ↦ (T t e).map fun s ↦ .ofAllowed (s.image p)

/-- The distribution of verb second. -/
def verbSecond : Distribution := T.occurrence LeftEdge.verbSecond

/-- The distribution of the complementizer. -/
def complementizer : Distribution := T.occurrence LeftEdge.complementizer

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
