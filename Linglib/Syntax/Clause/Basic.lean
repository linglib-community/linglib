module

public import Linglib.Core.Order.PartialUnify
public import Linglib.Syntax.Case.Basic
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Basic
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.DeriveFintype

/-!
# Clause axes

This file defines the axes of a clause by which the lexicon and the studies index their facts.
A sentence type is the grammatical kind of a clause: Sadock and Zwicky's declarative,
interrogative, imperative and exclamative, with the interrogative subtyped as polar,
alternative or constituent, and the promissive that Korean grammaticalizes beside the
imperative. A sentence type is a form; the speech act it conventionally performs is its force,
`Discourse.SpeechAct.Force`, read off by `Clause.SentenceType.force`. An embedding context is
where a clause token occurs, Bhatt and Dayal's four contexts together with Evans's
insubordination, the conventionalized root use of a subordinate form. A cell is a sentence type
in an embedding context, and a distribution records for each cell whether some element or process is
obligatory, optional or excluded there, or nothing where the source is silent; the cells where
it is possible and where it is required are the two relations a distribution determines. A
particle's licensing and a language's verb-second grammar are distributions. A selection is
the set of sentence types a complementizer types or a clausal argument position selects, so
that *whether* selects polar and alternative questions and *wonder* any question; selections
are ordered by information, a smaller set being the more specific, and two of them unify to
their intersection when it is nonempty. The subject requirement and the semantic size of a
complement clause are the remaining axes.

## Main definitions

* `Clause.SentenceType`, `Clause.SentenceType.IsInterrogative`: the sentence types.
* `Clause.EmbeddingContext`, `Clause.root`, `Clause.embedded`: the embedding contexts and the
  cells of root and subordinated clauses.
* `Clause.Occurrence`, `Clause.Distribution`: the value of a cell and a table of cells.
* `Clause.Distribution.recorded`, `possible`, `required`: the relations a distribution
  determines.
* `Clause.Selection`: the sentence types a clause-typer types or a clausal position selects,
  unified by intersection.
* `Clause.EmbeddedSubject`, `Clause.Size`: the subject requirement and the size of a
  complement clause.

## References

* [sadock-zwicky-1985]
* [zanuttini-pak-portner-2012]
* [bhatt-dayal-2020]
* [dayal-2025]
* [noonan-2007]
* [bondarenko-2022]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
* [evans-2007]
-/

@[expose] public section

namespace Clause

/-! ### Sentence types -/

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

/-! ### Embedding contexts and cells -/

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

/-! ### Distributions -/

/-- An occurrence says whether an element or process is obligatory, optional or excluded in a
cell. -/
inductive Occurrence where
  | obligatory
  | optional
  | excluded
  deriving DecidableEq, Repr, Fintype

/-- A distribution records the occurrence of an element or process in each cell; `none` means
that the source records nothing for the cell, not that it is excluded. -/
abbrev Distribution := SentenceType → EmbeddingContext → Option Occurrence

namespace Distribution

variable (d : Distribution)

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

instance {R : SetRel SentenceType EmbeddingContext} [DecidablePred (· ∈ R)] :
    DecidablePred (· ∈ R.dom) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

instance {R : SetRel SentenceType EmbeddingContext} [DecidablePred (· ∈ R)] :
    DecidablePred (· ∈ R.cod) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

/-! ### Selections -/

/-- A nonempty set of sentence types, the more specific selection being the smaller set. -/
abbrev Selection.Types := {s : Finset SentenceType // s.Nonempty}ᵒᵈ

/-- The sentence types a clause-typer types or a clausal position selects: nothing recorded,
the bottom, or a nonempty set of types. -/
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
  ⟨fun sel _ ↦ repr (([.declarative, .polar, .alternative, .constituent, .imperative,
    .exclamative, .promissive] : List SentenceType).filter fun t ↦ decide (t ∈ sel.types))⟩

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

/-- Two nonempty sets of types unify to their intersection when it is nonempty. -/
def unifyTypes (a b : Types) : WithTop Types :=
  if h : ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty then
    ((OrderDual.toDual ⟨_, h⟩ : Types) : WithTop Types)
  else ⊤

theorem le_iff {a b : Types} : a ≤ b ↔ (OrderDual.ofDual b).1 ⊆ (OrderDual.ofDual a).1 :=
  Iff.rfl

instance : PartialUnify Types where
  unify := unifyTypes
  isLUB_of_unify_eq_coe := by
    intro a b c h
    unfold unifyTypes at h
    split at h
    · next hne =>
      obtain rfl := WithTop.coe_inj.mp h
      refine ⟨mem_upperBounds_pair.mpr
        ⟨le_iff.mpr Finset.inter_subset_left, le_iff.mpr Finset.inter_subset_right⟩,
        fun u hu ↦ ?_⟩
      obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
      exact le_iff.mpr (Finset.subset_inter (le_iff.mp hau) (le_iff.mp hbu))
    · exact absurd h WithTop.top_ne_coe
  unify_ne_top_of_bddAbove := by
    intro a b ⟨u, hu⟩
    obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
    have hne : ((OrderDual.ofDual a).1 ∩ (OrderDual.ofDual b).1).Nonempty :=
      (OrderDual.ofDual u).2.mono (Finset.subset_inter (le_iff.mp hau) (le_iff.mp hbu))
    simp [unifyTypes, hne]

/-- The bottom unifies with anything, and two recorded selections unify to their intersection
when it is nonempty. -/
def unify : Selection → Selection → WithTop Selection
  | ⊥, y => y
  | (a : Types), ⊥ => (a : Selection)
  | (a : Types), (b : Types) => (PartialUnify.unify a b).map WithBot.some

instance : PartialUnify Selection where
  unify := unify
  isLUB_of_unify_eq_coe := by
    intro x y z h
    match x, y with
    | ⊥, y =>
      obtain rfl := WithTop.coe_inj.mp h
      exact ⟨mem_upperBounds_pair.mpr ⟨bot_le, le_rfl⟩,
        fun u hu ↦ (mem_upperBounds_pair.mp hu).2⟩
    | (a : Types), ⊥ =>
      obtain rfl := WithTop.coe_inj.mp h
      exact ⟨mem_upperBounds_pair.mpr ⟨le_rfl, bot_le⟩,
        fun u hu ↦ (mem_upperBounds_pair.mp hu).1⟩
    | (a : Types), (b : Types) =>
      simp only [unify, WithTop.map_eq_some_iff] at h
      obtain ⟨c, hc, rfl⟩ := h
      have hl := PartialUnify.isLUB_of_unify_eq_coe hc
      obtain ⟨hac, hbc⟩ := mem_upperBounds_pair.mp hl.1
      refine ⟨mem_upperBounds_pair.mpr
        ⟨WithBot.coe_le_coe.mpr hac, WithBot.coe_le_coe.mpr hbc⟩, fun u hu ↦ ?_⟩
      obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
      obtain ⟨u', rfl, hau'⟩ := WithBot.coe_le_iff.mp hau
      exact WithBot.coe_le_coe.mpr (hl.2 (mem_upperBounds_pair.mpr
        ⟨hau', WithBot.coe_le_coe.mp hbu⟩))
  unify_ne_top_of_bddAbove := by
    intro x y ⟨u, hu⟩
    obtain ⟨hxu, hyu⟩ := mem_upperBounds_pair.mp hu
    match x, y with
    | ⊥, _ => exact WithTop.coe_ne_top
    | (a : Types), ⊥ => exact WithTop.coe_ne_top
    | (a : Types), (b : Types) =>
      obtain ⟨u', rfl, hau'⟩ := WithBot.coe_le_iff.mp hxu
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (PartialUnify.unify_ne_top_of_bddAbove
        ⟨u', mem_upperBounds_pair.mpr ⟨hau', WithBot.coe_le_coe.mp hyu⟩⟩)
      simp [unify, ← hc]

end Selection

/-! ### Complement clauses -/

/-- The subject of an embedded clause is obligatorily null, as in control complements, or
overt, optionally with a fixed case. Genitive marking on the subject is Noonan's criterion for
the nominalization coding; Bondarenko's Buryat genitive subjects of nominalized clauses are the
modern instance. -/
inductive EmbeddedSubject where
  | obligatorilyNull
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr

/-- The semantic sort of a complement clause, which fixes the minimal structure it needs, the
implicational complementation hierarchy of Wurmbrand and Lohninger: an event needs only the
thematic domain, a situation adds the tense–mood–aspect domain, a proposition adds the
operator domain. Ordered by containment. -/
inductive Size where
  | event
  | situation
  | proposition
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder Size := .lift' Size.ctorIdx (by decide)

end Clause
