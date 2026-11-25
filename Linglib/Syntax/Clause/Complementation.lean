/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Syntax.Feature.Case.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Complement clauses

A complement clause has, besides its sentence type, a complement type and a realization of its
subject. Noonan's cross-linguistic survey of complementation sorts complement clauses into six
complement types by the part of speech of the predicate, the relation of the subject to the
predicate, and the inflectional categories the clause carries. The subject of a complement
clause, where it has one of its own, is overt or unexpressed.

A predicate selects complement clauses, and a complementizer types them, in these three respects.
A *selection* is the set of complement types, the set of sentence types and the set of subject
realizations admitted: the selection of *whether* is the polar and the alternative interrogative,
with every complement type and every subject. One selection is at most another, `k ≤ l`, when it
admits at most the other's values in each respect, so the more specific selection is the smaller,
and the selection admitting everything is `⊤`. A selection takes another when some clause is
admitted by both and both restrict a common respect.

The size of a complement is the semantic sort it denotes, which fixes the structure it needs.

## Main definitions

* `Clause.ComplementType`: the six complement types.
* `Clause.EmbeddedSubject`: the realization of a complement clause's own subject.
* `Clause.Selection`: the complement types, sentence types and subject realizations admitted.
* `Clause.Selection.Takes`: two selections admit a common clause and restrict a common respect.
* `Clause.Size`: the semantic size of a complement clause, ordered by containment.

## Main results

* `Clause.Selection.le_iff_admits_subset`: for a selection admitting some clause, the order is
  inclusion of the clauses admitted.
* `Clause.Selection.not_disjoint_admits`: two selections admit a common clause exactly when they
  share a value in each respect.

## Implementation notes

* A complement type is reduced when it has fewer syntactic and inflectional possibilities than an
  indicative main clause. That is a fact about a language's complement types rather than about
  the six labels, since the subjunctive is typically reduced but need not be, so no predicate on
  `ComplementType` states it; the predicate that is a fact about the labels is
  `ComplementType.IsSentenceLike`.
* A selection is a set of admissible values in each respect, not an optional value: a respect on
  which nothing is recorded admits everything, two selections are consistent when they admit a
  common clause, and they unify to their intersection.
* `Selection.Takes` asks for more than a common clause. An entry that restricts nothing, as a
  converb suffix or the complement position of a small clause, falls outside the complement types
  and is taken by nothing, though the set it admits is every clause; the second condition of
  `Takes` records this.

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

/-- The realization of a complement clause's subject: unpronounced, as under control or raising,
or overt, optionally with a fixed case. Genitive marking on the subject is
[noonan-2007]'s criterion for the nominalized complement type, and the genitive subjects of Buryat
nominalized clauses are a modern instance ([bondarenko-2022]). -/
inductive EmbeddedSubject where
  | null
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr, Fintype

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

/-! ### Selections -/

instance : Repr (Finset ComplementType) :=
  ⟨fun s _ ↦ repr (ComplementType.enumList.filter (· ∈ s))⟩

instance : Repr (Finset EmbeddedSubject) :=
  ⟨fun s _ ↦ repr ((EmbeddedSubject.null :: .overt none ::
    Case.enumList.map fun c ↦ .overt (some c)).filter (· ∈ s))⟩

/-- What a predicate selects of a complement clause, and what a complementizer types: the
complement types, the sentence types and the subject realizations admitted, each all of them
unless restricted. -/
@[ext]
structure Selection where
  /-- The [noonan-2007] complement types admitted. -/
  coding : Finset ComplementType := Finset.univ
  /-- The sentence types admitted. -/
  types : Finset SentenceType := Finset.univ
  /-- The realizations of the clause's own subject admitted. -/
  subject : Finset EmbeddedSubject := Finset.univ
  deriving DecidableEq, Repr

namespace Selection

variable {k l : Selection}

/-- A selection is at most another when it admits at most the other's values in each respect. -/
instance : PartialOrder Selection :=
  PartialOrder.lift (fun k ↦ (k.coding, k.types, k.subject)) fun k l h ↦ by
    cases k; cases l; simp_all

theorem le_def :
    k ≤ l ↔ k.coding ⊆ l.coding ∧ k.types ⊆ l.types ∧ k.subject ⊆ l.subject := Iff.rfl

/-- The selection admitting everything. -/
instance : OrderTop Selection where
  top := {}
  le_top _ := ⟨Finset.subset_univ _, Finset.subset_univ _, Finset.subset_univ _⟩

@[simp] theorem coding_top : (⊤ : Selection).coding = Finset.univ := rfl

@[simp] theorem types_top : (⊤ : Selection).types = Finset.univ := rfl

@[simp] theorem subject_top : (⊤ : Selection).subject = Finset.univ := rfl

theorem eq_top_iff' :
    k = ⊤ ↔ k.coding = Finset.univ ∧ k.types = Finset.univ ∧ k.subject = Finset.univ :=
  Selection.ext_iff

/-- The order, decided without enumerating a respect the larger selection leaves unrestricted. -/
instance : DecidableLE Selection := fun k l ↦
  decidable_of_iff
    ((l.coding.card = Fintype.card ComplementType ∨ k.coding ⊆ l.coding) ∧
      (l.types.card = Fintype.card SentenceType ∨ k.types ⊆ l.types) ∧
        (l.subject.card = Fintype.card EmbeddedSubject ∨ k.subject ⊆ l.subject)) <| by
    have h {α : Type} [Fintype α] (s t : Finset α) : t.card = Fintype.card α ∨ s ⊆ t ↔ s ⊆ t :=
      or_iff_right_of_imp fun h ↦ (Finset.card_eq_iff_eq_univ t).1 h ▸ Finset.subset_univ s
    rw [h, h, h, le_def]

/-! ### The clauses a selection admits -/

/-- The complement clauses a selection admits, each a complement type, a sentence type and a
subject realization. -/
def admits (k : Selection) : Finset (ComplementType × SentenceType × EmbeddedSubject) :=
  k.coding ×ˢ k.types ×ˢ k.subject

@[simp] theorem mem_admits {c : ComplementType} {t : SentenceType} {s : EmbeddedSubject} :
    (c, t, s) ∈ k.admits ↔ c ∈ k.coding ∧ t ∈ k.types ∧ s ∈ k.subject := by
  simp [admits]

theorem admits_nonempty :
    k.admits.Nonempty ↔ k.coding.Nonempty ∧ k.types.Nonempty ∧ k.subject.Nonempty := by
  simp [admits, Finset.nonempty_product]

theorem admits_mono : Monotone admits := fun _ _ h ↦
  Finset.product_subset_product h.1 (Finset.product_subset_product h.2.1 h.2.2)

/-- For a selection admitting some clause, the order is inclusion of the clauses admitted. -/
theorem le_iff_admits_subset (hk : k.admits.Nonempty) : k ≤ l ↔ k.admits ⊆ l.admits := by
  obtain ⟨⟨c, t, s⟩, h⟩ := hk
  rw [mem_admits] at h
  refine ⟨fun h' ↦ admits_mono h', fun h' ↦ ⟨fun c' hc ↦ ?_, fun t' ht ↦ ?_, fun s' hs ↦ ?_⟩⟩
  · exact (mem_admits.1 (h' (mem_admits.2 ⟨hc, h.2⟩))).1
  · exact (mem_admits.1 (h' (mem_admits.2 ⟨h.1, ht, h.2.2⟩))).2.1
  · exact (mem_admits.1 (h' (mem_admits.2 ⟨h.1, h.2.1, hs⟩))).2.2

/-- Two selections admit a common clause exactly when they share a value in each respect. -/
theorem not_disjoint_admits :
    ¬ Disjoint k.admits l.admits ↔ ¬ Disjoint k.coding l.coding ∧ ¬ Disjoint k.types l.types ∧
      ¬ Disjoint k.subject l.subject := by
  simp only [admits, Finset.not_disjoint_iff_nonempty_inter, Finset.product_inter_product,
    Finset.nonempty_product]

/-! ### Taking -/

/-- A selection takes another when some clause is admitted by both and both restrict a common
respect. The relation is symmetric; it is read with `k` the selection of a predicate and `l`
that of a complementizer. -/
def Takes (k l : Selection) : Prop :=
  ¬ Disjoint k.admits l.admits ∧
    (k.coding ≠ Finset.univ ∧ l.coding ≠ Finset.univ ∨
      k.types ≠ Finset.univ ∧ l.types ≠ Finset.univ ∨
        k.subject ≠ Finset.univ ∧ l.subject ≠ Finset.univ)

/-- `Takes`, decided by a common value in each respect and the sizes of the sets. -/
instance : Decidable (k.Takes l) :=
  decidable_of_iff
    (((∃ c ∈ k.coding, c ∈ l.coding) ∧ (∃ t ∈ k.types, t ∈ l.types) ∧
        ∃ s ∈ k.subject, s ∈ l.subject) ∧
      (k.coding.card ≠ Fintype.card ComplementType ∧
          l.coding.card ≠ Fintype.card ComplementType ∨
        k.types.card ≠ Fintype.card SentenceType ∧ l.types.card ≠ Fintype.card SentenceType ∨
          k.subject.card ≠ Fintype.card EmbeddedSubject ∧
            l.subject.card ≠ Fintype.card EmbeddedSubject)) <| by
    rw [Takes, not_disjoint_admits]
    simp only [Finset.not_disjoint_iff, ne_eq, Finset.card_eq_iff_eq_univ]

theorem Takes.symm (h : k.Takes l) : l.Takes k :=
  ⟨fun hd ↦ h.1 hd.symm, h.2.imp And.symm (Or.imp And.symm And.symm)⟩

/-- A selection restricting nothing takes nothing. -/
theorem not_top_takes : ¬ (⊤ : Selection).Takes l := fun h ↦ by
  simpa using h.2

/-- A selection restricting nothing is taken by nothing. -/
theorem not_takes_top : ¬ k.Takes ⊤ := fun h ↦ not_top_takes h.symm

/-- A selection takes itself exactly when it admits some clause and restricts some respect. -/
theorem takes_self_iff : k.Takes k ↔ k.admits.Nonempty ∧ k ≠ ⊤ := by
  simp only [Takes, disjoint_self, Finset.bot_eq_empty, ← Finset.nonempty_iff_ne_empty, and_self,
    ne_eq, eq_top_iff', not_and_or]

end Selection

end Clause
