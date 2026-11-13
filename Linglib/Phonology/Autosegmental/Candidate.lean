/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Morph

/-!
# Candidates

This file defines the candidates of a form, the states of a serial optimality-theoretic
derivation from it: the autosegments deleted so far and the current surface lines. GEN acts on
candidates and never on the form, so faithfulness constraints compare the surface lines with the
form's lines, and the sponsors of every element stay those of the form. An autosegment that is
neither deleted nor linked on the surface is floating.

## Main definitions

* `Candidate u`: the surface state of a derivation from the form `u`; `Candidate.input` is the
  faithful candidate.
* `Candidate.IsLinked`, `Candidate.IsFloating`: an autosegment with a surface line, and one
  neither deleted nor linked.
* `Candidate.Hosts`: a slot with a surface line to an autosegment of a given kind.
* `Candidate.gen`: the one-step GEN of harmonic serialism.

## Main results

* `Candidate.isNonCrossing_links_of_mem_gen`: GEN is closed on the No-Crossing Constraint.

## Implementation notes

The readings of the surface are `List.finRange` filters, which reduce under kernel `decide`,
because `Finset.sort` does not unfold structurally.

## References

* [mccarthy-mullin-smith-2012]
* [mcpherson-lamont-2026]
* [bermudez-otero-2012]
* [wolf-2007]
-/

@[expose] public section

namespace Autosegmental

universe u

/-- A `Candidate u` is the surface state of a derivation from the form `u`, recording the
autosegments deleted so far and the current surface lines. The faithful candidate is
`Candidate.input u`, and GEN edits candidates while `u` stays fixed. A candidate carries no
sponsors of its own, so, as in [bermudez-otero-2012]'s architecture (p. 47), GEN cannot violate
Consistency of Exponence. -/
@[ext] structure Candidate {S T M : Type u} (u : AR (TwoTier (Sponsored T M) (Sponsored S M))) where
  /-- The autosegments deleted on the surface. -/
  deleted : Finset (Fin (u.word .upper).length)
  /-- The surface association lines. -/
  links : Finset (Fin (u.word .upper).length × Fin (u.word .lower).length)

namespace Candidate

variable {S T M : Type u} {u : AR (TwoTier (Sponsored T M) (Sponsored S M))} (c : Candidate u)
  {k j : Fin (u.word .upper).length}
  {i : Fin (u.word .lower).length} {l : Fin (u.word .upper).length × Fin (u.word .lower).length}

/-- Candidates are compared on their positions alone, whatever the labels of the form. -/
instance : DecidableEq (Candidate u) := fun _ _ ↦ decidable_of_iff _ Candidate.ext_iff.symm

/-- `input u` is the faithful candidate of `u`, with nothing deleted and the form's lines as
its surface lines. -/
@[simps] def input (u : AR (TwoTier (Sponsored T M) (Sponsored S M))) : Candidate u :=
  ⟨∅, u.links .upper .lower⟩

/-! ### Surface predicates -/

/-- Autosegment `k` is linked when it bears a surface line. -/
def IsLinked (k : Fin (u.word .upper).length) : Prop := ∃ l ∈ c.links, l.1 = k

/-- Autosegment `k` is floating when it is not deleted and bears no surface line. -/
def IsFloating (k : Fin (u.word .upper).length) : Prop := k ∉ c.deleted ∧ ¬ c.IsLinked k

/-- `insertedLinks c` is the set of surface lines absent from the form, which GEN has
inserted and `DEP` counts. -/
def insertedLinks : Finset (Fin (u.word .upper).length × Fin (u.word .lower).length) :=
  c.links \ (u.links .upper .lower)

/-- `deletedLinks c` is the set of the form's lines absent from the surface, which GEN has
deleted and `MAX` counts. -/
def deletedLinks : Finset (Fin (u.word .upper).length × Fin (u.word .lower).length) :=
  (u.links .upper .lower) \ c.links

instance : Decidable (c.IsLinked k) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (c.IsFloating k) := inferInstanceAs (Decidable (_ ∧ _))

variable {c}

theorem isLinked_iff : c.IsLinked k ↔ ∃ i, (k, i) ∈ c.links :=
  ⟨fun ⟨⟨_, i⟩, h, rfl⟩ ↦ ⟨i, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

@[simp] theorem mem_insertedLinks : l ∈ c.insertedLinks ↔
    l ∈ c.links ∧ l ∉ (u.links .upper .lower) :=
  Finset.mem_sdiff

@[simp] theorem mem_deletedLinks : l ∈ c.deletedLinks ↔ l ∈ (u.links .upper .lower) ∧ l ∉ c.links :=
  Finset.mem_sdiff

@[simp] theorem insertedLinks_input : (input u).insertedLinks = ∅ := by
  simp [insertedLinks]

@[simp] theorem deletedLinks_input : (input u).deletedLinks = ∅ := by
  simp [deletedLinks]

/-! ### Reading the surface

The readings of the surface are lists over `List.finRange` in tier order, which reduce under
kernel `decide`. -/

variable (c)

/-- `linksTo c i` lists the autosegments linked to slot `i` on the surface, in tier order. -/
def linksTo (i : Fin (u.word .lower).length) : List (Fin (u.word .upper).length) :=
  (List.finRange (u.word .upper).length).filter fun k ↦ (k, i) ∈ c.links

/-- `tierValues c i` lists the values of the autosegments linked to slot `i` on the surface,
in tier order. -/
def tierValues (i : Fin (u.word .lower).length) : List T :=
  (c.linksTo i).map fun k ↦ (u.word .upper)[k].value

/-- `alive c` lists the undeleted autosegments in tier order. -/
def alive : List (Fin (u.word .upper).length) :=
  (List.finRange (u.word .upper).length).filter (· ∉ c.deleted)

variable {c}

@[simp] theorem mem_linksTo : k ∈ c.linksTo i ↔ (k, i) ∈ c.links := by
  simp [linksTo]

variable (c) in
theorem nodup_linksTo (i : Fin (u.word .lower).length) : (c.linksTo i).Nodup :=
  (List.nodup_finRange _).filter _

@[simp] theorem mem_tierValues {t : T} :
    t ∈ c.tierValues i ↔ ∃ k, (k, i) ∈ c.links ∧ (u.word .upper)[k].value = t := by
  simp only [tierValues, List.mem_map]
  exact exists_congr fun k ↦ and_congr_left fun _ ↦ mem_linksTo

@[simp] theorem mem_alive : k ∈ c.alive ↔ k ∉ c.deleted := by
  simp [alive]

/-! ### Hosting -/

section Hosts

variable (c) (P Q : T → Prop)

/-- Slot `i` hosts an autosegment satisfying `P` when one is linked to it on the surface. -/
def Hosts (i : Fin (u.word .lower).length) : Prop :=
  ∃ k, (k, i) ∈ c.links ∧ P (u.word .upper)[k].value

instance [DecidablePred P] : Decidable (c.Hosts P i) :=
  inferInstanceAs (Decidable (∃ _, _ ∧ _))

variable {c P Q}

theorem hosts_iff_exists_mem_tierValues : c.Hosts P i ↔ ∃ t ∈ c.tierValues i, P t := by
  simp only [mem_tierValues]
  exact ⟨fun ⟨k, hk, h⟩ ↦ ⟨_, ⟨k, hk, rfl⟩, h⟩, fun ⟨_, ⟨k, hk, rfl⟩, h⟩ ↦ ⟨k, hk, h⟩⟩

theorem Hosts.mono (h : ∀ t, P t → Q t) : c.Hosts P i → c.Hosts Q i :=
  fun ⟨k, hk, hP⟩ ↦ ⟨k, hk, h _ hP⟩

/-- A slot that hosts an autosegment hosts it on every candidate with more lines. -/
theorem Hosts.of_links_subset {c' : Candidate u} (h : c.links ⊆ c'.links) :
    c.Hosts P i → c'.Hosts P i :=
  fun ⟨k, hk, hP⟩ ↦ ⟨k, h hk, hP⟩

theorem not_hosts_of_links_eq_empty (h : c.links = ∅) : ¬ c.Hosts P i :=
  fun ⟨_, hk, _⟩ ↦ by simp [h] at hk

end Hosts

/-! ### The atomic GEN operations -/

variable (c)

/-- `delete c k` deletes autosegment `k` on the surface, with every surface line it bears. -/
@[simps] def delete (k : Fin (u.word .upper).length) : Candidate u :=
  ⟨insert k c.deleted, c.links.filter (·.1 ≠ k)⟩

/-- `insertLink c k i` inserts the surface line from autosegment `k` to slot `i`. -/
@[simps] def insertLink (k : Fin (u.word .upper).length) (i : Fin (u.word .lower).length) :
    Candidate u :=
  ⟨c.deleted, insert (k, i) c.links⟩

/-- `deleteLink c k i` deletes the surface line from autosegment `k` to slot `i`. -/
@[simps] def deleteLink (k : Fin (u.word .upper).length) (i : Fin (u.word .lower).length) :
    Candidate u :=
  ⟨c.deleted, c.links.erase (k, i)⟩

variable {c}

@[simp] theorem isLinked_delete :
    (c.delete k).IsLinked j ↔ j ≠ k ∧ c.IsLinked j := by
  simp only [isLinked_iff, delete_links, Finset.mem_filter]
  aesop

@[simp] theorem isLinked_insertLink : (c.insertLink k i).IsLinked j ↔ j = k ∨ c.IsLinked j := by
  simp only [isLinked_iff, insertLink_links, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isFloating_delete :
    (c.delete k).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  simp only [IsFloating, delete_deleted, Finset.mem_insert, isLinked_delete]
  tauto

@[simp] theorem isFloating_insertLink :
    (c.insertLink k i).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  simp only [IsFloating, insertLink_deleted, isLinked_insertLink]
  tauto

@[simp] theorem hosts_insertLink {P : T → Prop} {i' : Fin (u.word .lower).length} :
    (c.insertLink k i).Hosts P i' ↔ i' = i ∧ P (u.word .upper)[k].value ∨ c.Hosts P i' := by
  simp only [Hosts, insertLink_links, Finset.mem_insert, Prod.mk.injEq]
  exact ⟨fun ⟨_, h, hP⟩ ↦ h.elim (fun ⟨hk, hi⟩ ↦ .inl ⟨hi, hk ▸ hP⟩) fun h ↦ .inr ⟨_, h, hP⟩,
    fun h ↦ h.elim (fun ⟨hi, hP⟩ ↦ ⟨k, .inl ⟨rfl, hi⟩, hP⟩) fun ⟨j, h, hP⟩ ↦ ⟨j, .inr h, hP⟩⟩

theorem links_delete_subset : (c.delete k).links ⊆ c.links :=
  Finset.filter_subset _ _

theorem links_subset_insertLink : c.links ⊆ (c.insertLink k i).links :=
  Finset.subset_insert _ _

/-! ### One-step GEN -/

section Gen

variable {c' : Candidate u}

/-- `gen c` is the one-step GEN of harmonic serialism. It contains `c` itself, the deletion of
each undeleted autosegment, and each line from a floating autosegment to a slot in its
window, which crosses no surface line; insert-and-associate and shift are omitted. -/
def gen (c : Candidate u) : Finset (Candidate u) :=
  insert c <|
    (Finset.univ.filter (· ∉ c.deleted)).image c.delete ∪
      ((Finset.univ.filter c.IsFloating ×ˢ Finset.univ).filter
        fun p ↦ p.2 ∈ window (c.links : SetRel _ _) p.1).image
          fun p ↦ c.insertLink p.1 p.2

theorem mem_gen : c' ∈ c.gen ↔ c' = c ∨ (∃ k ∉ c.deleted, c' = c.delete k) ∨
    ∃ k i, c.IsFloating k ∧
      i ∈ window (c.links : SetRel _ _) k ∧
        c' = c.insertLink k i := by
  simp only [gen, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product, and_true, Prod.exists, and_assoc,
    eq_comm (a := c')]

@[simp] theorem self_mem_gen : c ∈ c.gen := Finset.mem_insert_self _ _

theorem delete_mem_gen (hd : k ∉ c.deleted) : c.delete k ∈ c.gen :=
  mem_gen.2 (.inr (.inl ⟨k, hd, rfl⟩))

theorem insertLink_mem_gen (hk : c.IsFloating k)
    (hx : i ∈ window (c.links : SetRel _ _) k) :
    c.insertLink k i ∈ c.gen :=
  mem_gen.2 (.inr (.inr ⟨k, i, hk, hx, rfl⟩))

theorem deleted_subset_of_mem_gen (hc : c' ∈ c.gen) : c.deleted ⊆ c'.deleted := by
  rcases mem_gen.1 hc with rfl | ⟨_, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
  exacts [subset_rfl, Finset.subset_insert _ _, subset_rfl]

/-- GEN is closed on the No-Crossing Constraint, since deletion shrinks the surface lines and
each inserted line ends in its node's window. -/
theorem isNonCrossing_links_of_mem_gen
    (h : IsNonCrossing (c.links : SetRel (Fin (u.word .upper).length) (Fin (u.word .lower).length)))
    (hc : c' ∈ c.gen) :
    IsNonCrossing
      (c'.links : SetRel (Fin (u.word .upper).length) (Fin (u.word .lower).length)) := by
  rcases mem_gen.1 hc with rfl | ⟨_, -, rfl⟩ | ⟨_, _, -, hx, rfl⟩
  · exact h
  · exact h.subset (Finset.coe_subset.2 links_delete_subset)
  · simpa using h.insert_of_mem_window hx

end Gen

end Candidate

end Autosegmental
