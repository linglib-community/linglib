/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Core.Data.List.Sublist
public import Mathlib.Data.List.Sort
public import Mathlib.Order.Extension.Linear

/-!
# Cyclic linearization of syntactic structure

[fox-pesetsky-2005]'s theory of the syntax–phonology interface: Spell-out linearizes each
Spell-out domain as the derivation builds it, the ordering statements it establishes are never
deleted (Order Preservation, (52)), and a derivation converges only if the accumulated
statements cohere.

A derivation is its list of phase snapshots. A snapshot contributes the ordering statements
`a < b` between its terminals, the pair-sublist relation `[a, b] <+ p` (`Statement`), and
`SpelloutOrder` is the transitive closure of their union. Convergence (`Consistent`) is
irreflexivity of this candidate order, so the crash condition is exactly that Spell-out induces a
strict order (`consistent_iff_isStrictOrder`), equivalently that some duplicate-free string has
every snapshot as a sub-order (`consistent_iff_exists_linearization`): the derivation has a PF
string. Order Preservation is monotonicity (`SpelloutOrder.mono`), not an axiom; it keeps
adjacency too, since whatever a later Spell-out places between two terminals adjacent at an earlier
one was not spelled out with them (`Consistent.notMem_of_isInfix`); the order reads only the set of
snapshots (`spelloutOrder_perm`); two Spell-outs, the later containing the earlier, cohere exactly
when the earlier is a sub-order of the later (`consistent_pair_iff_sublist`); and `Consistent`
decides on concrete data.

## Main results

* `Minimalist.Linearization.consistent_iff_isStrictOrder`: the crash condition is that
  Spell-out induces a strict order.
* `Minimalist.Linearization.consistent_iff_exists_linearization`: a derivation converges
  exactly when a duplicate-free string extends every Spell-out.

## References

* [fox-pesetsky-2005]
-/

@[expose] public section

namespace Minimalist.Linearization

open List

variable {α : Type*} {phases ps qs : List (List α)} {p q : List α} {a b c : α}

/-- An ordering statement `a < b` is established when the pair `[a, b]` is a sub-order of some
phase snapshot ([fox-pesetsky-2005] (10), (52)). -/
def Statement (phases : List (List α)) (a b : α) : Prop := ∃ p ∈ phases, [a, b] <+ p

/-- The candidate order induced by a derivation is the transitive closure of its ordering
statements. -/
def SpelloutOrder (phases : List (List α)) : α → α → Prop :=
  Relation.TransGen (Statement phases)

/-- A derivation linearizes when its candidate order is irreflexive, so that, transitivity being
free, it is a strict order with no ordering cycle of any length ([fox-pesetsky-2005]'s convergence
condition). -/
def Consistent (phases : List (List α)) : Prop := ∀ a, ¬ SpelloutOrder phases a a

theorem Statement.spelloutOrder (h : Statement phases a b) : SpelloutOrder phases a b := .single h

/-- The crash condition, in order-theoretic vocabulary. -/
theorem consistent_iff_isStrictOrder :
    Consistent phases ↔ IsStrictOrder α (SpelloutOrder phases) :=
  ⟨fun h ↦ { irrefl := h, trans := fun _ _ _ ↦ Relation.TransGen.trans },
   fun h ↦ h.toIrrefl.irrefl⟩

/-- By Order Preservation ((52)) ordering statements are never deleted, so a larger derivation
induces a larger order. -/
theorem SpelloutOrder.mono (h : ∀ p ∈ ps, p ∈ qs) (hab : SpelloutOrder ps a b) :
    SpelloutOrder qs a b :=
  Relation.TransGen.mono (fun _ _ ⟨p, hp, hs⟩ ↦ ⟨p, h p hp, hs⟩) a b hab

theorem spelloutOrder_perm (h : ps.Perm qs) : SpelloutOrder ps = SpelloutOrder qs := by
  funext a b
  exact propext ⟨.mono fun p hp ↦ h.mem_iff.mp hp, .mono fun p hp ↦ h.mem_iff.mpr hp⟩

theorem not_consistent_of_pair (a b : α) (h₁ : Statement phases a b) (h₂ : Statement phases b a) :
    ¬ Consistent phases :=
  fun h ↦ h a (h₁.spelloutOrder.trans h₂.spelloutOrder)

theorem Consistent.nodup (h : Consistent phases) (hp : p ∈ phases) : p.Nodup :=
  nodup_iff_sublist.mpr fun a hs ↦ h a (Statement.spelloutOrder ⟨p, hp, hs⟩)

theorem Consistent.notMem_of_isInfix (h : Consistent phases) (hp : p ∈ phases) (hq : q ∈ phases)
    (hab : [a, b] <:+: p) (hac : [a, c] <+ q) (hcb : [c, b] <+ q) : c ∉ p := by
  intro hc
  obtain ⟨s, t, rfl⟩ := hab
  simp only [mem_append, mem_cons, not_mem_nil, or_false] at hc
  rcases hc with (hs | rfl | rfl) | ht
  · refine not_consistent_of_pair c a ⟨_, hp, ?_⟩ ⟨q, hq, hac⟩ h
    rw [append_assoc]
    exact (singleton_sublist.2 hs).append (by simp)
  · exact h c (Statement.spelloutOrder ⟨q, hq, hac⟩)
  · exact h c (Statement.spelloutOrder ⟨q, hq, hcb⟩)
  · refine not_consistent_of_pair b c ⟨_, hp, ?_⟩ ⟨q, hq, hcb⟩ h
    exact (show [b] <+ s ++ [a, b] by simp).append (singleton_sublist.2 ht)

variable [DecidableEq α]

theorem spelloutOrder_singleton_idxOf (hnd : p.Nodup) (h : SpelloutOrder [p] a b) :
    p.idxOf a < p.idxOf b := by
  induction h with
  | single h =>
    obtain ⟨q, hq, hs⟩ := h
    rw [mem_singleton] at hq
    exact hq ▸ idxOf_lt_of_pair_sublist (hq ▸ hnd) hs
  | tail _ h ih =>
    obtain ⟨q, hq, hs⟩ := h
    rw [mem_singleton] at hq
    exact ih.trans (hq ▸ idxOf_lt_of_pair_sublist (hq ▸ hnd) hs)

theorem consistent_singleton (hnd : p.Nodup) : Consistent [p] :=
  fun _ h ↦ Nat.lt_irrefl _ (spelloutOrder_singleton_idxOf hnd h)

theorem consistent_of_forall_sublist {l : List α} (h : ∀ p ∈ phases, p <+ l) (hnd : l.Nodup) :
    Consistent phases := fun a hab ↦
  consistent_singleton hnd a
    (Relation.TransGen.mono (fun _ _ ⟨p, hp, hs⟩ ↦ ⟨l, mem_singleton_self l, hs.trans (h p hp)⟩)
      a a hab)

theorem consistent_pair_iff_sublist (hq : q.Nodup) (hpq : p ⊆ q) :
    Consistent [p, q] ↔ p <+ q := by
  refine ⟨fun h ↦ sublist_of_forall_pair_sublist (h.nodup (by simp)) hq hpq fun a b hab ↦ ?_,
    fun h ↦ consistent_of_forall_sublist (by simpa using h) hq⟩
  have hne : a ≠ b := by
    rintro rfl; exact h a (Statement.spelloutOrder ⟨p, by simp, hab⟩)
  exact (pair_sublist_or_pair_sublist (hpq (hab.subset (by simp))) (hpq (hab.subset (by simp)))
    hne).resolve_right fun hba ↦ not_consistent_of_pair a b ⟨p, by simp, hab⟩ ⟨q, by simp, hba⟩ h

/-- Every terminal mentioned at some Spell-out. -/
def support (phases : List (List α)) : List α := phases.flatten.dedup

theorem Statement.left_mem_support (h : Statement phases a b) : a ∈ support phases :=
  let ⟨p, hp, hs⟩ := h
  mem_dedup.mpr (mem_flatten.mpr ⟨p, hp, hs.subset (by simp)⟩)

theorem Statement.right_mem_support (h : Statement phases a b) : b ∈ support phases :=
  let ⟨p, hp, hs⟩ := h
  mem_dedup.mpr (mem_flatten.mpr ⟨p, hp, hs.subset (by simp)⟩)

/-- Convergence is the existence of a PF string: a duplicate-free order of the terminals of
which every Spell-out is a sub-order. One direction is `consistent_of_forall_sublist`; the other
extends the candidate order to a linear order (Szpilrajn) and sorts the support by it. -/
theorem consistent_iff_exists_linearization :
    Consistent phases ↔ ∃ l : List α, l.Nodup ∧ ∀ p ∈ phases, p <+ l := by
  refine ⟨fun h ↦ ?_, fun ⟨l, hnd, hl⟩ ↦ consistent_of_forall_sublist hl hnd⟩
  classical
  have := consistent_iff_isStrictOrder.mp h
  have : IsPartialOrder α (Relation.ReflGen (SpelloutOrder phases)) :=
    { toIsPreorder := inferInstance
      antisymm := fun a b hab hba ↦ by
        rcases hab with _ | hab
        · rfl
        rcases hba with _ | hba
        · rfl
        exact (h a (hab.trans hba)).elim }
  obtain ⟨s, hs, hle⟩ := extend_partialOrder (Relation.ReflGen (SpelloutOrder phases))
  have := hs
  refine ⟨(support phases).insertionSort s,
    (perm_insertionSort s _).nodup_iff.mpr (nodup_dedup _), fun p hp ↦
    sublist_insertionSort' ?_ (subperm_of_subset (h.nodup hp) fun a ha ↦ ?_)⟩
  · exact pairwise_iff_forall_sublist.mpr fun hab ↦ hle _ _ (.single (.single ⟨p, hp, hab⟩))
  · exact mem_dedup.mpr (mem_flatten.mpr ⟨p, hp, ha⟩)

/-! ### Decidability

The candidate order's generator only relates terminals in the support, so irreflexivity reduces
to a finite check over the support, with reachability decided by
`Relation.ReflTransGen.decidable_of_finite`. -/

section Decidability

variable (phases)

instance : Decidable (Statement phases a b) := inferInstanceAs (Decidable (∃ p ∈ phases, _))

instance : Decidable (Relation.ReflTransGen (Statement phases) a b) :=
  Relation.ReflTransGen.decidable_of_finite (support phases)
    (fun _ _ h ↦ h.right_mem_support) a b

instance : Decidable (SpelloutOrder phases a b) :=
  decidable_of_iff (∃ c ∈ support phases, Statement phases a c ∧
      Relation.ReflTransGen (Statement phases) c b) <| by
    rw [SpelloutOrder, Relation.TransGen.head'_iff]
    exact ⟨fun ⟨c, _, h, h'⟩ ↦ ⟨c, h, h'⟩, fun ⟨c, h, h'⟩ ↦ ⟨c, h.right_mem_support, h, h'⟩⟩

instance : Decidable (Consistent phases) :=
  decidable_of_iff (∀ a ∈ support phases, ¬ SpelloutOrder phases a a) <| by
    refine ⟨fun h a ha ↦ ?_, fun h a _ ↦ h a⟩
    obtain ⟨c, hac, _⟩ := Relation.TransGen.head'_iff.mp ha
    exact h a hac.left_mem_support ha

end Decidability

end Minimalist.Linearization
