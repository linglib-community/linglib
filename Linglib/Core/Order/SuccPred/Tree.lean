/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.List.Iterate
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Rooted trees from a parent map

`Mathlib/Order/SuccPred/Tree.lean` represents a rooted tree by its ancestorship order, with the
parent of an element as its predecessor. This file goes the other way. A `ParentTree α` is a map
`parent : α → α` with a `root` that is its own parent and that every element reaches by iterating
the map. We define the ancestorship order `a ≤ b ↔ ∃ n, parent^[n] b = a`, for which the root is
`⊥` and the parent is `Order.pred`, and the predecessor is archimedean, so that the order is a
rooted tree in mathlib's sense. On a finite type the order is decidable. The `depth` of an element
is the number of steps from it to the root, one more than the depth of its parent.

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/Tree.lean`.
-/

@[expose] public section

/-- On a finite type, a point reached by iterating a map is reached in fewer steps than the type
has elements. -/
theorem Function.exists_iterate_eq_lt_card {α : Type*} [Fintype α] (f : α → α) {a b : α}
    (h : ∃ n, f^[n] b = a) : ∃ n < Fintype.card α, f^[n] b = a := by
  classical
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  by_contra! hc
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.find h + 1) ↦ f^[i] b) (by simpa using Nat.lt_succ_of_le hc)
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm he.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  have hj := j.is_lt
  have hi := Fin.lt_def.1 hlt
  refine Nat.find_min h (m := Nat.find h - j + i) (by omega) ?_
  rw [Function.iterate_add_apply, he, ← Function.iterate_add_apply,
    Nat.sub_add_cancel (by omega), Nat.find_spec h]

/-- A rooted tree given by its parent map: the root is its own parent, and every element reaches
the root by iterating the map. -/
structure ParentTree (α : Type*) where
  /-- The parent of an element, the root being its own. -/
  parent : α → α
  /-- The root. -/
  root : α
  parent_root : parent root = root
  exists_iterate_eq_root : ∀ a, ∃ n, parent^[n] a = root

namespace ParentTree

variable {α : Type*}

/-- A parent map some iterate of which is constant is a rooted tree. -/
def ofIterate (parent : α → α) (root : α) (k : ℕ) (h : ∀ a, parent^[k] a = root) :
    ParentTree α where
  parent := parent
  root := root
  parent_root := calc
    parent root = parent (parent^[k] root) := by rw [h]
    _ = parent^[k] (parent root) :=
      (Function.iterate_succ_apply' parent k root).symm.trans
        (Function.iterate_succ_apply parent k root)
    _ = root := h _
  exists_iterate_eq_root a := ⟨k, h a⟩

variable (t : ParentTree α) {a b : α}

theorem iterate_root (n : ℕ) : t.parent^[n] t.root = t.root :=
  Function.iterate_fixed t.parent_root n

/-- The root is the only element that returns to itself. -/
theorem eq_root_of_iterate_eq {n : ℕ} (hn : n ≠ 0) (h : t.parent^[n] a = a) : a = t.root := by
  obtain ⟨m, hm⟩ := t.exists_iterate_eq_root a
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h₁ : t.parent^[(k + 1) * m] a = a := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed h m
  rw [← h₁, Nat.succ_mul, Function.iterate_add_apply, hm, t.iterate_root]

/-- The ancestorship order of a rooted tree: `a ≤ b` when iterating the parent map from `b`
reaches `a`. -/
@[reducible] def toPartialOrder : PartialOrder α where
  le a b := ∃ n, t.parent^[n] b = a
  le_refl _ := ⟨0, rfl⟩
  le_trans _ _ _ := fun ⟨m, hm⟩ ⟨n, hn⟩ ↦ ⟨m + n, by rw [Function.iterate_add_apply, hn, hm]⟩
  le_antisymm a b := fun ⟨m, hm⟩ ⟨n, hn⟩ ↦ by
    obtain rfl | hm0 := Nat.eq_zero_or_pos m
    · exact hm.symm
    · have ha : a = t.root := t.eq_root_of_iterate_eq (n := m + n) (by omega)
        (by rw [Function.iterate_add_apply, hn, hm])
      rw [ha, ← hn, ha, t.iterate_root]

/-- The root is the least element. -/
@[reducible] def toOrderBot : @OrderBot α t.toPartialOrder.toLE :=
  letI := t.toPartialOrder
  { bot := t.root
    bot_le := t.exists_iterate_eq_root }

/-- The parent is the predecessor. -/
@[reducible] def toPredOrder : @PredOrder α t.toPartialOrder.toPreorder :=
  letI := t.toPartialOrder
  { pred := t.parent
    pred_le := fun _ ↦ ⟨1, rfl⟩
    min_of_le_pred := fun {a} ⟨n, hn⟩ b _ ↦ by
      rw [t.eq_root_of_iterate_eq (n := n + 1) (by omega) hn]
      exact t.exists_iterate_eq_root b
    le_pred_of_lt := fun {a b} h ↦ by
      obtain ⟨⟨n, hn⟩, hba⟩ := lt_iff_le_not_ge.1 h
      cases n with
      | zero => exact absurd ⟨0, hn.symm⟩ hba
      | succ n => exact ⟨n, hn⟩ }

theorem isPredArchimedean :
    @IsPredArchimedean α t.toPartialOrder.toPreorder t.toPredOrder :=
  letI := t.toPartialOrder
  letI := t.toPredOrder
  ⟨fun h ↦ h⟩

/-- On a finite type the ancestorship order is decided by walking from an element to the root. -/
@[reducible] def decidableLE [Fintype α] [DecidableEq α] :
    @DecidableLE α t.toPartialOrder.toLE :=
  fun a b ↦ decidable_of_iff (a ∈ List.iterate t.parent b (Fintype.card α))
    ⟨fun h ↦ let ⟨n, _, hn⟩ := List.mem_iterate.1 h; ⟨n, hn.symm⟩,
      fun h ↦ List.mem_iterate.2 <|
        (Function.exists_iterate_eq_lt_card t.parent h).imp fun _ hn ↦ ⟨hn.1, hn.2.symm⟩⟩

/-! ### Depth -/

open Classical in
/-- The depth of an element: the number of steps to the root. -/
noncomputable def depth (a : α) : ℕ := Nat.find (t.exists_iterate_eq_root a)

open Classical in
theorem iterate_depth (a : α) : t.parent^[t.depth a] a = t.root :=
  Nat.find_spec (t.exists_iterate_eq_root a)

open Classical in
theorem depth_le {a : α} {n : ℕ} (h : t.parent^[n] a = t.root) : t.depth a ≤ n :=
  Nat.find_min' (t.exists_iterate_eq_root a) h

theorem depth_eq_zero_iff {a : α} : t.depth a = 0 ↔ a = t.root := by
  constructor
  · intro h
    have := t.iterate_depth a
    rwa [h] at this
  · rintro rfl
    exact Nat.le_zero.1 (t.depth_le rfl)

theorem depth_eq_depth_parent_add_one {a : α} (ha : a ≠ t.root) :
    t.depth a = t.depth (t.parent a) + 1 := by
  apply le_antisymm
  · exact t.depth_le (by rw [Function.iterate_succ_apply]; exact t.iterate_depth _)
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (mt t.depth_eq_zero_iff.1 ha)
    have h := t.iterate_depth a
    rw [hn, Function.iterate_succ_apply] at h
    rw [hn]
    exact Nat.succ_le_succ (t.depth_le h)

theorem depth_lt_card [Fintype α] (a : α) : t.depth a < Fintype.card α := by
  obtain ⟨n, hn, h⟩ := Function.exists_iterate_eq_lt_card t.parent (t.exists_iterate_eq_root a)
  exact (t.depth_le h).trans_lt hn

end ParentTree
