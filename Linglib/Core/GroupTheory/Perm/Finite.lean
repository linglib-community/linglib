/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations that move finitely many points

A permutation of any type agrees on a given finite set with a permutation that moves only
finitely many points.

`[UPSTREAM]` candidate for `Mathlib/GroupTheory/Perm/Finite.lean`.
-/

public section

/-- A permutation agrees on any finite set of points with a permutation that moves finitely many
points. -/
theorem Equiv.Perm.exists_finite_setOf_ne_and_eqOn {α : Type*} (σ : Equiv.Perm α)
    (s : Finset α) : ∃ τ : Equiv.Perm α, {a | τ a ≠ a}.Finite ∧ Set.EqOn τ σ s := by
  classical
  let t : Finset α := s ∪ s.image σ
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair (α := s) (β := t)
    (fun a ↦ ⟨a, Finset.mem_union_left _ a.2⟩)
    (fun a ↦ ⟨σ a, Finset.mem_union_right _ (Finset.mem_image_of_mem σ a.2)⟩)
    (fun a b h ↦ Subtype.ext (by simpa using h))
    (fun a b h ↦ Subtype.ext (by simpa using h))
  refine ⟨Equiv.Perm.ofSubtype (p := (· ∈ t)) ρ, t.finite_toSet.subset fun a ha ↦ ?_,
    fun a ha ↦ ?_⟩
  · by_contra h
    exact ha (Equiv.Perm.ofSubtype_apply_of_not_mem _ h)
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ (Finset.mem_union_left _ ha)]
    exact congrArg Subtype.val (hρ ⟨a, ha⟩)
