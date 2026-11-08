/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Monotone functions taking prescribed values on finitely many sets

`[UPSTREAM]` A function on a preorder can be required to take the value `k i` throughout the set
`s i`, for each `i` in a finset. A monotone such function exists exactly when the prescriptions
agree with the order, `k i ≤ k j` whenever some point of `s i` lies below some point of `s j`. The
condition is necessary since a monotone function preserves the order of the two points, and
sufficient into a join-semilattice with a bottom, the value at `x` being the join of the `k i`
whose set reaches below `x`.

Upstream home: beside `MonotoneOn.exists_monotone_extension` in
`Mathlib/Order/Monotone/Extension.lean`, which extends a single function from a bounded set into a
conditionally complete linear order.
-/

@[expose] public section

variable {ι α β : Type*} [Preorder α] [SemilatticeSup β] [OrderBot β] {t : Finset ι}
  {s : ι → Set α} {k : ι → β}

/-- A monotone function takes the value `k i` on each `s i` exactly when `k i ≤ k j` whenever a
point of `s i` lies below a point of `s j`. -/
theorem exists_monotone_forall_eq_iff :
    (∃ f : α → β, Monotone f ∧ ∀ i ∈ t, ∀ x ∈ s i, f x = k i) ↔
      ∀ i ∈ t, ∀ j ∈ t, (∃ x ∈ s i, ∃ y ∈ s j, x ≤ y) → k i ≤ k j := by
  classical
  refine ⟨fun ⟨f, hf, hk⟩ i hi j hj ⟨x, hx, y, hy, hxy⟩ ↦ hk i hi x hx ▸ hk j hj y hy ▸ hf hxy,
    fun h ↦ ⟨fun x ↦ (t.filter fun i ↦ ∃ y ∈ s i, y ≤ x).sup k, fun x x' hx ↦ ?_,
      fun j hj y hy ↦ ?_⟩⟩
  · exact Finset.sup_mono <| Finset.monotone_filter_right t fun _ _ ⟨z, hz, hzx⟩ ↦
      ⟨z, hz, hzx.trans hx⟩
  · refine le_antisymm (Finset.sup_le fun i hi ↦ ?_)
      (Finset.le_sup (f := k) (Finset.mem_filter.2 ⟨hj, y, hy, le_rfl⟩))
    obtain ⟨hi, z, hz, hzy⟩ := Finset.mem_filter.1 hi
    exact h i hi j hj ⟨z, hz, y, hy, hzy⟩

/-- An antitone function takes the value `k i` on each `s i` exactly when `k i ≤ k j` whenever a
point of `s j` lies below a point of `s i`. -/
theorem exists_antitone_forall_eq_iff :
    (∃ f : α → β, Antitone f ∧ ∀ i ∈ t, ∀ x ∈ s i, f x = k i) ↔
      ∀ i ∈ t, ∀ j ∈ t, (∃ x ∈ s j, ∃ y ∈ s i, x ≤ y) → k i ≤ k j :=
  Iff.trans ⟨fun ⟨f, hf, hk⟩ ↦ ⟨f ∘ OrderDual.ofDual, hf.dual_left, hk⟩,
    fun ⟨f, hf, hk⟩ ↦ ⟨f ∘ OrderDual.toDual, hf.dual_left, hk⟩⟩ <|
    (exists_monotone_forall_eq_iff (α := αᵒᵈ) (s := fun i ↦ OrderDual.ofDual ⁻¹' s i)).trans <|
      forall₂_congr fun _ _ ↦ forall₂_congr fun _ _ ↦ imp_congr_left
        ⟨fun ⟨x, hx, y, hy, h⟩ ↦ ⟨y, hy, x, hx, h⟩, fun ⟨x, hx, y, hy, h⟩ ↦ ⟨y, hy, x, hx, h⟩⟩
