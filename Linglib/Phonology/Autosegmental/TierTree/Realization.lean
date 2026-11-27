/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Realization
public import Linglib.Phonology.Autosegmental.TierTree.Basic

/-!
# Realizations along a tree of tiers

A realization `(w.map g₀).prod` whose primitives have one slot each bears at slot `k` the
melody that the primitive of its `k`th symbol bears at its slot (`melody_prod_map`). When the
primitives have at most one token on each tier, the realization is functional
(`isFunctional_prod_map`), and when each primitive is a tree, the children of a token are the
tokens of its own symbol on the tiers hanging from its tier (`mem_children_prod_map`).

## References

* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] (T : ParentTree ι)

variable {S : Type*} (g₀ : S → AR τ) {w : List S} {j : ι} {k : ℕ}

section

omit [Fintype ι] [DecidableEq ι]

variable {g₀}

/-- A realization whose primitives have at most one token on each tier is functional. -/
theorem isFunctional_prod_map (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1) :
    (w.map g₀).prod.IsFunctional T := by
  intro j p q q' _ hl hl'
  obtain ⟨k, hk, rfl, rfl, hl0⟩ :=
    (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hl
  obtain ⟨k', hk', he, rfl, hl0'⟩ :=
    (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hl'
  rw [eq_of_tierOffset_eq g₀ _ w hk hk' (List.ne_nil_of_length_pos hl0.lt_left)
    (List.ne_nil_of_length_pos hl0'.lt_left) he]


end

/-- A realization whose primitives have one slot each bears at slot `k` the melody that the
primitive of its `k`th symbol bears. -/
theorem melody_prod_map (h : ∀ s, ((g₀ s).word T.root).length = 1) (hk : k < w.length) :
    (w.map g₀).prod.melody T k j = (g₀ w[k]).melody T 0 j := by
  induction w generalizing k with
  | nil => simp at hk
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons]
    cases k with
    | zero => exact melody_mul_left (by rw [h]; exact Nat.one_pos)
    | succ k =>
      have key := melody_mul_right (T := T) (X := g₀ a) (Y := (w.map g₀).prod) (k := k) (j := j)
      rw [h a] at key
      rw [key]
      exact ih (Nat.lt_of_succ_lt_succ hk)

/-- A realization bears a label at slot `k` exactly when the primitive of its `k`th symbol
does. -/
theorem mem_melody_prod_map (h : ∀ s, ((g₀ s).word T.root).length = 1) {b : τ j} :
    b ∈ (w.map g₀).prod.melody T k j ↔ ∃ hk : k < w.length, b ∈ (g₀ w[k]).melody T 0 j := by
  by_cases hk : k < w.length
  · rw [melody_prod_map T g₀ h hk]
    exact ⟨fun hb ↦ ⟨hk, hb⟩, fun ⟨_, hb⟩ ↦ hb⟩
  · refine iff_of_false (notMem_melody_of_length_le ?_) fun ⟨hk', _⟩ ↦ hk hk'
    rw [length_word_prod_map_of_length_eq_one g₀ T.root w h]
    exact not_lt.1 hk


/-- In a realization by trees with at most one token on a tier, the children of a token are the
tokens of its own symbol on the tiers hanging from its tier. -/
theorem mem_children_prod_map (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1)
    (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
    {i' t : ι} {p q : ℕ} :
    (t, q) ∈ (w.map g₀).prod.children T (i', p) ↔ T.parent t = i' ∧ t ≠ T.root ∧
      ∃ k, ∃ hk : k < w.length, p = tierOffset g₀ i' w k ∧ q = tierOffset g₀ t w k ∧
        (g₀ w[k]).word t ≠ [] := by
  rw [mem_children]
  constructor
  · rintro ⟨hp, hr, hl⟩
    obtain rfl : T.parent t = i' := hp
    replace hl : (w.map g₀).prod.Link (T.parent t) t p q := hl
    obtain ⟨k, hk, rfl, rfl, hl0⟩ :=
      (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hl
    exact ⟨rfl, hr, k, hk, rfl, rfl, (htree _ t hr).1 hl0⟩
  · rintro ⟨rfl, hr, k, hk, rfl, rfl, hne⟩
    exact ⟨rfl, hr, (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).2
      ⟨k, hk, rfl, rfl, (htree _ t hr).2 hne⟩⟩


end Autosegmental.AR
