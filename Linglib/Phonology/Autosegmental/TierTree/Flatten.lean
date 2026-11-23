/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TierTree.Basic

/-!
# Dominance as association

In a representation along a tree of tiers, a slot dominates the tokens that descending lines
lead to. The flattening `X.flatten T` of a representation `X` has the words of `X`, and a line
from each slot to every token the slot dominates, and no other line. Its tiers form a star: every
tier hangs from the slots.

Flattening does not change what a slot dominates, so the melody of a slot is the same before and
after (`melody_flatten`), and flattening twice is flattening once. Flattening commutes with
concatenation, so it is a monoid homomorphism, `flattenHom`.

Flattening is how an intermediate tier is contracted: after it, `AR.comapDomain` can drop the
tier without losing the lines that ran through it.

## TODO

* A flattening of a representation that obeys the No-Crossing Constraint obeys it when each token
  has at most one line to each lower tier.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] (T : ParentTree ι)
  (X Y : AR τ) {i j : ι} {k p q : ℕ}

/-- The flattening of a representation: each slot has a line to every token it dominates, and
there is no other line. -/
def flatten : AR τ := fromRel X.word fun i j p q ↦ i = T.root ∧ X.Dominates T p j q

@[simp] theorem word_flatten : (X.flatten T).word = X.word := rfl

variable {T X}

/-- A slot that dominates a token of another tier is a position of the skeleton. -/
theorem Dominates.lt_length (h : X.Dominates T k j q) (hj : j ≠ T.root) :
    k < (X.word T.root).length := by
  by_contra hk
  have h' : (j, q) ∈ X.descendants T (Fintype.card ι) (T.root, k) := h
  rw [descendants_eq_singleton (v := (T.root, k)) (not_lt.1 hk)] at h'
  exact hj (congrArg Prod.fst (Finset.mem_singleton.1 h'))

theorem Dominates.lt_length_right (h : X.Dominates T k j q) (hk : k < (X.word T.root).length) :
    q < (X.word j).length :=
  lt_length_of_mem_descendants (v := (T.root, k)) hk h

theorem link_flatten_iff : (X.flatten T).Link i j p q ↔
    i ≠ j ∧ (i = T.root ∧ X.Dominates T p j q ∨ j = T.root ∧ X.Dominates T q i p) := by
  rw [flatten, link_fromRel]
  refine and_congr_right fun hij ↦ ⟨fun h ↦ h.2.2, fun h ↦ ?_⟩
  rcases h with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
  · have hp := hd.lt_length (Ne.symm hij)
    exact ⟨hp, hd.lt_length_right hp, .inl ⟨rfl, hd⟩⟩
  · have hq := hd.lt_length hij
    exact ⟨hd.lt_length_right hq, hq, .inr ⟨rfl, hd⟩⟩

/-- In a flattening, a slot has a line to a token of another tier if and only if it dominates
the token. -/
theorem link_flatten (hj : j ≠ T.root) :
    (X.flatten T).Link T.root j k q ↔ X.Dominates T k j q := by
  rw [link_flatten_iff]
  exact ⟨fun h ↦ h.2.elim (·.2) fun h' ↦ absurd h'.1 hj, fun h ↦ ⟨Ne.symm hj, .inl ⟨rfl, h⟩⟩⟩

theorem dominates_root_iff : X.Dominates T k T.root q ↔ q = k :=
  ⟨fun h ↦ (congrArg Prod.snd (dominates_iff_dom.1 h).eq_of_root).symm,
    fun h ↦ h ▸ mem_descendants_self _ _⟩

/-- A slot dominates in the flattening what it dominates in the representation. -/
@[simp] theorem dominates_flatten :
    (X.flatten T).Dominates (.star T.root) k j q ↔ X.Dominates T k j q := by
  by_cases hj : j = T.root
  · subst hj
    exact (dominates_root_iff (T := .star T.root) (X := X.flatten T)).trans
      dominates_root_iff.symm
  · rw [dominates_iff_dom, dom_root_iff_mem_children (ParentTree.star_parent _ _), mem_children]
    simp [hj, link_flatten hj]

/-- The melody of a slot in the flattening is its melody in the representation. -/
@[simp] theorem melody_flatten (k : ℕ) (j : ι) :
    (X.flatten T).melody (.star T.root) k j = X.melody T k j := by
  simp only [melody, word_flatten]
  exact congrArg _ (List.filter_congr fun x _ ↦ decide_eq_decide.2 dominates_flatten)

/-- Flattening twice is flattening once. -/
theorem flatten_flatten : (X.flatten T).flatten (.star T.root) = X.flatten T :=
  AR.ext rfl fun i j p q ↦ by
    simp only [link_flatten_iff, ParentTree.star_root, dominates_flatten]

variable (T X)

theorem dominates_mul : (X * Y).Dominates T k j q ↔
    k < (X.word T.root).length ∧ X.Dominates T k j q ∨
      (X.word T.root).length ≤ k ∧ (X.word j).length ≤ q ∧
        Y.Dominates T (k - (X.word T.root).length) j (q - (X.word j).length) := by
  by_cases hk : k < (X.word T.root).length
  · have h := descendants_mul_left (T := T) X Y (Fintype.card ι) (v := (T.root, k)) hk
    simp only [Dominates, h, hk, true_and, not_le.2 hk, false_and, or_false]
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hk)
    have h := descendants_mul_right (T := T) X Y (Fintype.card ι) (T.root, k')
    simp only [Dominates, h, hk, false_and, false_or, Nat.le_add_right, true_and,
      Nat.add_sub_cancel_left, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨a, b, hab, rfl, rfl⟩
      exact ⟨Nat.le_add_right _ _, by rwa [Nat.add_sub_cancel_left]⟩
    · rintro ⟨hq, hd⟩
      exact ⟨j, _, hd, rfl, by omega⟩

@[simp] theorem flatten_one : (1 : AR τ).flatten T = 1 :=
  AR.ext rfl fun i j p q ↦ by simp [flatten, link_fromRel]

/-- Flattening commutes with concatenation. -/
theorem flatten_mul : (X * Y).flatten T = X.flatten T * Y.flatten T := by
  refine AR.ext rfl fun i j p q ↦ ?_
  simp only [link_mul, link_flatten_iff, dominates_mul, word_flatten]
  constructor
  · rintro ⟨hij, ⟨rfl, ⟨hp, hd⟩ | ⟨hp, hq, hd⟩⟩ | ⟨rfl, ⟨hq, hd⟩ | ⟨hq, hp, hd⟩⟩⟩
    · exact .inl ⟨hij, .inl ⟨rfl, hd⟩⟩
    · exact .inr ⟨hp, hq, hij, .inl ⟨rfl, hd⟩⟩
    · exact .inl ⟨hij, .inr ⟨rfl, hd⟩⟩
    · exact .inr ⟨hp, hq, hij, .inr ⟨rfl, hd⟩⟩
  · rintro (⟨hij, ⟨rfl, hd⟩ | ⟨rfl, hd⟩⟩ | ⟨hp, hq, hij, ⟨rfl, hd⟩ | ⟨rfl, hd⟩⟩)
    · exact ⟨hij, .inl ⟨rfl, .inl ⟨hd.lt_length (Ne.symm hij), hd⟩⟩⟩
    · exact ⟨hij, .inr ⟨rfl, .inl ⟨hd.lt_length hij, hd⟩⟩⟩
    · exact ⟨hij, .inl ⟨rfl, .inr ⟨hp, hq, hd⟩⟩⟩
    · exact ⟨hij, .inr ⟨rfl, .inr ⟨hq, hp, hd⟩⟩⟩

/-- `AR.flatten` as a monoid homomorphism. -/
def flattenHom : AR τ →* AR τ where
  toFun X := X.flatten T
  map_one' := flatten_one T
  map_mul' := flatten_mul T

@[simp] theorem flattenHom_apply : flattenHom T X = X.flatten T := rfl

end Autosegmental.AR
