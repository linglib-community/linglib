/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Linglib.Core.Order.Flat
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The knowledge order on three-valued truth

The order of `SignType` is the truth order `-1 < 0 < 1`. The flat domain `Flat Bool` orders the
same three values by information instead, with the undefined value `0` below both `1` and `-1`.
Kleene's strong connectives are monotone for this knowledge order, which is Kleene's regularity
condition, while the Weak Kleene connectives are not even monotone for the truth order.
`Flat Bool` has a knowledge meet but only a partial knowledge join: the three values lack the glut
of Belnap's four values, of which they are the consistent part.

## Main definitions

* `SignType.toFlat`, `SignType.equivFlatBool`: `0 ↦ ⊥`, `1 ↦ true`, `-1 ↦ false`.

## Main results

* `SignType.truthOrder_ne_knowledgeOrder`: the two orders differ.
* `SignType.toFlat_neg_mono`, `SignType.toFlat_inf_mono_left`, `SignType.toFlat_sup_mono_left`:
  the Strong Kleene connectives are knowledge-monotone.
* `SignType.toFlat_le_toFlat_ofProp_eq_one`: Bochvar's assertion operator only adds information.
* `SignType.meetWeak_not_truthMono`, `SignType.joinWeak_not_truthMono`: the Weak Kleene ones are
  not truth-monotone.
* `SignType.toFlat_supervaluation`: over a nonempty family, the supervaluation is the knowledge
  meet of the classical values, so shrinking the family can only add information
  (`SignType.toFlat_supervaluation_mono`).

## References

* [kleene-1952]
-/

@[expose] public section

namespace SignType

section KnowledgeOrder

/-- The value in the flat domain sends `0` to `⊥`, and `1` and `-1` to `true` and `false`. -/
def toFlat : SignType → Flat Bool
  | .zero => none
  | .pos => some Bool.true
  | .neg => some Bool.false

/-- The inverse of `toFlat`. -/
def ofFlat : Flat Bool → SignType
  | none => 0
  | some Bool.true => 1
  | some Bool.false => -1

/-- `SignType` and the flat domain `Flat Bool` are the same three values. -/
def equivFlatBool : SignType ≃ Flat Bool where
  toFun := toFlat
  invFun := ofFlat
  left_inv a := by cases a <;> rfl
  right_inv x := by cases x with | bot => rfl | coe b => cases b <;> rfl

/-- The truth order and the knowledge order differ, since `-1 ≤ 0` in the truth order but the
defined value `-1` is not below the undefined `0 = ⊥` in the knowledge order. -/
theorem truthOrder_ne_knowledgeOrder :
    (-1 : SignType) ≤ 0 ∧ ¬ toFlat (-1) ≤ toFlat 0 := by decide

/-- Strong Kleene negation is regular; being unary, it is the unique monotone extension of
Boolean `not`. -/
theorem toFlat_neg_mono {a b : SignType} (h : toFlat a ≤ toFlat b) :
    toFlat (-a) ≤ toFlat (-b) := by
  cases a <;> cases b <;> revert h <;> decide

/-- Strong Kleene conjunction is regular in each argument. -/
theorem toFlat_inf_mono_left {a a' : SignType} (b : SignType)
    (h : toFlat a ≤ toFlat a') : toFlat (a ⊓ b) ≤ toFlat (a' ⊓ b) := by
  cases a <;> cases a' <;> cases b <;> revert h <;> decide

/-- Strong Kleene disjunction is regular in each argument. -/
theorem toFlat_sup_mono_left {a a' : SignType} (b : SignType)
    (h : toFlat a ≤ toFlat a') : toFlat (a ⊔ b) ≤ toFlat (a' ⊔ b) := by
  cases a <;> cases a' <;> cases b <;> revert h <;> decide

/-- Bochvar's assertion operator only adds information. -/
theorem toFlat_le_toFlat_ofProp_eq_one (a : SignType) : toFlat a ≤ toFlat (ofProp (a = 1)) := by
  cases a <;> decide

theorem eq_of_toFlat_le {a b : SignType} (h : toFlat a ≤ toFlat b) (ha : a ≠ 0) : a = b := by
  cases a <;> cases b <;> revert h ha <;> decide

/-- Weak Kleene conjunction is not truth-monotone, since `0 ≤ 1` but `meetWeak 0 (-1) = 0` is not
below `meetWeak 1 (-1) = -1`; unlike `⊓` it is no bilattice operation. -/
theorem meetWeak_not_truthMono :
    ¬ ∀ a a' b : SignType, a ≤ a' → meetWeak a b ≤ meetWeak a' b :=
  fun h ↦ absurd (h 0 1 (-1) (by decide)) (by decide)

/-- Weak Kleene disjunction is not truth-monotone either. -/
theorem joinWeak_not_truthMono :
    ¬ ∀ a a' b : SignType, a ≤ a' → joinWeak a b ≤ joinWeak a' b :=
  fun h ↦ absurd (h (-1) 0 1 (by decide)) (by decide)

/-- Over a nonempty family, the supervaluation is the knowledge meet of the classical values. -/
theorem toFlat_supervaluation {α : Type*} {s : Finset α} (P : α → Prop) [DecidablePred P]
    (hs : s.Nonempty) :
    toFlat (supervaluation s P) = s.inf' hs fun a ↦ (decide (P a) : Flat Bool) := by
  cases h : supervaluation s P
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_zero_iff ..).1 h
    refine (le_bot_iff.1 ?_).symm
    calc s.inf' hs (fun a ↦ (decide (P a) : Flat Bool))
        ≤ (decide (P a) : Flat Bool) ⊓ (decide (P b) : Flat Bool) :=
          le_inf (Finset.inf'_le _ ha) (Finset.inf'_le _ hb)
      _ = ⊥ := by simp [hp, hn]
  · have := ((supervaluation_eq_neg_one_iff ..).1 h).2
    rw [Finset.inf'_congr hs rfl fun a ha ↦ by rw [decide_eq_false (this a ha)],
      Finset.inf'_const]; rfl
  · have := (supervaluation_eq_one_iff ..).1 h
    rw [Finset.inf'_congr hs rfl fun a ha ↦ by rw [decide_eq_true (this a ha)],
      Finset.inf'_const]; rfl

/-- Shrinking a family to a nonempty subfamily can only add information. Nonemptiness is needed,
since the empty family's `1` is a convention rather than a meet and a family whose members all fail
`P` has the incomparable value `-1`. -/
theorem toFlat_supervaluation_mono {α : Type*} {s t : Finset α} (P : α → Prop)
    [DecidablePred P] (h : s ⊆ t) (hs : s.Nonempty) :
    toFlat (supervaluation t P) ≤ toFlat (supervaluation s P) := by
  rw [toFlat_supervaluation P hs, toFlat_supervaluation P (hs.mono h)]
  exact Finset.inf'_mono _ h hs

end KnowledgeOrder

end SignType
