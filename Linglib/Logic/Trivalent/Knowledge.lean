/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Bilattice.Involution
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The knowledge order on three-valued truth

The order of `Trivalent` is the truth order `false < undefined < true`. The knowledge order `≤ₖ`,
carried by the synonym `Know Trivalent` as in `Logic/Bilattice/Defs.lean`, orders the same values
by information instead, with `undefined` below both defined values. Kleene's negation and his
strong connectives are monotone for it, which is Kleene's regularity condition, while the Weak
Kleene connectives are not even monotone for the truth order. The knowledge order has meets but no
top: Kleene's values lack the glut of Belnap's four values, of which they are the consistent part.

## Main definitions

* the `PartialOrder`, `OrderBot` and `SemilatticeInf` instances on `Know Trivalent`.

## Main results

* `Trivalent.kLE_iff`: the knowledge order, characterized.
* `Trivalent.truthOrder_ne_knowledgeOrder`: the two orders differ.
* the `Negation Trivalent` instance, `Trivalent.inf_kLE_inf_left`, `Trivalent.sup_kLE_sup_left`:
  the Strong Kleene connectives are knowledge-monotone.
* `Trivalent.kLE_ofProp_eq_true`: Bochvar's assertion operator only adds information.
* `Trivalent.meetWeak_not_truthMono`, `Trivalent.joinWeak_not_truthMono`: the Weak Kleene ones are
  not truth-monotone.
* `Trivalent.toKnow_supervaluation`: over a nonempty family, the supervaluation is the knowledge
  meet of the classical values, so shrinking the family can only add information
  (`Trivalent.supervaluation_kLE_supervaluation`).

## References

* [kleene-1952]
-/

@[expose] public section

namespace Trivalent

open Bilattice

/-! ### The knowledge order -/

/-- The knowledge order: `undefined` is below every value, and the defined values are
incomparable. -/
protected inductive KLE : Trivalent → Trivalent → Prop
  | undefined (a) : Trivalent.KLE .undefined a
  | refl (a) : Trivalent.KLE a a

instance : DecidableRel Trivalent.KLE := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor!) | exact isFalse (by rintro ⟨_⟩)

instance : Fintype (Know Trivalent) := inferInstanceAs (Fintype Trivalent)

instance : LE (Know Trivalent) := ⟨fun a b ↦ Trivalent.KLE (ofKnow a) (ofKnow b)⟩

instance : DecidableLE (Know Trivalent) := fun a b ↦
  inferInstanceAs (Decidable (Trivalent.KLE (ofKnow a) (ofKnow b)))

instance : PartialOrder (Know Trivalent) where
  le_refl _ := KLE.refl _
  le_trans := by decide
  le_antisymm := by decide

instance : OrderBot (Know Trivalent) where
  bot := toKnow .undefined
  bot_le _ := KLE.undefined _

instance : SemilatticeInf (Know Trivalent) where
  inf a b := if a = b then a else ⊥
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

theorem kLE_iff {a b : Trivalent} : a ≤ₖ b ↔ a = .undefined ∨ a = b := by
  cases a <;> cases b <;> decide

@[simp] theorem undefined_kLE (a : Trivalent) : .undefined ≤ₖ a := KLE.undefined a

/-- The truth order and the knowledge order differ: `false` is below `undefined` in the truth
order but not in the knowledge order. -/
theorem truthOrder_ne_knowledgeOrder :
    Trivalent.false ≤ .undefined ∧ ¬ Trivalent.false ≤ₖ .undefined := by decide

/-- Kleene's negation is regular; being unary, it is the unique monotone extension of Boolean
`not`. -/
instance : Negation Trivalent := ⟨by decide⟩

/-- Strong Kleene conjunction is regular in each argument. -/
theorem inf_kLE_inf_left {a a' : Trivalent} (b : Trivalent) (h : a ≤ₖ a') : a ⊓ b ≤ₖ a' ⊓ b := by
  revert h; cases a <;> cases a' <;> cases b <;> decide

/-- Strong Kleene disjunction is regular in each argument. -/
theorem sup_kLE_sup_left {a a' : Trivalent} (b : Trivalent) (h : a ≤ₖ a') : a ⊔ b ≤ₖ a' ⊔ b := by
  revert h; cases a <;> cases a' <;> cases b <;> decide

/-- Bochvar's assertion operator only adds information. -/
theorem kLE_ofProp_eq_true (a : Trivalent) : a ≤ₖ ofProp (a = .true) := by
  cases a <;> decide

/-- Weak Kleene conjunction is not truth-monotone, since `undefined ≤ true` but
`meetWeak undefined false = undefined` is not below `meetWeak true false = false`; unlike `⊓` it is
no bilattice operation. -/
theorem meetWeak_not_truthMono :
    ¬ ∀ a a' b : Trivalent, a ≤ a' → meetWeak a b ≤ meetWeak a' b :=
  fun h ↦ absurd (h .undefined .true .false (by decide)) (by decide)

/-- Weak Kleene disjunction is not truth-monotone either. -/
theorem joinWeak_not_truthMono :
    ¬ ∀ a a' b : Trivalent, a ≤ a' → joinWeak a b ≤ joinWeak a' b :=
  fun h ↦ absurd (h .false .undefined .true (by decide)) (by decide)

/-- Over a nonempty family, the supervaluation is the knowledge meet of the classical values. -/
theorem toKnow_supervaluation {α : Type*} {s : Finset α} (P : α → Prop) [DecidablePred P]
    (hs : s.Nonempty) :
    toKnow (supervaluation s P) = s.inf' hs fun a ↦ toKnow (ofProp (P a)) := by
  cases h : supervaluation s P
  · have := ((supervaluation_eq_false_iff ..).1 h).2
    rw [Finset.inf'_congr hs rfl fun a ha ↦ by rw [ofProp_congr (iff_false_intro (this a ha)),
      ofProp_false], Finset.inf'_const]
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_undefined_iff ..).1 h
    refine (le_bot_iff.1 ?_).symm
    calc s.inf' hs (fun a ↦ toKnow (ofProp (P a)))
        ≤ toKnow (ofProp (P a)) ⊓ toKnow (ofProp (P b)) :=
          le_inf (Finset.inf'_le _ ha) (Finset.inf'_le _ hb)
      _ = ⊥ := by rw [ofProp_congr (iff_true_intro hp), ofProp_congr (iff_false_intro hn)]; rfl
  · have := (supervaluation_eq_true_iff ..).1 h
    rw [Finset.inf'_congr hs rfl fun a ha ↦ by rw [ofProp_congr (iff_true_intro (this a ha)),
      ofProp_true], Finset.inf'_const]

/-- Shrinking a family to a nonempty subfamily can only add information. Nonemptiness is needed,
since the empty family's `true` is a convention rather than a meet and a family whose members all
fail `P` has the incomparable value `false`. -/
theorem supervaluation_kLE_supervaluation {α : Type*} {s t : Finset α} (P : α → Prop)
    [DecidablePred P] (h : s ⊆ t) (hs : s.Nonempty) :
    supervaluation t P ≤ₖ supervaluation s P := by
  rw [kLE_def, toKnow_supervaluation P hs, toKnow_supervaluation P (hs.mono h)]
  exact Finset.inf'_mono _ h hs

end Trivalent
