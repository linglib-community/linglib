module

public import Linglib.Semantics.Tense.Perspective
public import Linglib.Logic.Modal.Basic

/-!
# Quantificational tense

Read quantificationally, a tense quantifies over the times its cell admits, as in the tense
logic of Prior: the past holds of a predicate at a time when the predicate holds at some earlier
time. The quantificational tense of a cell is possibility `◇` along the cell's relation
(`Tense.toSetRel`, and `Tense.Perspective.toSetRel` on intervals), so `◇[toSetRel ⟦past⟧] P t`
says that `P` held at some time before `t`, and necessity `□` along the relation holds when `P`
held at all of them. The laws of `Logic/Modal` then apply. The past and the future are converse
relations, so sometime in the one is adjoint to always in the other. A tense under a tense
entails the tense of the composed cell, and is that tense when time is dense and has no first or
last moment. The past of a past is a past as soon as time is dense, the density law of tense
logic.

## Main statements

* `Tense.diamond_toSetRel_past`: the quantificational past holds when the predicate held at
  some earlier time.
* `Tense.diamond_past_box_future_gc`, `Tense.diamond_future_box_past_gc`: sometime in the past
  is left adjoint to always in the future, and sometime in the future to always in the past.
* `Tense.diamond_diamond_toSetRel`, `Tense.diamond_toSetRel_comp`: a quantificational tense
  under another entails the quantificational tense of the composed cell, and is that tense on
  dense time without endpoints.
* `Tense.diamond_past_diamond_past`: on dense time the past of a past is a past.

## References

* [prior-1967]
-/

@[expose] public section

namespace Tense

open Semantics ModalLogic
open scoped SetRel

variable {T : Type*} {C D : Finset Ordering} {P : T → Prop} {t : T}

section LT

variable [LT T]

@[simp] theorem diamond_toSetRel_past : ◇[toSetRel ⟦past⟧] P t ↔ ∃ t' < t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_future : ◇[toSetRel ⟦future⟧] P t ↔ ∃ t' > t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_present (P : T → Prop) : ◇[toSetRel ⟦present⟧] P = P :=
  funext fun _ ↦ propext (by simp [Diamond])

@[simp] theorem box_toSetRel_past : □[toSetRel ⟦past⟧] P t ↔ ∀ t' < t, P t' := by
  simp [Box]

@[simp] theorem box_toSetRel_future : □[toSetRel ⟦future⟧] P t ↔ ∀ t' > t, P t' := by
  simp [Box]

theorem diamond_past_box_future_gc :
    GaloisConnection (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦future⟧] :=
  inv_toSetRel_past (T := T) ▸ diamond_box_gc _

theorem diamond_future_box_past_gc :
    GaloisConnection (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦past⟧] :=
  inv_toSetRel_future (T := T) ▸ diamond_box_gc _

end LT

theorem diamond_past_diamond_past [Preorder T] [DenselyOrdered T] (P : T → Prop) :
    ◇[toSetRel ⟦past⟧] (◇[toSetRel ⟦past⟧] P) = ◇[toSetRel ⟦past⟧] P := by
  rw [← diamond_comp, toSetRel_past_comp_self]

section LinearOrder

variable [LinearOrder T]

theorem diamond_diamond_toSetRel (h : ◇[toSetRel C] (◇[toSetRel D] P) t) :
    ◇[toSetRel (comp D C)] P t :=
  diamond_restrict P (toSetRel_comp_subset C D) t ((congrFun (diamond_comp _ _ P) t).mpr h)

theorem diamond_toSetRel_comp [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T]
    (C D : Finset Ordering) (P : T → Prop) :
    ◇[toSetRel (comp D C)] P = ◇[toSetRel C] (◇[toSetRel D] P) := by
  rw [← toSetRel_comp, diamond_comp]

end LinearOrder

namespace Perspective

variable [LinearOrder T] {π : NonemptyInterval T} {Q : NonemptyInterval T → Prop}

@[simp] theorem diamond_toSetRel_past :
    ◇[toSetRel ⟦past⟧] Q π ↔ ∃ r, r.Precedes π ∧ Q r := by
  simp [Diamond]

theorem diamond_past_diamond_past [DenselyOrdered T] (Q : NonemptyInterval T → Prop) :
    ◇[toSetRel ⟦past⟧] (◇[toSetRel ⟦past⟧] Q) = ◇[toSetRel ⟦past⟧] Q := by
  rw [← diamond_comp, toSetRel_past_comp_self]

end Perspective

end Tense
