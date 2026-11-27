module

public import Linglib.Logic.Temporal.TenseLogic
public import Linglib.Semantics.Tense.Defs

/-!
# Quantificational tense

Read quantificationally, a tense quantifies over the times its denotation admits:
`◇[toSetRel ⟦past⟧] P t`, possibility along the relation of the element of the point algebra that
the past denotes, says that `P` held at some time before `t`, and `□` that it held at all of them.
The past denotes `{.lt}`, the present the unit and the future `{.gt}`, so the laws of tense logic
(`Logic/Temporal/TenseLogic.lean`) hold of the tenses: sometime in the past is left adjoint to
always in the future, a future is a future of a future exactly when time is dense, and every time
has a future exactly when time has no last moment.

## References

* [prior-1967]
* [burgess-1984]
* [thomason-1984]
-/

public section

namespace Tense

open ModalLogic PointAlgebra
open scoped Denotes
open scoped SetRel

variable {T : Type*} {P : T → Prop} {t : T}

section LT

variable [LT T]

@[simp] theorem diamond_toSetRel_past : ◇[toSetRel ⟦past⟧] P t ↔ ∃ t' < t, P t' :=
  PointAlgebra.diamond_toSetRel_lt

@[simp] theorem diamond_toSetRel_future : ◇[toSetRel ⟦future⟧] P t ↔ ∃ t' > t, P t' :=
  PointAlgebra.diamond_toSetRel_gt

@[simp] theorem diamond_toSetRel_present (P : T → Prop) : ◇[toSetRel ⟦present⟧] P = P :=
  PointAlgebra.diamond_toSetRel_one P

@[simp] theorem box_toSetRel_past : □[toSetRel ⟦past⟧] P t ↔ ∀ t' < t, P t' :=
  PointAlgebra.box_toSetRel_lt

@[simp] theorem box_toSetRel_future : □[toSetRel ⟦future⟧] P t ↔ ∀ t' > t, P t' :=
  PointAlgebra.box_toSetRel_gt

/-- Sometime in the past is left adjoint to always in the future. -/
theorem diamond_past_box_future_gc :
    GaloisConnection (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦future⟧] :=
  PointAlgebra.diamond_lt_box_gt_gc

/-- Sometime in the future is left adjoint to always in the past. -/
theorem diamond_future_box_past_gc :
    GaloisConnection (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) □[toSetRel ⟦past⟧] :=
  PointAlgebra.diamond_gt_box_lt_gc

theorem isSerial_toSetRel_past_iff : IsSerial (toSetRel ⟦past⟧ : SetRel T T) ↔ NoMinOrder T :=
  PointAlgebra.isSerial_toSetRel_lt_iff

theorem isSerial_toSetRel_future_iff : IsSerial (toSetRel ⟦future⟧ : SetRel T T) ↔ NoMaxOrder T :=
  PointAlgebra.isSerial_toSetRel_gt_iff

theorem diamond_past_den_iff :
    (◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⟦past⟧] ∘ ◇[toSetRel ⟦past⟧] ↔
      DenselyOrdered T :=
  PointAlgebra.diamond_lt_den_iff

theorem diamond_future_den_iff :
    (◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) ≤
        ◇[toSetRel ⟦future⟧] ∘ ◇[toSetRel ⟦future⟧] ↔
      DenselyOrdered T :=
  PointAlgebra.diamond_gt_den_iff

end LT

section PartialOrder

variable [PartialOrder T]

theorem diamond_future_diamond_past_le_iff :
    (◇[toSetRel ⟦future⟧] ∘ ◇[toSetRel ⟦past⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⊤] ↔
      IsForestOrder T :=
  PointAlgebra.diamond_gt_diamond_lt_le_iff

theorem diamond_past_diamond_future_le_iff :
    (◇[toSetRel ⟦past⟧] ∘ ◇[toSetRel ⟦future⟧] : (T → Prop) → T → Prop) ≤ ◇[toSetRel ⊤] ↔
      IsForestOrder Tᵒᵈ :=
  PointAlgebra.diamond_lt_diamond_gt_le_iff

end PartialOrder

end Tense
