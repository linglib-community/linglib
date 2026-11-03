/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Temporal.Defs

/-!
# T × W tense-modal logic: the satisfaction clauses

Historical equivalence is an equivalence relation, so `N` is an S5 necessity by modal
correspondence, and each connective of the object language has its expected truth conditions.

## References

* [thomason-1984]
* [von-kutschera-1997]
-/

@[expose] public section

namespace Temporal.TWFrame

variable {T World Atom : Type*} [Preorder T] (F : TWFrame World T) (V : Atom → T → World → Prop)

open scoped ModalLogic Denotes

instance (t : T) : (F.alt t).IsRefl := ⟨(F.sim t).iseqv.refl⟩

instance (t : T) : (F.alt t).IsSymm := ⟨fun _ _ ↦ (F.sim t).iseqv.symm⟩

instance (t : T) : (F.alt t).IsTrans := ⟨fun _ _ _ ↦ (F.sim t).iseqv.trans⟩

@[simp] theorem sat_atom (p : Atom) (t : T) (w : World) :
    F.sat V (.atom p) t w ↔ V p t w := Iff.rfl

@[simp] theorem sat_neg (a : Formula Atom) (t : T) (w : World) :
    F.sat V (.neg a) t w ↔ ¬ F.sat V a t w := Iff.rfl

@[simp] theorem sat_and (a b : Formula Atom) (t : T) (w : World) :
    F.sat V (.and a b) t w ↔ F.sat V a t w ∧ F.sat V b t w := Iff.rfl

@[simp] theorem sat_G (a : Formula Atom) (t : T) (w : World) :
    F.sat V (.G a) t w ↔ ∀ t', t < t' → F.sat V a t' w :=
  forall_congr' fun _ ↦ imp_congr_left Tense.mem_toSetRel_future

@[simp] theorem sat_H (a : Formula Atom) (t : T) (w : World) :
    F.sat V (.H a) t w ↔ ∀ t', t' < t → F.sat V a t' w :=
  forall_congr' fun _ ↦ imp_congr_left Tense.mem_toSetRel_past

@[simp] theorem sat_N (a : Formula Atom) (t : T) (w : World) :
    F.sat V (.N a) t w ↔ ∀ w', F.sim t w w' → F.sat V a t w' := Iff.rfl

@[simp] theorem sat_box (a : Formula Atom) (t : T) (w : World) :
    F.sat V (.box a) t w ↔ ∀ w', F.sat V a t w' :=
  ⟨fun h w' ↦ h w' trivial, fun h w' _ ↦ h w'⟩

@[simp] theorem sat_M (a : Formula Atom) (t : T) (w : World) :
    F.sat V a.M t w ↔ ∃ w', F.sim t w w' ∧ F.sat V a t w' := by
  simp only [Formula.M, sat_neg, sat_N, not_forall, not_not, exists_prop]

@[simp] theorem sat_dia (a : Formula Atom) (t : T) (w : World) :
    F.sat V a.dia t w ↔ ∃ w', F.sat V a t w' := by
  simp only [Formula.dia, sat_neg, sat_box, not_forall, not_not]

@[simp] theorem sat_Fut (a : Formula Atom) (t : T) (w : World) :
    F.sat V a.Fut t w ↔ ∃ t', t < t' ∧ F.sat V a t' w := by
  simp only [Formula.Fut, sat_neg, sat_G, not_forall, not_not, exists_prop]

@[simp] theorem sat_Pst (a : Formula Atom) (t : T) (w : World) :
    F.sat V a.Pst t w ↔ ∃ t', t' < t ∧ F.sat V a t' w := by
  simp only [Formula.Pst, sat_neg, sat_H, not_forall, not_not, exists_prop]

@[simp] theorem sat_imp (a b : Formula Atom) (t : T) (w : World) :
    F.sat V (a.imp b) t w ↔ (F.sat V a t w → F.sat V b t w) := by
  simp only [Formula.imp, sat_neg, sat_and, not_and, not_not]

@[simp] theorem sat_or (a b : Formula Atom) (t : T) (w : World) :
    F.sat V (a.or b) t w ↔ (F.sat V a t w ∨ F.sat V b t w) := by
  simp only [Formula.or, sat_neg, sat_and, not_and_or, not_not]

end Temporal.TWFrame
