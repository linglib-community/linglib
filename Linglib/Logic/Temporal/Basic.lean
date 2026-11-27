/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Temporal.Defs

/-!
# T × W tense-modal logic: the satisfaction clauses

Historical equivalence at a time is an equivalence relation, so historical necessity is an S5
modality. Since it is antitone in the time, a step into the future followed by a step to a
historical alternative [is a step to an alternative followed by a step into the
future](##Temporal.TWFrame.future_comp_historical_subset). Each connective of the object language
has its expected truth conditions.

## References

* [thomason-1984]
* [von-kutschera-1997]
-/

@[expose] public section

namespace Temporal.TWFrame

variable {T World Atom : Type*} [Preorder T] (F : TWFrame World T) (V : Atom → T → World → Prop)

open scoped ModalLogic SetRel

instance (t : T) : (F.alt t).IsRefl := ⟨(F.sim t).refl'⟩

instance (t : T) : (F.alt t).IsSymm := ⟨fun _ _ ↦ (F.sim t).symm'⟩

instance (t : T) : (F.alt t).IsTrans := ⟨fun _ _ _ ↦ (F.sim t).trans'⟩

/-! ### Time and historical equivalence -/

/-- A step into the future followed by a step to a historical alternative is a step to a
historical alternative followed by a step into the future. -/
theorem future_comp_historical_subset :
    Index.future ○ F.historical ⊆ F.historical ○ Index.future :=
  Index.temporal_comp_modal_subset fun _ _ h _ hp ↦
    F.antitone_sim (le_of_lt h) hp

/-! ### Satisfaction -/

section Sat

variable (a b : Formula Atom) (t : T) (w : World) {i : Index World T}

@[simp] theorem sat_atom (p : Atom) : F.sat V (.atom p) ⟨w, t⟩ ↔ V p t w := Iff.rfl

@[simp] theorem sat_neg : F.sat V (.neg a) ⟨w, t⟩ ↔ ¬ F.sat V a ⟨w, t⟩ := Iff.rfl

@[simp] theorem sat_and : F.sat V (.and a b) ⟨w, t⟩ ↔ F.sat V a ⟨w, t⟩ ∧ F.sat V b ⟨w, t⟩ :=
  Iff.rfl

@[simp] theorem sat_G : F.sat V (.G a) ⟨w, t⟩ ↔ ∀ t', t < t' → F.sat V a ⟨w, t'⟩ :=
  Index.box_temporal

@[simp] theorem sat_H : F.sat V (.H a) ⟨w, t⟩ ↔ ∀ t', t' < t → F.sat V a ⟨w, t'⟩ :=
  Index.box_temporal

@[simp] theorem sat_N : F.sat V (.N a) ⟨w, t⟩ ↔ ∀ w', F.sim t w w' → F.sat V a ⟨w', t⟩ :=
  Index.box_modal

@[simp] theorem sat_box : F.sat V (.box a) ⟨w, t⟩ ↔ ∀ w', F.sat V a ⟨w', t⟩ :=
  Index.box_modal.trans ⟨fun h w' ↦ h w' trivial, fun h w' _ ↦ h w'⟩

@[simp] theorem sat_M : F.sat V a.M ⟨w, t⟩ ↔ ∃ w', F.sim t w w' ∧ F.sat V a ⟨w', t⟩ := by
  simp only [Formula.M, sat_neg, sat_N, not_forall, not_not, exists_prop]

@[simp] theorem sat_dia : F.sat V a.dia ⟨w, t⟩ ↔ ∃ w', F.sat V a ⟨w', t⟩ := by
  simp only [Formula.dia, sat_neg, sat_box, not_forall, not_not]

@[simp] theorem sat_Fut : F.sat V a.Fut ⟨w, t⟩ ↔ ∃ t', t < t' ∧ F.sat V a ⟨w, t'⟩ := by
  simp only [Formula.Fut, sat_neg, sat_G, not_forall, not_not, exists_prop]

@[simp] theorem sat_Pst : F.sat V a.Pst ⟨w, t⟩ ↔ ∃ t', t' < t ∧ F.sat V a ⟨w, t'⟩ := by
  simp only [Formula.Pst, sat_neg, sat_H, not_forall, not_not, exists_prop]

@[simp] theorem sat_imp :
    F.sat V (a.imp b) ⟨w, t⟩ ↔ (F.sat V a ⟨w, t⟩ → F.sat V b ⟨w, t⟩) := by
  simp only [Formula.imp, sat_neg, sat_and, not_and, not_not]

@[simp] theorem sat_or : F.sat V (a.or b) ⟨w, t⟩ ↔ (F.sat V a ⟨w, t⟩ ∨ F.sat V b ⟨w, t⟩) := by
  simp only [Formula.or, sat_neg, sat_and, not_and_or, not_not]

variable {F V a}

theorem sat_N_iff_box : F.sat V (.N a) i ↔ □[F.historical] (F.sat V a) i := Iff.rfl

theorem sat_Pst_iff_diamond :
    F.sat V a.Pst i ↔ ◇[Index.past] (F.sat V a) i := by
  change ¬ □[Index.past] (fun j ↦ ¬ F.sat V a j) i ↔ _
  rw [ModalLogic.not_box]
  simp only [not_not]

end Sat

end Temporal.TWFrame
