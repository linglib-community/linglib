/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Defs

/-!
# Modalities along a pair of relations

A possibility `◇[S]` and a necessity `□[R]` along two unrelated relations interact through the
schema `p → □[R] ◇[S] p`: it is valid exactly when the converse of `R` lies in `S`. The two
operators are adjoint exactly when `S` is the converse of `R`. With `R` the relation of the future
operators and `S` that of the past operators, these are the two interaction axioms of the minimal
tense logic, which together say that past and future run along converse relations
([goranko-2023]).

## Main results

* `ModalLogic.id_le_box_comp_diamond_iff`: `p → □[R] ◇[S] p` is valid iff `R.inv ⊆ S`.
* `ModalLogic.gc_diamond_box_iff`: `◇[S]` is left adjoint to `□[R]` iff `R.inv = S`.

## References

* [goranko-2023]
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W W' : Type*} {R : SetRel W W'} {S : SetRel W' W}

/-- The schema `p → □[R] ◇[S] p` defines inclusion of the converse of `R` in `S`. Axiom B is the
case of one relation. -/
theorem id_le_box_comp_diamond_iff : id ≤ Box R ∘ Diamond S ↔ R.inv ⊆ S where
  mp h := fun ⟨v, w⟩ hvw ↦ match h (· = w) w rfl v hvw with | ⟨_, hu, rfl⟩ => hu
  mpr h _ w hp _ hv := ⟨w, h hv, hp⟩

/-- Both interaction schemas are valid exactly when the two relations are converse. -/
theorem id_le_box_comp_diamond_and_iff :
    id ≤ Box R ∘ Diamond S ∧ id ≤ Box S ∘ Diamond R ↔ R.inv = S := by
  rw [id_le_box_comp_diamond_iff, id_le_box_comp_diamond_iff]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ h₁.antisymm fun _ hx ↦ h₂ hx, by rintro rfl; exact ⟨subset_rfl, subset_rfl⟩⟩

/-- A possibility is left adjoint to a necessity exactly when their relations are converse. -/
theorem gc_diamond_box_iff : GaloisConnection (Diamond S) (Box R) ↔ R.inv = S := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact diamond_box_gc _⟩
  have key (p : W → Prop) : Diamond R.inv p = Diamond S p :=
    le_antisymm ((diamond_box_gc R.inv).l_le (h.le_u_l p))
      (h.l_le ((diamond_box_gc R.inv).le_u_l p))
  exact (diamond_le_diamond_iff.1 fun p ↦ (key p).le).antisymm
    (diamond_le_diamond_iff.1 fun p ↦ (key p).ge)

end ModalLogic
