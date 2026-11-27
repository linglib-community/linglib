module

public import Linglib.Logic.Modal.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Necessity and possibility as morphisms

Necessity along a relation preserves arbitrary meets of propositions and possibility arbitrary
joins, since possibility along `R` is left adjoint to necessity along its converse. This file
states the two operators as the bundled maps `ModalLogic.boxHom` and `ModalLogic.diamondHom`, so
that mathlib's `map_inf`, `map_top`, `map_sInf`, `map_sup`, `map_bot` and `map_sSup` apply to them.

## Main definitions

* `ModalLogic.boxHom`: necessity along `R`, as a map preserving arbitrary meets.
* `ModalLogic.diamondHom`: possibility along `R`, as a map preserving arbitrary joins.

## References

* [blackburn-derijke-venema-2001]
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W W' : Type*} (R : SetRel W' W)

/-- Necessity along `R`, as a map preserving arbitrary meets. -/
def boxHom : sInfHom (W → Prop) (W' → Prop) where
  toFun := □[R]
  map_sInf' s := by rw [← inv_inv (R := R), (diamond_box_gc R.inv).u_sInf, sInf_image]

/-- Possibility along `R`, as a map preserving arbitrary joins. -/
def diamondHom : sSupHom (W → Prop) (W' → Prop) where
  toFun := ◇[R]
  map_sSup' s := by rw [(diamond_box_gc R).l_sSup, sSup_image]

@[simp] theorem coe_boxHom : ⇑(boxHom R) = □[R] := rfl

@[simp] theorem coe_diamondHom : ⇑(diamondHom R) = ◇[R] := rfl

theorem boxHom_apply (p : W → Prop) : boxHom R p = □[R] p := rfl

theorem diamondHom_apply (p : W → Prop) : diamondHom R p = ◇[R] p := rfl

end ModalLogic
