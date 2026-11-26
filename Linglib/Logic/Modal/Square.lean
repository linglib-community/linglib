module

public import Linglib.Logic.Modal.Definability
public import Linglib.Logic.Aristotelian.Square
public import Mathlib.Order.Lattice

/-!
# The modal square of opposition

Along a relation `R`, the propositions $\Box p$, $\Box \neg p$, $\Diamond p$ and $\neg \Box p$
are the four corners of a square of opposition. When `R` is serial, so that necessity entails
possibility, they stand in the relations of the Aristotelian square: the two necessities are
contraries, the two possibilities subcontraries, and the diagonals contradictories.

## Main definitions

* `ModalLogic.modalSquare`: the modal square of opposition along a relation.

## Main results

* `ModalLogic.squareRelations_modalSquare`: along a serial relation the corners stand in the
  Aristotelian relations.

## References

* [carnielli-pizzi-2008]
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W : Type*} {R : SetRel W W} {p : W → Prop}

/-- The modal square of opposition along `R`, with corners $\Box p$, $\Box \neg p$, $\Diamond p$
and $\neg \Box p$. -/
def modalSquare (R : SetRel W W) (p : W → Prop) : Aristotelian.Square (W → Prop) where
  A := □[R] p
  E := □[R] pᶜ
  I := ◇[R] p
  O := (□[R] p)ᶜ

theorem squareRelations_modalSquare (R : SetRel W W) [IsSerial R] (p : W → Prop) :
    Aristotelian.SquareRelations (modalSquare R p) :=
  .of_disjoint (compl_box_compl R p).symm rfl box_disjoint_compl

end ModalLogic
