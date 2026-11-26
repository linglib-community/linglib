module

public import Linglib.Logic.Modal.Definability

/-!
# Frames of the standard modal systems

A normal modal system is named for the axioms it adds to K, and its frames are the relations
with the properties those axioms define. The frames of S4 are the preorders, `R.IsPreorder`, and
the frames of S5 the equivalence relations, `R.IsEquiv`, both stated with mathlib's classes. This
file names the frames of the two systems of belief: K45 frames are transitive and Euclidean, and
KD45 frames are K45 frames that are serial. Every equivalence relation is a KD45 frame, so what
holds of belief holds of knowledge.

## Main definitions

* `ModalLogic.IsK45Frame`, `ModalLogic.IsKD45Frame`: the frames of K45 and KD45.

## Main results

* `ModalLogic.IsKD45Frame.of_isEquiv`: an equivalence relation is a KD45 frame.
* `ModalLogic.diamond_box_iff`: on a KD45 frame, possibly necessary is necessary.

## Implementation notes

A system gets a class when instances of it are declared, as for the belief and commitment
relations of `Discourse/Commitment/`. S5 has none of its own: `SetRel.isEquiv_iff` gives its
presentation by T and 5.

## References

* [dowty-wall-peters-1981]
* [blackburn-derijke-venema-2001]
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W : Type*} (R : SetRel W W)

/-- `R` is a *K45 frame* when it is transitive and Euclidean. -/
class IsK45Frame : Prop extends R.IsTrans, IsEuclidean R

/-- `R` is a *KD45 frame* when it is serial, transitive and Euclidean. -/
class IsKD45Frame : Prop extends IsK45Frame R, IsSerial R

/-- An equivalence relation is a KD45 frame. -/
instance (priority := 100) IsKD45Frame.of_isEquiv [R.IsEquiv] : IsKD45Frame R where

theorem diamond_box_iff [IsKD45Frame R] {p : W → Prop} {w : W} :
    ◇[R] (□[R] p) w ↔ □[R] p w :=
  ⟨box_of_diamond_box, diamond_box_of_box⟩

end ModalLogic
