module

public import Linglib.Logic.Modal.Definability

/-!
# Frames of the standard modal systems

A normal modal system is named for the axioms it adds to K, and its frames are the relations
with the properties those axioms define: S5 frames are reflexive and Euclidean, KD45 frames
serial, transitive and Euclidean, K45 frames transitive and Euclidean, and KTB frames reflexive
and symmetric. S5 is the logic of Montague's necessity operators and of knowledge, and KD45 the
usual logic of belief.

## Main definitions

* `ModalLogic.IsS5Frame`, `ModalLogic.IsKD45Frame`, `ModalLogic.IsK45Frame`,
  `ModalLogic.IsKTBFrame`: the frames of the four systems.

## Main results

* `ModalLogic.diamond_box_iff`: on a KD45 frame, possibly necessary is necessary.

## References

* [dowty-wall-peters-1981]
* [blackburn-derijke-venema-2001]
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W : Type*} (R : SetRel W W)

/-- `R` is an *S5 frame* when it is reflexive and Euclidean. -/
class IsS5Frame : Prop extends R.IsRefl, IsEuclidean R

/-- `R` is a *KD45 frame* when it is serial, transitive and Euclidean. -/
class IsKD45Frame : Prop extends IsSerial R, R.IsTrans, IsEuclidean R

/-- `R` is a *K45 frame* when it is transitive and Euclidean. -/
class IsK45Frame : Prop extends R.IsTrans, IsEuclidean R

/-- `R` is a *KTB frame* when it is reflexive and symmetric. -/
class IsKTBFrame : Prop extends R.IsRefl, R.IsSymm

theorem diamond_box_iff [IsKD45Frame R] {p : W → Prop} {w : W} :
    ◇[R] (□[R] p) w ↔ □[R] p w :=
  ⟨box_of_diamond_box, diamond_box_of_box⟩

end ModalLogic
