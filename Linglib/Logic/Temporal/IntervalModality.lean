module

public import Linglib.Logic.Modal.Definability
public import Linglib.Logic.Temporal.IntervalAlgebra

/-!
# Possibility along interval relations

Possibility and necessity along the relation of an element of the interval algebra,
`◇[toSetRel C] Q`, are the operators of interval temporal logic: `Q` holds at some interval that
stands in `C` to the given one. Possibility along one element after another entails possibility
along their product, and is that on dense time without endpoints; possibility along an element is
left adjoint to necessity along its converse; and along the embedding of the point algebra an
operator applies to a property of intervals through its values at points.

## Main results

* `IntervalAlgebra.diamond_toSetRel_diamond_le`, `IntervalAlgebra.diamond_toSetRel_mul`:
  operators compose as the elements do.
* `IntervalAlgebra.diamond_toSetRel_box_inv_gc`: the adjunction.
* `IntervalAlgebra.diamond_toSetRel_pure`: operators of the point algebra on point intervals.

## References

* [allen-1983]
-/

public section

namespace IntervalAlgebra

open ModalLogic

variable {T : Type*} [LinearOrder T] {π : NonemptyInterval T} {Q : NonemptyInterval T → Prop}

@[simp] theorem diamond_toSetRel_precedes :
    ◇[toSetRel precedes] Q π ↔ ∃ r, r.Precedes π ∧ Q r := by
  simp [Diamond]

/-- Den on intervals: a past is a past of a past exactly when time is dense. -/
theorem diamond_precedes_den_iff :
    (◇[toSetRel precedes] : (NonemptyInterval T → Prop) → NonemptyInterval T → Prop) ≤
        ◇[toSetRel precedes] ∘ ◇[toSetRel precedes] ↔
      DenselyOrdered T :=
  diamond_den_iff.trans toSetRel_precedes_subset_comp_self_iff

/-- On dense time the past of a past is the past on intervals. -/
theorem diamond_precedes_diamond_precedes [DenselyOrdered T] (Q : NonemptyInterval T → Prop) :
    ◇[toSetRel precedes] (◇[toSetRel precedes] Q) = ◇[toSetRel precedes] Q := by
  rw [← diamond_comp, toSetRel_precedes_comp_self]

/-- Possibility along one cell after another entails possibility along their product. -/
theorem diamond_toSetRel_diamond_le (C D : IntervalAlgebra) (Q : NonemptyInterval T → Prop) :
    ◇[toSetRel C] (◇[toSetRel D] Q) ≤ ◇[toSetRel (C * D)] Q := by
  rw [← diamond_comp]
  exact diamond_le_diamond_iff.2 (toSetRel_comp_subset C D) Q

/-- On dense time without endpoints, possibility along a product of cells is possibility along
one after the other. -/
theorem diamond_toSetRel_mul [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T]
    (C D : IntervalAlgebra) (Q : NonemptyInterval T → Prop) :
    ◇[toSetRel (C * D)] Q = ◇[toSetRel C] (◇[toSetRel D] Q) := by
  rw [toSetRel_mul, diamond_comp]

/-- Possibility along a cell is left adjoint to necessity along its converse. -/
theorem diamond_toSetRel_box_inv_gc (C : IntervalAlgebra) :
    GaloisConnection (◇[toSetRel C] : (NonemptyInterval T → Prop) → _) □[toSetRel C⁻¹] :=
  toSetRel_inv (T := T) C ▸ diamond_box_gc _

/-- Along the embedding of the point algebra, possibility on intervals at a point is possibility
on points: a tense applies to an interval property through its values at points. -/
theorem diamond_toSetRel_pure (C : PointAlgebra) (Q : NonemptyInterval T → Prop) (a : T) :
    ◇[toSetRel (pure C)] Q (.pure a) ↔ ◇[PointAlgebra.toSetRel C] (fun b ↦ Q (.pure b)) a := by
  simp only [diamond_iff, mem_toSetRel, relation_mem_pure, PointAlgebra.mem_toSetRel_iff]
  constructor
  · rintro ⟨s, ⟨hs, -, hC⟩, hQ⟩
    have hs : s = .pure s.fst := NonemptyInterval.ext (Prod.ext rfl hs.symm)
    exact ⟨s.fst, hC, hs ▸ hQ⟩
  · rintro ⟨b, hC, hQ⟩
    exact ⟨.pure b, ⟨rfl, rfl, hC⟩, hQ⟩

end IntervalAlgebra
