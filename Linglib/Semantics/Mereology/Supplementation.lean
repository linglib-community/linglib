module

public import Linglib.Semantics.Mereology.Overlap

/-!
# Supplementation and remainders

The decomposition principles of a part structure say what is left when a part is taken away.
Weak Supplementation says that a proper part `x` of `y` leaves a part of `y` that does not
overlap `x`, and Strong Supplementation that whatever is not part of `x` has a part that does
not overlap `x`. Remainder says that if `x` is not part of `y`, something has as parts exactly
the parts of `x` that do not overlap `y`. Remainder gives Strong Supplementation
(`Mereology.Remainder.strong`), which gives Weak Supplementation. Under Strong Supplementation
parthood is determined by overlap (`Mereology.StrongSupplementation.le_iff`), and under
Remainder a part structure with two elements has no least one (`Mereology.Remainder.no_zero`).

## References

* [cotnoir-varzi-2021], [cotnoir-varzi-2019]
-/

@[expose] public section

namespace Mereology

variable {X : Type*} [PartialOrder X] {x y : X}

variable (X) in
/-- Weak Supplementation (A.10): a proper part leaves some part of the whole that does not overlap
it. -/
def WeakSupplementation : Prop := ∀ ⦃x y : X⦄, x < y → ∃ z ≤ y, ¬ Overlap z x

variable (X) in
/-- Strong Supplementation (A.18): what is not part of `x` has a part that does not overlap `x`. -/
def StrongSupplementation : Prop := ∀ ⦃x y : X⦄, ¬ y ≤ x → ∃ z ≤ y, ¬ Overlap z x

variable (X) in
/-- Remainder (A.4 of Cotnoir and Varzi): if `x` is not part of `y`, something has as
parts exactly the parts of `x` that do not overlap `y`. -/
def Remainder : Prop := ∀ ⦃x y : X⦄, ¬ x ≤ y → ∃ z, ∀ w, w ≤ z ↔ w ≤ x ∧ ¬ Overlap w y

theorem StrongSupplementation.weak (h : StrongSupplementation X) : WeakSupplementation X :=
  fun _ _ hxy ↦ h hxy.not_ge

theorem Remainder.strong (h : Remainder X) : StrongSupplementation X := fun _ _ hyx ↦
  let ⟨z, hz⟩ := h hyx
  ⟨z, ((hz z).1 le_rfl).1, ((hz z).1 le_rfl).2⟩

theorem StrongSupplementation.le_of_forall_overlap (h : StrongSupplementation X)
    (hall : ∀ z ≤ x, Overlap z y) : x ≤ y := by
  by_contra hxy
  obtain ⟨z, hzx, hzy⟩ := h hxy
  exact hzy (hall z hzx)

/-- Under strong supplementation parthood is determined by overlap. -/
theorem StrongSupplementation.le_iff (h : StrongSupplementation X) :
    x ≤ y ↔ ∀ z, Overlap z x → Overlap z y :=
  ⟨fun hxy _ hz ↦ hz.mono le_rfl hxy, fun hall ↦ by
    by_contra hxy
    obtain ⟨z, hzx, hzy⟩ := h hxy
    exact hzy (hall z (.of_le hzx))⟩

/-- No Zero (T.2): under Remainder, if there are two things, nothing is part of everything. -/
theorem Remainder.no_zero (h : Remainder X) {a b : X} (hab : a ≠ b) : ¬ ∃ z : X, ∀ y, z ≤ y := by
  rintro ⟨z, hz⟩
  wlog hle : ¬ a ≤ b generalizing a b
  · exact this hab.symm fun hba ↦ hab (le_antisymm (not_not.1 hle) hba)
  obtain ⟨r, hr⟩ := h hle
  exact ((hr z).1 (hz r)).2 ⟨z, le_rfl, hz b⟩

end Mereology
