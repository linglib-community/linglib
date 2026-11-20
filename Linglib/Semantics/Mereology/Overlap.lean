module

public import Linglib.Core.Order.WithBot

/-!
# Overlap

Two individuals of a part structure overlap if they have a common part,
`Overlap x y ↔ ∃ z, z ≤ x ∧ z ≤ y`. This is the definition of [krifka-1989],
[champollion-krifka-2016] and [cotnoir-varzi-2021], for part structures with no null element,
where everything overlaps itself. Once a least element is adjoined, overlap is the negation of
`Disjoint` (`Mereology.overlap_iff_not_disjoint_coe`), and the elements of an order with a
least element other than that one overlap iff they are not disjoint
(`Mereology.overlap_subtype_ne_bot`), the solid disjointness of [cotnoir-varzi-2021].

## References

* [champollion-krifka-2016], [cotnoir-varzi-2021], [krifka-1989]
-/

@[expose] public section

namespace Mereology

variable {X B : Type*}

section PartialOrder

variable [PartialOrder X] {x y x' y' : X}

/-- Two individuals overlap if they have a common part. -/
def Overlap (x y : X) : Prop := ∃ z, z ≤ x ∧ z ≤ y

theorem Overlap.refl (x : X) : Overlap x x := ⟨x, le_rfl, le_rfl⟩

theorem Overlap.symm : Overlap x y → Overlap y x := fun ⟨z, hx, hy⟩ ↦ ⟨z, hy, hx⟩

theorem Overlap.mono (hx : x ≤ x') (hy : y ≤ y') : Overlap x y → Overlap x' y' :=
  fun ⟨z, h₁, h₂⟩ ↦ ⟨z, h₁.trans hx, h₂.trans hy⟩

theorem Overlap.of_le (h : x ≤ y) : Overlap x y := ⟨x, le_rfl, h⟩

/-- Overlap is non-disjointness once a null element is adjoined. -/
theorem overlap_iff_not_disjoint_coe : Overlap x y ↔ ¬ Disjoint (x : WithBot X) y := by
  simp [WithBot.disjoint_coe, Overlap]

end PartialOrder

/-- Solid disjointness (D.37): the elements other than `⊥` overlap iff they are not disjoint. -/
theorem overlap_subtype_ne_bot [SemilatticeInf B] [OrderBot B] {a b : {x : B // x ≠ ⊥}} :
    Overlap a b ↔ ¬ Disjoint (a : B) b :=
  ⟨fun ⟨z, hza, hzb⟩ h ↦ z.2 (le_bot_iff.1 (h hza hzb)),
    fun h ↦ ⟨⟨(a : B) ⊓ b, fun h0 ↦ h (disjoint_iff.2 h0)⟩, inf_le_left, inf_le_right⟩⟩

end Mereology
