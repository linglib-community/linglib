module

public import Linglib.Semantics.Mereology.Supplementation
public import Mathlib.Order.Bounds.Basic

/-!
# Fusions and additive remainders

The fusion of a set of individuals is its least upper bound. Leśniewski's fusion is defined
from overlap: it has every member as a part, and each of its parts overlaps a member. Under
Strong Supplementation a Leśniewski fusion is a least upper bound (`Mereology.IsFusion.isLUB`),
and under Remainder the least upper bound of a nonempty set is its Leśniewski fusion
(`IsLUB.isFusion`). Weak Supplementation is enough for the first if any two individuals have a
fusion (`Mereology.IsFusion.isLUB_of_weak`). Goodman's fusion overlaps exactly what the members
overlap; a Leśniewski fusion is one (`Mereology.IsFusion.isGoodmanFusion`), and without further
principles a Goodman fusion need not have the members as parts.

With binary sums, Additive Remainder says that a proper part `x` of `y` has a `z` that does not
overlap `x` with `x ⊔ z = y`. It follows from Remainder, under which that `z` is unique
(`Mereology.Remainder.uniqueAdditiveRemainder`) and a part of a sum that does not overlap one
summand is part of the other (`Mereology.Remainder.le_of_le_sup`). It gives Weak
Supplementation.

## Implementation notes

Additive Remainder is the relative complement of [krifka-1989]. The Remainder Principle of
[krifka-1998] and the Unique Separation of [champollion-krifka-2016] are
`UniqueAdditiveRemainder`. Three individuals with no common part, any two of which sum to a
fourth, satisfy Additive Remainder and Strong Supplementation without uniqueness and without
Remainder (`Studies/CotnoirVarzi2021.lean`).

## TODO

Whether unique Additive Remainder implies Remainder is not settled here. An exhaustive search
finds no part structure with binary sums and at most seven elements that separates them.

## References

* [cotnoir-varzi-2021], [champollion-krifka-2016], [hovda-2009], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {X M : Type*}

section PartialOrder

variable [PartialOrder X] {x : X} {s : Set X}

/-- Leśniewski's fusion (D.13), defined from overlap: it has every member of `s` as a part,
and each of its parts overlaps a member. -/
def IsFusion (s : Set X) (x : X) : Prop := (∀ y ∈ s, y ≤ x) ∧ ∀ z ≤ x, ∃ y ∈ s, Overlap z y

/-- Under strong supplementation a fusion is a least upper bound. -/
theorem IsFusion.isLUB (hS : StrongSupplementation X) (h : IsFusion s x) : IsLUB s x :=
  ⟨h.1, fun u hu ↦ by
    by_contra hxu
    obtain ⟨z, hzx, hzu⟩ := hS hxu
    obtain ⟨y, hy, hzy⟩ := h.2 z hzx
    exact hzu (hzy.mono le_rfl (hu hy))⟩

/-- Under Weak Supplementation, if any two individuals have a fusion then a fusion is a least
upper bound ([hovda-2009]). -/
theorem IsFusion.isLUB_of_weak (hW : WeakSupplementation X)
    (hF : ∀ x y : X, ∃ z, IsFusion {x, y} z) (h : IsFusion s x) : IsLUB s x :=
  ⟨h.1, fun u hu ↦ by
    obtain ⟨a, ha⟩ := hF u x
    have hua : u ≤ a := ha.1 u (.inl rfl)
    suffices a ≤ u from (ha.1 x (.inr rfl)).trans this
    by_contra hau
    obtain ⟨b, hba, hbu⟩ := hW (lt_of_le_not_ge hua hau)
    obtain ⟨_, rfl | rfl, hbo⟩ := ha.2 b hba
    · exact hbu hbo
    · obtain ⟨c, hcb, hcx⟩ := hbo
      obtain ⟨m, hm, w, hwc, hwm⟩ := h.2 c hcx
      exact hbu ⟨w, hwc.trans hcb, hwm.trans (hu hm)⟩⟩

/-- Under Remainder the least upper bound of a nonempty set is its fusion. -/
theorem _root_.IsLUB.isFusion (hR : Remainder X) (hne : s.Nonempty) (h : IsLUB s x) :
    IsFusion s x :=
  ⟨h.1, fun z hzx ↦ by
    by_contra hno
    simp only [not_exists, not_and] at hno
    by_cases hxz : x ≤ z
    · obtain ⟨y, hy⟩ := hne
      exact hno y hy (Overlap.of_le ((h.1 hy).trans hxz)).symm
    · obtain ⟨r, hr⟩ := hR hxz
      have : x ≤ r := h.2 fun y hy ↦ (hr y).2 ⟨h.1 hy, fun ho ↦ hno y hy ho.symm⟩
      exact ((hr z).1 (hzx.trans this)).2 (.refl z)⟩

variable (X) in
/-- Products: two overlapping individuals have a greatest common part. -/
def Products : Prop := ∀ ⦃x y : X⦄, Overlap x y → ∃ z, IsGLB {x, y} z

/-- Goodman's fusion, defined from overlap alone: it overlaps exactly what the members
overlap. -/
def IsGoodmanFusion (s : Set X) (x : X) : Prop := ∀ y, Overlap y x ↔ ∃ z ∈ s, Overlap y z

/-- A Leśniewski fusion is a Goodman fusion. -/
theorem IsFusion.isGoodmanFusion (h : IsFusion s x) : IsGoodmanFusion s x := fun _ ↦
  ⟨fun ⟨w, hwy, hwx⟩ ↦ let ⟨z, hz, v, hvw, hvz⟩ := h.2 w hwx; ⟨z, hz, v, hvw.trans hwy, hvz⟩,
    fun ⟨z, hz, ho⟩ ↦ ho.mono le_rfl (h.1 z hz)⟩

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup X] {x y v w : X}

variable (X) in
/-- Additive Remainder (T.18 of Cotnoir and Varzi), the relative complement of Krifka 1989
(D 9): a proper part `x` of `y` has something that does not overlap `x` and sums with it to
`y`. -/
def AdditiveRemainder : Prop := ∀ ⦃x y : X⦄, x < y → ∃ z, ¬ Overlap z x ∧ x ⊔ z = y

variable (X) in
/-- The remainder principle of Krifka 1998 and the unique separation of Champollion and Krifka:
the remainder is unique. -/
def UniqueAdditiveRemainder : Prop := ∀ ⦃x y : X⦄, x < y → ∃! z, ¬ Overlap z x ∧ x ⊔ z = y

theorem UniqueAdditiveRemainder.additiveRemainder (h : UniqueAdditiveRemainder X) :
    AdditiveRemainder X :=
  fun _ _ hxy ↦ (h hxy).exists

theorem AdditiveRemainder.weak (h : AdditiveRemainder X) : WeakSupplementation X := fun _ _ hxy ↦
  let ⟨z, hz, e⟩ := h hxy
  ⟨z, e ▸ le_sup_right, hz⟩

/-- Under Remainder a part of a sum that does not overlap one summand is part of the other. -/
theorem Remainder.le_of_le_sup (h : Remainder X) (hw : w ≤ x ⊔ v) (hx : ¬ Overlap w x) :
    w ≤ v := by
  by_contra hwv
  obtain ⟨r, hr⟩ := h hwv
  obtain ⟨hrw, hrv⟩ := (hr r).1 le_rfl
  have hrx : ¬ Overlap r x := fun ho ↦ hx (ho.mono hrw le_rfl)
  by_cases hle : x ⊔ v ≤ r
  · exact hrx (Overlap.of_le (le_sup_left.trans hle)).symm
  · obtain ⟨u, hu⟩ := h hle
    have hxu : x ≤ u := (hu x).2 ⟨le_sup_left, fun ho ↦ hrx ho.symm⟩
    have hvu : v ≤ u := (hu v).2 ⟨le_sup_right, fun ho ↦ hrv ho.symm⟩
    exact ((hu r).1 ((hrw.trans hw).trans (sup_le hxu hvu))).2 (.refl r)

theorem Remainder.additiveRemainder (h : Remainder X) : AdditiveRemainder X := fun x y hxy ↦ by
  obtain ⟨z, hz⟩ := h hxy.not_ge
  obtain ⟨hzy, hzx⟩ := (hz z).1 le_rfl
  refine ⟨z, hzx, le_antisymm (sup_le hxy.le hzy) ?_⟩
  by_contra hle
  obtain ⟨w, hwy, hw⟩ := h.strong hle
  exact hw (.of_le (le_sup_of_le_right
    ((hz w).2 ⟨hwy, fun ho ↦ hw (ho.mono le_rfl le_sup_left)⟩)))

variable (X) in
/-- Filtration for binary sums: a part of a sum overlaps one of the summands. -/
def Filtration : Prop := ∀ ⦃x y z : X⦄, z ≤ x ⊔ y → Overlap z x ∨ Overlap z y

theorem Remainder.filtration (h : Remainder X) : Filtration X := fun _ _ _ hz ↦
  or_iff_not_imp_left.2 fun hx ↦ .of_le (h.le_of_le_sup hz hx)

/-- Under Remainder the complement of a proper part is unique. -/
theorem Remainder.uniqueAdditiveRemainder (h : Remainder X) : UniqueAdditiveRemainder X :=
    fun x y hxy ↦ by
  obtain ⟨z, hzx, hz⟩ := h.additiveRemainder hxy
  refine ⟨z, ⟨hzx, hz⟩, fun z' ⟨hz'x, hz'⟩ ↦ le_antisymm ?_ ?_⟩
  · exact h.le_of_le_sup (le_sup_right.trans (hz'.trans hz.symm).le) hz'x
  · exact h.le_of_le_sup (le_sup_right.trans (hz.trans hz'.symm).le) hzx

end SemilatticeSup

end Mereology
