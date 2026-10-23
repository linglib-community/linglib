module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Linglib.Semantics.Degree.Measure.Dimension

/-!
# The quantity calculus

A quantity is a magnitude together with a dimension: `0.9 g` is a magnitude in the
dimension of mass, `0.9 g/mL` one in the dimension of density, and `9` is a pure number,
a magnitude in the identity dimension. This file sets up the quantity calculus that
measure-phrase semantics computes in. Dimensions are the group `QuantityDimension`;
quantities are pairs `K × QuantityDimension` of a magnitude and a dimension and
multiply and divide componentwise, so that dividing two quantities of one dimension yields a
pure number.

## Main definitions

* `Quantity`, `Quantity.pure`: quantities and pure numbers.

## Main statements

* `Quantity.isUnit_iff`: a quantity is invertible exactly when its magnitude is nonzero, so the
  division lemmas of mathlib's `IsUnit` API apply to it.

## References

* [de-boer-1995]
* [coppock-2021]
-/

@[expose] public section

namespace Degree

/-- A quantity, a magnitude in `K` with a dimension. Quantities multiply and divide
componentwise. -/
abbrev Quantity (K : Type*) := K × QuantityDimension

namespace Quantity

variable {K : Type*}

/-- The pure number `n`, a quantity `(n, 1)` of the identity dimension. -/
def pure (n : K) : Quantity K := (n, 1)

@[simp] theorem pure_fst (n : K) : (pure n).1 = n := rfl
@[simp] theorem pure_snd (n : K) : (pure n).2 = 1 := rfl

/-- A quantity is invertible exactly when its magnitude is, since every dimension is. -/
theorem isUnit_iff [CommGroupWithZero K] {q : Quantity K} : IsUnit q ↔ q.1 ≠ 0 := by
  simp [Prod.isUnit_iff, Group.isUnit, isUnit_iff_ne_zero]

end Quantity

end Degree
