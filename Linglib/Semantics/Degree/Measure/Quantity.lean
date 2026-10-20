module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Basic
public import Linglib.Semantics.Degree.Measure.Dimensioned

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
* `DimensionedMeasure.quantity`: the value of a measure function as a quantity.

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

variable [CommGroupWithZero K]

/-- Scaling both quantities by the same nonzero pure number leaves their quotient unchanged, so
that `0.1 kg / L = 0.1 g / mL`. -/
theorem pure_mul_div_pure_mul {k : K} (hk : k ≠ 0) (q r : Quantity K) :
    pure k * q / (pure k * r) = q / r := by
  ext <;> simp [mul_div_mul_left _ _ hk]

/-- `a / b = q / r ↔ a = q * (b / r)` when the magnitudes of `b` and `r` are nonzero. -/
theorem div_eq_div_iff_eq_mul_div {a b q r : Quantity K} (hb : b.1 ≠ 0) (hr : r.1 ≠ 0) :
    a / b = q / r ↔ a = q * (b / r) := by
  rw [Prod.ext_iff, Prod.ext_iff]
  simp only [Prod.fst_div, Prod.snd_div, Prod.fst_mul, Prod.snd_mul, ← mul_div_assoc]
  rw [div_eq_div_iff hb hr, eq_div_iff hr, div_eq_div_iff_mul_eq_mul, eq_div_iff_mul_eq']

/-- The quotient of two quantities of one dimension is the pure number `n` with `n ⋅ q = a`. -/
theorem div_eq_pure_iff {a q : Quantity K} {n : K} (hq : q.1 ≠ 0) (h : a.2 = q.2) :
    a / q = pure n ↔ pure n * q = a := by
  simp only [Prod.ext_iff, Prod.fst_div, Prod.snd_div, Prod.fst_mul, Prod.snd_mul, pure_fst,
    pure_snd, h, div_self', one_mul, and_true, div_eq_iff hq]
  exact eq_comm

end Quantity

variable {E : Type*} {K : Type}

/-- The value of `μ` at `x` as a quantity of `μ`'s dimension. -/
def DimensionedMeasure.quantity (μ : DimensionedMeasure E K) (x : E) : Quantity K :=
  (μ x, μ.dimension)

@[simp] theorem DimensionedMeasure.quantity_fst (μ : DimensionedMeasure E K) (x : E) :
    (μ.quantity x).1 = μ x := rfl

@[simp] theorem DimensionedMeasure.quantity_snd (μ : DimensionedMeasure E K) (x : E) :
    (μ.quantity x).2 = μ.dimension := rfl

end Degree
