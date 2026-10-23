/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Dual-primitive functionals on a bialgebra

A linear functional `f` on a bialgebra `A` is primitive in the dual if `f 1 = 0` and
`f (a * b) = f a * ε b + ε a * f b`, where `ε` is the counit. The product of `A` transposes to a
comultiplication on functionals, for which `ε` is the unit, and the two conditions say that `f`
is a primitive element for it. Radford calls such an `f` an `ε:ε`-derivation of `A` and
identifies these with the primitive elements of the finite dual. Under the commutator of the
convolution product they form a Lie algebra, which Connes and Kreimer attach to the Hopf algebra
of rooted trees.

## Main definitions

* `Bialgebra.IsDualPrimitive R f`: the functional `f` is primitive in the dual.
* `Bialgebra.dualPrimitives R A`: the dual primitives, as a Lie subalgebra of the convolution
  algebra `WithConv (A →ₗ[R] R)`.

## Main results

* `Bialgebra.IsDualPrimitive.convMul_apply_mul`: the convolution product of two dual primitives
  obeys a second-order product rule, whose cross terms are symmetric in the two functionals.
* `Bialgebra.IsDualPrimitive.lie`: the commutator of two dual primitives is a dual primitive.
* `Bialgebra.IsPrimitiveElem.isDualPrimitive`: a pairing of bialgebras sends primitive elements to
  dual primitives.

## Implementation notes

`f 1 = 0` is a field, as in `Derivation` and as the counit condition is in
`Coalgebra.IsSkewPrimitiveElem`. It follows from the product rule when addition on `R` cancels
(`Bialgebra.isDualPrimitive_iff_leibniz`), but not over every semiring.

[UPSTREAM] Belongs beside `Mathlib/RingTheory/Bialgebra/Primitive.lean`, as the dual of
`Bialgebra.IsPrimitiveElem`.

## References

* [radford-2012]
* [connes-kreimer-1998]
-/

@[expose] public section

open Coalgebra WithConv

namespace Bialgebra

variable {R A : Type*}

section CommSemiring

variable [CommSemiring R] [Semiring A] [Bialgebra R A] {f g : A →ₗ[R] R} {a b : A}

variable (R) in
/-- A linear functional `f` on a bialgebra is primitive in the dual if `f 1 = 0` and
`f (a * b) = f a * ε b + ε a * f b`, where `ε` is the counit. -/
@[mk_iff]
structure IsDualPrimitive (f : A →ₗ[R] R) : Prop where
  /-- A dual primitive vanishes at `1`. -/
  map_one_eq_zero : f 1 = 0
  /-- A dual primitive obeys the product rule of a derivation at the counit. -/
  leibniz (a b : A) : f (a * b) = f a * counit b + counit a * f b

namespace IsDualPrimitive

@[simp] theorem zero : IsDualPrimitive R (0 : A →ₗ[R] R) := by simp [isDualPrimitive_iff]

theorem add (hf : IsDualPrimitive R f) (hg : IsDualPrimitive R g) : IsDualPrimitive R (f + g) where
  map_one_eq_zero := by simp [hf.map_one_eq_zero, hg.map_one_eq_zero]
  leibniz a b := by simp [hf.leibniz, hg.leibniz, add_mul, mul_add, add_add_add_comm]

theorem smul (hf : IsDualPrimitive R f) (r : R) : IsDualPrimitive R (r • f) where
  map_one_eq_zero := by simp [hf.map_one_eq_zero]
  leibniz a b := by simp [hf.leibniz, mul_add, mul_assoc, mul_left_comm]

theorem map_mul_eq_zero (hf : IsDualPrimitive R f) (ha : counit (R := R) a = 0)
    (hb : counit (R := R) b = 0) : f (a * b) = 0 := by
  simp [hf.leibniz, ha, hb]

/-- The convolution product of two dual primitives obeys a second-order product rule. Its cross
terms `f a * g b + g a * f b` are symmetric in `f` and `g`, so they cancel in the commutator. -/
theorem convMul_apply_mul (hf : IsDualPrimitive R f) (hg : IsDualPrimitive R g) (a b : A) :
    (toConv f * toConv g) (a * b) =
      (toConv f * toConv g) a * counit b + f a * g b + g a * f b +
        counit a * (toConv f * toConv g) b := by
  trans (toConv f * toConv g) a * (1 * 1 : WithConv (A →ₗ[R] R)) b +
      (toConv f * 1) a * (1 * toConv g) b + (1 * toConv g) a * (toConv f * 1) b +
        (1 * 1 : WithConv (A →ₗ[R] R)) a * (toConv f * toConv g) b
  · simp only [((ℛ R a).mul (ℛ R b)).convMul_apply, (ℛ R a).convMul_apply, (ℛ R b).convMul_apply,
      Finset.sum_mul_sum, ← Finset.sum_add_distrib, Repr.mul_index, Repr.mul_left, Repr.mul_right,
      Finset.sum_product, hf.leibniz, hg.leibniz, LinearMap.convOne_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  · simp

end IsDualPrimitive

theorem isDualPrimitive_iff_leibniz [IsCancelAdd R] :
    IsDualPrimitive R f ↔ ∀ a b, f (a * b) = f a * counit b + counit a * f b :=
  ⟨fun hf ↦ hf.leibniz, fun h ↦ ⟨by simpa using h 1 1, h⟩⟩

/-- A pairing of bialgebras that transposes the product of `A` to the comultiplication of `B`, and
the units to the counits, sends the primitive elements of `B` to dual primitives of `A`. -/
theorem IsPrimitiveElem.isDualPrimitive {B : Type*} [Semiring B] [Bialgebra R B] {b : B}
    (hb : IsPrimitiveElem R b) {p : B →ₗ[R] A →ₗ[R] R} (h_one : ∀ a, p 1 a = counit a)
    (h_counit : ∀ b, p b 1 = counit b)
    (h_mul : ∀ a a', toConv (p.flip (a * a')) = toConv (p.flip a) * toConv (p.flip a')) :
    IsDualPrimitive R (p b) where
  map_one_eq_zero := (h_counit b).trans hb.counit_eq_zero
  leibniz a a' := by
    simpa [hb.comul_eq_tmul_add_tmul, h_one, add_comm] using congr($(h_mul a a') b)

end CommSemiring

section CommRing

variable [CommRing R] [Semiring A] [Bialgebra R A] {f g : A →ₗ[R] R}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The commutator of two dual primitives under the convolution product is a dual primitive. -/
theorem IsDualPrimitive.lie (hf : IsDualPrimitive R f) (hg : IsDualPrimitive R g) :
    IsDualPrimitive R (⁅toConv f, toConv g⁆ : WithConv (A →ₗ[R] R)).ofConv where
  map_one_eq_zero := by
    simp [Ring.lie_def, Algebra.TensorProduct.one_def, hf.map_one_eq_zero, hg.map_one_eq_zero]
  leibniz a b := by
    simp only [Ring.lie_def, ofConv_sub, LinearMap.sub_apply]
    rw [hf.convMul_apply_mul hg, hg.convMul_apply_mul hf]
    ring

variable (R A) in
/-- The dual primitives of a bialgebra, as a Lie subalgebra of its convolution algebra of linear
functionals under the commutator bracket. -/
def dualPrimitives : LieSubalgebra R (WithConv (A →ₗ[R] R)) where
  carrier := {f | IsDualPrimitive R f.ofConv}
  zero_mem' := .zero
  add_mem' hf hg := hf.add hg
  smul_mem' r _ hf := hf.smul r
  lie_mem' hf hg := hf.lie hg

@[simp] theorem mem_dualPrimitives {f : WithConv (A →ₗ[R] R)} :
    f ∈ dualPrimitives R A ↔ IsDualPrimitive R f.ofConv := .rfl

end CommRing

end Bialgebra
