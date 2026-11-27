/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.Brace
public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Derivation
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
public import Mathlib.Algebra.NonAssoc.PreLie.Basic
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Tactic.LinearCombination

/-!
# The action of a pre-Lie algebra on its symmetric algebra

Let `L` be a right pre-Lie algebra over a commutative ring `R`. Each `X` in `L` acts on the
symmetric algebra `S(L)` by `a ↦ a * ι X + D_X a`, where `D_X` is the derivation that multiplies
one generator on the right by `X` (`RightPreLieAlgebra.derivation`). The pre-Lie identity makes
this a right action of the commutator Lie algebra of `L` (`RightPreLieAlgebra.act_act`), so it
extends to a right action of the enveloping algebra, and acting on `1` gives a linear map
`RightPreLieAlgebra.toSymmetricAlgebra` from the enveloping algebra to `S(L)`, under which
multiplying on the right by an element of `L` is its action
(`RightPreLieAlgebra.toSymmetricAlgebra_mul_ι`).

## References

* [oudom-guin-2008]
-/

@[expose] public section

noncomputable section

namespace RightPreLieAlgebra

open SymmetricAlgebra RightPreLieRing

variable (R : Type*) {L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]

/-- The derivation of the symmetric algebra that multiplies one generator on the right by `X`. -/
def derivation (X : L) : Derivation R (SymmetricAlgebra R L) (SymmetricAlgebra R L) :=
  mkDerivation (ι R L ∘ₗ LinearMap.mulRight R X)

@[simp] theorem derivation_ι (X Y : L) : derivation R X (ι R L Y) = ι R L (Y * X) := by
  simp [derivation]

theorem derivation_add (X Y : L) : derivation R (X + Y) = derivation R X + derivation R Y :=
  derivation_ext fun m ↦ by simp [mul_add]

theorem derivation_smul (r : R) (X : L) : derivation R (r • X) = r • derivation R X :=
  derivation_ext fun m ↦ by simp [mul_smul_comm]

/-- The commutator of the derivations is the derivation of the commutator, in the opposite
order. -/
theorem commutator_derivation (Y Z : L) :
    ⁅derivation R Z, derivation R Y⁆ = derivation R (Y * Z) - derivation R (Z * Y) :=
  derivation_ext fun m ↦ by
    simp only [Derivation.commutator_apply, sub_apply, derivation_ι, ← map_sub]
    refine congrArg _ ?_
    rw [sub_eq_sub_iff_add_eq_add, add_comm (m * (Y * Z))]
    exact mul_mul_add_mul_mul _ _ _

/-- The right action of `L` on its symmetric algebra: multiplication by `X` plus the derivation
of `X`. -/
def act : L →ₗ[R] Module.End R (SymmetricAlgebra R L) where
  toFun X := LinearMap.mulRight R (ι R L X) + (derivation R X : SymmetricAlgebra R L →ₗ[R] _)
  map_add' X Y := LinearMap.ext fun a ↦ by
    simp only [map_add, derivation_add, LinearMap.add_apply, LinearMap.mulRight_apply,
      Derivation.coeFn_coe, add_apply, mul_add]
    abel
  map_smul' r X := LinearMap.ext fun a ↦ by
    simp [derivation_smul, smul_add]

theorem act_apply (X : L) (a : SymmetricAlgebra R L) :
    act R X a = a * ι R L X + derivation R X a := rfl

/-- The symmetric algebra is a right module over the commutator Lie algebra of `L`:
`(a • Y) • Z - (a • Z) • Y = a • (Y * Z - Z * Y)`, here stated without subtraction. -/
theorem act_act (a : SymmetricAlgebra R L) (Y Z : L) :
    act R Z (act R Y a) + act R (Z * Y) a = act R Y (act R Z a) + act R (Y * Z) a := by
  have h := congrArg (fun D : Derivation R (SymmetricAlgebra R L) (SymmetricAlgebra R L) ↦ D a)
    (commutator_derivation R Y Z)
  simp only [Derivation.commutator_apply, sub_apply] at h
  simp only [act_apply, map_add, Derivation.leibniz, derivation_ι, smul_eq_mul]
  linear_combination h

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The action as a map of Lie algebras into the opposite of the endomorphisms of the symmetric
algebra. -/
def toEnd : L →ₗ⁅R⁆ (Module.End R (SymmetricAlgebra R L))ᵐᵒᵖ where
  toFun X := MulOpposite.op (act R X)
  map_add' X Y := by rw [map_add, MulOpposite.op_add]
  map_smul' r X := by rw [map_smul, MulOpposite.op_smul, RingHom.id_apply]
  map_lie' := fun {X Y} ↦ by
    change MulOpposite.op (act R (X * Y - Y * X)) =
      MulOpposite.op (act R X) * MulOpposite.op (act R Y) -
        MulOpposite.op (act R Y) * MulOpposite.op (act R X)
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_sub]
    refine congrArg _ (LinearMap.ext fun a ↦ ?_)
    have h := act_act R a X Y
    simp only [map_sub, LinearMap.sub_apply, mul_apply_eq_comp]
    linear_combination -h

/-- The right action of the enveloping algebra on the symmetric algebra. -/
def envelopingToEnd :
    UniversalEnvelopingAlgebra R L →ₐ[R] (Module.End R (SymmetricAlgebra R L))ᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift R (toEnd R)

/-- The enveloping algebra acting on `1` in the symmetric algebra. -/
def toSymmetricAlgebra : UniversalEnvelopingAlgebra R L →ₗ[R] SymmetricAlgebra R L where
  toFun u := (envelopingToEnd R u).unop 1
  map_add' u v := by rw [map_add, MulOpposite.unop_add, LinearMap.add_apply]
  map_smul' r u := by rw [map_smul, MulOpposite.unop_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem toSymmetricAlgebra_one :
    toSymmetricAlgebra R (1 : UniversalEnvelopingAlgebra R L) = 1 := by
  change (envelopingToEnd R 1).unop 1 = 1
  rw [map_one (envelopingToEnd R (L := L))]
  rfl

/-- Multiplying on the right by a generator is the action of that generator. -/
theorem toSymmetricAlgebra_mul_ι (u : UniversalEnvelopingAlgebra R L) (X : L) :
    toSymmetricAlgebra R (u * UniversalEnvelopingAlgebra.ι R X) =
      act R X (toSymmetricAlgebra R u) := by
  change (envelopingToEnd R (u * UniversalEnvelopingAlgebra.ι R X)).unop 1 = _
  rw [map_mul (envelopingToEnd R (L := L)), MulOpposite.unop_mul, mul_apply_eq_comp,
    envelopingToEnd, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem toSymmetricAlgebra_ι (X : L) :
    toSymmetricAlgebra R (UniversalEnvelopingAlgebra.ι R X) = ι R L X := by
  rw [← one_mul (UniversalEnvelopingAlgebra.ι R X), toSymmetricAlgebra_mul_ι,
    toSymmetricAlgebra_one, act_apply, one_mul, Derivation.map_one_eq_zero, add_zero]

theorem toSymmetricAlgebra_algebraMap (r : R) :
    toSymmetricAlgebra R (algebraMap R (UniversalEnvelopingAlgebra R L) r) =
      algebraMap R (SymmetricAlgebra R L) r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, toSymmetricAlgebra_one,
    Algebra.algebraMap_eq_smul_one]

end RightPreLieAlgebra
