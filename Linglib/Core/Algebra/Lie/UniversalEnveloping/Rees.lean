/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.Algebra.Rees
public import Linglib.Core.Algebra.Lie.UniversalEnveloping.Filtration
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The symmetric algebra maps onto the graded enveloping algebra

Two elements of a Lie algebra `L` commute in its enveloping algebra up to an element of `L`, so a
product of `n + 1` elements of `L` depends, modulo products of at most `n`, only on its image in
the symmetric algebra. This is `UniversalEnvelopingAlgebra.mkAlgHom_mem_of_algHom_eq_zero`: a
homogeneous tensor of degree `n + 1` whose image in the symmetric algebra is zero has image in
`UniversalEnvelopingAlgebra.filtration R L n`. It is the statement that the symmetric algebra
maps onto the associated graded algebra of the enveloping algebra, the half of the
Poincaré–Birkhoff–Witt theorem that holds for every Lie algebra.

## Implementation notes

The associated graded algebra is not constructed. The statement is read off the Rees algebra
`UniversalEnvelopingAlgebra.rees` of the filtration: sending `x` to `ι x * X` is an algebra
homomorphism `UniversalEnvelopingAlgebra.toRees` from the tensor algebra into it, under which a
homogeneous tensor `t` of degree `n` goes to `mkAlgHom t * X ^ n`. Modulo `X` times the Rees algebra the
images of the elements of `L` commute, so the homomorphism factors through the symmetric algebra.

`[UPSTREAM]` candidate.
-/

@[expose] public section

noncomputable section

namespace UniversalEnvelopingAlgebra

open Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The elements of `L` in the enveloping algebra, as a submodule. -/
local notation "M_U" =>
  LinearMap.range ((ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L) : L →ₗ[R] _)

/-- The Rees algebra of the enveloping algebra: the polynomials whose coefficient of `X ^ k` is
in `filtration R L k`. -/
def rees : Subalgebra R (UniversalEnvelopingAlgebra R L)[X] := Submodule.rees M_U

theorem mem_rees {p : (UniversalEnvelopingAlgebra R L)[X]} :
    p ∈ rees R L ↔ ∀ k, p.coeff k ∈ filtration R L k := Iff.rfl

theorem C_ι_mul_X_mem_rees (x : L) : C (ι R x) * X ∈ rees R L :=
  Submodule.C_mul_X_mem_rees ⟨x, rfl⟩

/-- The homomorphism from the tensor algebra to the polynomials over the enveloping algebra that
sends `x` to `ι x * X`. -/
def toRees : TensorAlgebra R L →ₐ[R] (UniversalEnvelopingAlgebra R L)[X] :=
  TensorAlgebra.lift R
    { toFun := fun x ↦ C (ι R x) * X
      map_add' := fun x y ↦ by rw [map_add, C_add, add_mul]
      map_smul' := fun r x ↦ by rw [map_smul, ← smul_C, smul_mul_assoc, RingHom.id_apply] }

@[simp] theorem toRees_ι (x : L) : toRees R L (TensorAlgebra.ι R x) = C (ι R x) * X :=
  TensorAlgebra.lift_ι_apply _ x

theorem toRees_mem_rees (a : TensorAlgebra R L) : toRees R L a ∈ rees R L := by
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact (rees R L).algebraMap_mem r
  | ι x => rw [toRees_ι]; exact C_ι_mul_X_mem_rees R L x
  | mul a b ha hb => rw [map_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- A homogeneous tensor of degree `n` goes to its image in the enveloping algebra times
`X ^ n`. -/
theorem toRees_of_mem_pow {n : ℕ} {t : TensorAlgebra R L}
    (ht : t ∈ LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ n) :
    toRees R L t = C (mkAlgHom R L t) * X ^ n := by
  induction ht using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, pow_zero, mul_one, Polynomial.algebraMap_apply]
  | add x y i hx hy ihx ihy => rw [map_add, map_add, C_add, add_mul, ihx, ihy]
  | mul_mem i x hx ih m hm =>
    obtain ⟨y, rfl⟩ := hm
    rw [map_mul, map_mul, ih, toRees_ι, C_mul, mul_assoc, ← mul_assoc (X ^ i), X_pow_mul_C,
      mul_assoc, ← pow_succ, ← mul_assoc]
    rfl

/-! ### The Rees algebra modulo `X` -/

/-- Two tensors are congruent when their images differ by `X` times an element of the Rees
algebra. The quotient is the associated graded algebra of the enveloping algebra. -/
def reesCon : RingCon (TensorAlgebra R L) where
  r a b := ∃ q ∈ rees R L, toRees R L a - toRees R L b = X * q
  iseqv :=
    ⟨fun a ↦ ⟨0, zero_mem _, by rw [sub_self, mul_zero]⟩,
      fun ⟨q, hq, h⟩ ↦ ⟨-q, neg_mem hq, by rw [mul_neg, ← h, neg_sub]⟩,
      fun ⟨q, hq, h⟩ ⟨q', hq', h'⟩ ↦
        ⟨q + q', add_mem hq hq', by rw [mul_add, ← h, ← h', sub_add_sub_cancel]⟩⟩
  add' := fun ⟨q, hq, h⟩ ⟨q', hq', h'⟩ ↦
    ⟨q + q', add_mem hq hq', by rw [map_add, map_add, mul_add, ← h, ← h', add_sub_add_comm]⟩
  mul' := fun {a b c d} ⟨q, hq, h⟩ ⟨q', hq', h'⟩ ↦
    ⟨q * toRees R L c + toRees R L b * q',
      add_mem (mul_mem hq (toRees_mem_rees R L c)) (mul_mem (toRees_mem_rees R L b) hq'), by
      rw [map_mul, map_mul, mul_add, ← mul_assoc, ← h, ← mul_assoc, (commute_X (toRees R L b)).eq,
        mul_assoc, ← h', sub_mul, mul_sub]
      abel⟩

theorem reesCon_def {a b : TensorAlgebra R L} :
    reesCon R L a b ↔ ∃ q ∈ rees R L, toRees R L a - toRees R L b = X * q := Iff.rfl

private theorem C_mul_X_mul_C_mul_X (a b : UniversalEnvelopingAlgebra R L) :
    C a * X * (C b * X) = X * (C (a * b) * X) := by
  rw [← (commute_X (C a)).eq, mul_assoc, ← mul_assoc (C a), ← C_mul]

/-- Two elements of `L` commute modulo `X` times the Rees algebra. -/
theorem reesCon_ι_mul_ι (x y : L) :
    reesCon R L (TensorAlgebra.ι R x * TensorAlgebra.ι R y)
      (TensorAlgebra.ι R y * TensorAlgebra.ι R x) := by
  refine ⟨C (ι R ⁅x, y⁆) * X, C_ι_mul_X_mem_rees R L _, ?_⟩
  rw [map_mul, map_mul, toRees_ι, toRees_ι, C_mul_X_mul_C_mul_X, C_mul_X_mul_C_mul_X, ← mul_sub,
    ← sub_mul, ← C_sub, LieHom.map_lie, Ring.lie_def]

/-- The quotient map from the tensor algebra. -/
def reesMk : TensorAlgebra R L →ₐ[R] (reesCon R L).Quotient := (reesCon R L).mkₐ R

theorem reesMk_surjective : Function.Surjective (reesMk R L) := Quotient.mk_surjective

theorem reesMk_eq_zero_iff {t : TensorAlgebra R L} :
    reesMk R L t = 0 ↔ ∃ q ∈ rees R L, toRees R L t = X * q := by
  change ((t : (reesCon R L).Quotient) = ((0 : TensorAlgebra R L) : (reesCon R L).Quotient)) ↔ _
  rw [RingCon.eq, reesCon_def, map_zero, sub_zero]

theorem commute_reesMk (a b : TensorAlgebra R L) : Commute (reesMk R L a) (reesMk R L b) := by
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_left r _
  | ι x =>
    induction b using TensorAlgebra.induction with
    | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right r _
    | ι y =>
      have h : reesMk R L (TensorAlgebra.ι R x * TensorAlgebra.ι R y) =
          reesMk R L (TensorAlgebra.ι R y * TensorAlgebra.ι R x) :=
        (RingCon.eq _).mpr (reesCon_ι_mul_ι R L x y)
      rwa [map_mul, map_mul] at h
    | mul b c hb hc => rw [map_mul]; exact hb.mul_right hc
    | add b c hb hc => rw [map_add]; exact hb.add_right hc
  | mul a c ha hc => rw [map_mul]; exact ha.mul_left hc
  | add a c ha hc => rw [map_add]; exact ha.add_left hc

/-- The Rees algebra modulo `X` is commutative. -/
@[implicit_reducible] def reesCommRing : CommRing (reesCon R L).Quotient :=
  { (inferInstance : Ring (reesCon R L).Quotient) with
    mul_comm := fun p q ↦ by
      obtain ⟨a, rfl⟩ := reesMk_surjective R L p
      obtain ⟨b, rfl⟩ := reesMk_surjective R L q
      exact commute_reesMk R L a b }

/-- A homogeneous tensor of degree `n + 1` that vanishes in the symmetric algebra has image in
the enveloping algebra a sum of products of at most `n` elements of `L`. -/
theorem mkAlgHom_mem_of_algHom_eq_zero {n : ℕ} {t : TensorAlgebra R L}
    (ht : t ∈ LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ (n + 1))
    (h : SymmetricAlgebra.algHom R L t = 0) : mkAlgHom R L t ∈ filtration R L n := by
  let _ := reesCommRing R L
  let g : SymmetricAlgebra R L →ₐ[R] (reesCon R L).Quotient :=
    SymmetricAlgebra.lift ((reesMk R L).toLinearMap ∘ₗ TensorAlgebra.ι R)
  have hg : g.comp (SymmetricAlgebra.algHom R L) = reesMk R L :=
    TensorAlgebra.hom_ext (LinearMap.ext fun x ↦ SymmetricAlgebra.lift_ι_apply _ x)
  have h0 : reesMk R L t = 0 := by
    rw [← hg, AlgHom.comp_apply, h, map_zero]
  obtain ⟨q, hq, hq'⟩ := (reesMk_eq_zero_iff R L).mp h0
  have hc := congrArg (fun p ↦ p.coeff (n + 1)) hq'
  simp only [toRees_of_mem_pow R L ht, coeff_C_mul_X_pow, ite_true, coeff_X_mul] at hc
  rw [hc]
  exact hq n

end UniversalEnvelopingAlgebra
