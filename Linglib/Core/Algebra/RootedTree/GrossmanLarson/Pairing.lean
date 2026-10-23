/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.GrossmanLarson.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Linglib.Core.Combinatorics.RootedTree.Aut

/-!
# The symmetry-weighted pairing on forests

This file defines the pairing on `H = ConnesKreimer R (UnorderedTree α)` that makes the forests an
orthogonal basis, each forest paired with itself to its number of symmetries:
`⟨of' F, of' G⟩ = if F = G then |Aut F| else 0`. Foissy uses this pairing in his dual
construction of the Connes–Kreimer coproduct; here it makes the Grossman–Larson product dual to
the pruning coproduct (`Coproduct/PruningDuality.lean`).

## Main definitions

* `GrossmanLarson.pairing`: the symmetry-weighted pairing.
* `GrossmanLarson.pairing₂`: its extension to `H ⊗ H`.

## Main results

* `GrossmanLarson.pairing_symm`: the pairing is symmetric.
* `GrossmanLarson.pairing_of'`: pairing with a forest takes the coefficient of that forest,
  times its number of symmetries.
* `GrossmanLarson.pairing_nondegenerate`: the pairing is nondegenerate over a ring of
  characteristic zero without zero divisors.
* `GrossmanLarson.pairing_of'_mul`, `GrossmanLarson.pairing_product_of'_mul_of'`: pairing against
  a Connes–Kreimer product splits a basis forest over its antidiagonal, and splits both factors of
  a Grossman–Larson product.

## References

* [foissy-2021]
* [grossman-larson-1989]
* [oudom-guin-2008]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace GrossmanLarson

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ### The bilinear pairing -/

/-- `pairing (of' F) (of' G)` is the number of symmetries of `F` when `F = G`, and `0`
otherwise. -/
noncomputable def pairing :
    ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) →ₗ[R] R :=
  ConnesKreimer.linearLift fun F ↦ ConnesKreimer.linearLift fun G ↦
    if F = G then (forestAutCard F : R) else 0

@[simp] theorem pairing_of'_of' (F G : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' F) (ConnesKreimer.of' G) =
      (if F = G then (forestAutCard F : R) else 0) := by
  simp [pairing]

theorem pairing_symm (x y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) x y = pairing y x := by
  have h : pairing (R := R) (α := α) = pairing.flip := by
    ext F G
    rcases eq_or_ne F G with rfl | h
    · simp
    · simp [h, h.symm]
  exact congr($h x y)

@[simp] theorem pairing_zero_left (y : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) 0 y = 0 := by
  simp only [LinearMap.map_zero, LinearMap.zero_apply]

@[simp] theorem pairing_zero_right (x : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) x 0 = 0 :=
  LinearMap.map_zero _

theorem pairing_one_right (w : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) w (1 : ConnesKreimer R (UnorderedTree α)) =
      (ConnesKreimer.counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R) w := by
  have h : (pairing (R := R)).flip (1 : ConnesKreimer R (UnorderedTree α)) =
      (ConnesKreimer.counit : ConnesKreimer R (UnorderedTree α) →ₐ[R] R).toLinearMap := by
    ext F
    rcases eq_or_ne F 0 with rfl | h <;> simp [← ConnesKreimer.of'_zero, *]
  exact congr($h w)

theorem pairing_of' (F : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' F) = (forestAutCard F : R) • ConnesKreimer.lcoeff R F := by
  ext G
  rcases eq_or_ne F G with rfl | h
  · simp [ConnesKreimer.coeff_of']
  · simp [ConnesKreimer.coeff_of', h, h.symm]

theorem pairing_apply_of' (x : ConnesKreimer R (UnorderedTree α))
    (G : Forest (UnorderedTree α)) :
    pairing (R := R) x (ConnesKreimer.of' G) =
      x.coeff G * (forestAutCard G : R) := by
  rw [pairing_symm, pairing_of', LinearMap.smul_apply, ConnesKreimer.lcoeff_apply, smul_eq_mul,
    mul_comm]

theorem pairing_nondegenerate
    [CharZero R] [NoZeroDivisors R] (x : ConnesKreimer R (UnorderedTree α))
    (h : ∀ y, pairing (R := R) x y = 0) : x = 0 := by
  refine ConnesKreimer.ext_coeff fun G => ?_
  rw [ConnesKreimer.coeff_zero]
  have hG : pairing (R := R) x (ConnesKreimer.of' G) = 0 := h _
  rw [pairing_apply_of'] at hG
  have hauts_ne : (UnorderedTree.forestAutCard G : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (UnorderedTree.forestAutCard_pos G).ne'
  rcases mul_eq_zero.mp hG with hx | hx
  · exact hx
  · exact absurd hx hauts_ne

section Ring
variable {R : Type*} [CommRing R] [CharZero R] [NoZeroDivisors R]

theorem ext_pairing_right {x y : ConnesKreimer R (UnorderedTree α)}
    (h : ∀ z, pairing (R := R) x z = pairing y z) : x = y :=
  sub_eq_zero.mp <| pairing_nondegenerate _ fun z => by
    rw [map_sub, LinearMap.sub_apply, h, sub_self]

end Ring

/-! ### Product rule

Pairing against a Connes–Kreimer product splits the basis forest over its antidiagonal; the
weights recombine by `UnorderedTree.forestAutCard_add`. -/

theorem pairing_of'_mul_of' (W C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' W)
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1) (ConnesKreimer.of' C₁) *
        pairing (R := R) (ConnesKreimer.of' p.2) (ConnesKreimer.of' C₂))).sum := by
  rw [Multiset.sum_map_eq_nsmul_single (C₁, C₂) fun p hp _ ↦ ?_, ← ConnesKreimer.of'_add]
  · simp only [pairing_of'_of', ite_true, nsmul_eq_mul]
    split_ifs with hW
    · rw [hW, ← Nat.cast_mul, ← Nat.cast_mul, forestAutCard_add]
    · rw [Multiset.count_eq_zero.mpr (mt (Multiset.mem_antidiagonal (x := (C₁, C₂))).mp
        (Ne.symm hW)), Nat.cast_zero, zero_mul]
  · rw [pairing_of'_of', pairing_of'_of']
    split_ifs with h₁ h₂ <;> simp_all [Prod.ext_iff]

theorem pairing_of'_mul (W : Forest (UnorderedTree α))
    (z₁ z₂ : ConnesKreimer R (UnorderedTree α)) :
    pairing (R := R) (ConnesKreimer.of' W) (z₁ * z₂) =
      ((Multiset.antidiagonal W).map (fun p =>
        pairing (R := R) (ConnesKreimer.of' p.1) z₁ *
        pairing (R := R) (ConnesKreimer.of' p.2) z₂)).sum := by
  induction z₁ using ConnesKreimer.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb, Multiset.sum_map_add]
  | single F r =>
    induction z₂ using ConnesKreimer.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mul_add, map_add, ha, hb, Multiset.sum_map_add]
    | single G s =>
      simp only [← ConnesKreimer.smul_of', smul_mul_smul_comm, map_smul, smul_eq_mul,
        pairing_of'_mul_of', mul_mul_mul_comm r, Multiset.sum_map_mul_left]

theorem pairing_product_of'_mul_of' (A B C₁ C₂ : Forest (UnorderedTree α)) :
    pairing (R := R) (product (ConnesKreimer.of' A) (ConnesKreimer.of' B))
        (ConnesKreimer.of' C₁ * ConnesKreimer.of' C₂) =
      ((A.antidiagonal ×ˢ B.antidiagonal).map fun pq ↦
        pairing (R := R) (product (ConnesKreimer.of' pq.1.1) (ConnesKreimer.of' pq.2.1))
            (ConnesKreimer.of' C₁) *
          pairing (R := R) (product (ConnesKreimer.of' pq.1.2) (ConnesKreimer.of' pq.2.2))
            (ConnesKreimer.of' C₂)).sum := by
  have h (A B : Forest (UnorderedTree α)) (z : ConnesKreimer R (UnorderedTree α)) :
      pairing (R := R) (product (ConnesKreimer.of' A) (ConnesKreimer.of' B)) z =
        ((productMultiset A B).map fun W ↦ pairing (R := R) (ConnesKreimer.of' W) z).sum := by
    change pairing.flip z _ = _
    rw [product_of'_of', map_multiset_sum, Multiset.map_map]
    rfl
  rw [h, Multiset.map_congr rfl fun W _ ↦ pairing_of'_mul W _ _, ← Multiset.sum_bind,
    ← Multiset.map_bind, productMultiset_bind_antidiagonal, Multiset.map_bind, Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun pq _ ↦ ?_)
  rw [h, h, ← Multiset.sum_map_product_mul]

open scoped TensorProduct

/-! ### The pairing on `H ⊗ H`

The duality with the pruning coproduct is stated on `H ⊗ H`. No such duality holds for a coproduct
that leaves marker leaves in the trunk, since grafting never produces them. -/

/-- `pairing₂` is the pairing on `H ⊗ H` with `pairing₂ (x ⊗ y) (w ⊗ z) = ⟨x, w⟩ * ⟨y, z⟩`. -/
noncomputable def pairing₂ :
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R]
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R] R :=
  let pair : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)
                →ₗ[R] R :=
    TensorProduct.lift pairing
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair pair ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))).toLinearMap

@[simp] theorem pairing₂_tmul_tmul
    (x y w z : ConnesKreimer R (UnorderedTree α)) :
    pairing₂ (R := R) (x ⊗ₜ y) (w ⊗ₜ z) =
      pairing x w * pairing y z := by
  rfl

end GrossmanLarson

