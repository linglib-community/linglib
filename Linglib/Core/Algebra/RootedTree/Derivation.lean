/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of the Connes–Kreimer algebra

`ConnesKreimer R T` is the free commutative algebra on `T`, so a derivation from it is
[determined by its values on the trees](##ConnesKreimer.derivation_ext), and every function on
the trees [extends to one](##ConnesKreimer.mkDerivation), as `MvPolynomial.mkDerivation` does for
polynomials: on a forest it replaces each tree in turn by its value.
-/

@[expose] public section

noncomputable section

namespace ConnesKreimer

open UnorderedTree

variable {R T M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Module (ConnesKreimer R T) M] [IsScalarTower R (ConnesKreimer R T) M]

open Classical in
/-- The linear map underlying `mkDerivation`. -/
def mkDerivationₗ (f : T → M) : ConnesKreimer R T →ₗ[R] M :=
  linearLift (R := R) fun F ↦ (F.map fun t ↦ (of' (F.erase t) : ConnesKreimer R T) • f t).sum

omit [IsScalarTower R (ConnesKreimer R T) M] in
theorem mkDerivationₗ_of'_add (f : T → M) (F G : Forest T) :
    mkDerivationₗ (R := R) f (of' (F + G)) =
      (of' F : ConnesKreimer R T) • mkDerivationₗ (R := R) f (of' G) +
        (of' G : ConnesKreimer R T) • mkDerivationₗ (R := R) f (of' F) := by
  classical
  simp only [mkDerivationₗ, linearLift_of', Multiset.map_add, Multiset.sum_add, Multiset.smul_sum,
    Multiset.map_map, Function.comp_def]
  rw [add_comm]
  refine congrArg₂ _ (congrArg _ (Multiset.map_congr rfl fun t ht ↦ ?_))
    (congrArg _ (Multiset.map_congr rfl fun t ht ↦ ?_))
  · rw [Multiset.erase_add_right_pos _ ht, of'_add, mul_smul]
  · rw [Multiset.erase_add_left_pos _ ht, of'_add, mul_comm, mul_smul]

/-- The derivation of the Connes–Kreimer algebra with the given values on the trees. -/
def mkDerivation (f : T → M) : Derivation R (ConnesKreimer R T) M where
  toLinearMap := mkDerivationₗ f
  map_one_eq_zero' := by
    rw [← of'_zero, mkDerivationₗ, linearLift_of']
    simp
  leibniz' a b := by
    induction a using induction_linear with
    | zero => simp
    | add a₁ a₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, add_smul, map_add, smul_add]; abel
    | single F r =>
    induction b using induction_linear with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, add_smul, map_add, smul_add]; abel
    | single G s =>
      rw [← smul_of', ← smul_of', smul_mul_smul_comm, ← of'_add, map_smul, map_smul, map_smul,
        mkDerivationₗ_of'_add]
      simp only [smul_assoc, smul_add, smul_comm (of' _ : ConnesKreimer R T), smul_smul,
        mul_comm s r]

open Classical in
/-- On a forest the derivation replaces each tree in turn by its value. -/
theorem mkDerivation_of' (f : T → M) (F : Forest T) :
    mkDerivation (R := R) f (of' F) =
      (F.map fun t ↦ (of' (F.erase t) : ConnesKreimer R T) • f t).sum := by
  change mkDerivationₗ (R := R) f (of' F) = _
  rw [mkDerivationₗ, linearLift_of']

@[simp] theorem mkDerivation_ofTree (f : T → M) (t : T) :
    mkDerivation (R := R) f (ofTree t) = f t := by
  classical
  change mkDerivationₗ (R := R) f (ofTree t) = f t
  rw [← of'_singleton, mkDerivationₗ, linearLift_of']
  simp

omit [IsScalarTower R (ConnesKreimer R T) M] in
/-- Derivations that agree on the trees are equal. -/
theorem derivation_ext {D₁ D₂ : Derivation R (ConnesKreimer R T) M}
    (h : ∀ t, D₁ (ofTree t) = D₂ (ofTree t)) : D₁ = D₂ := by
  refine Derivation.ext fun x ↦ LinearMap.congr_fun
    (lhom_ext' (f := (D₁ : ConnesKreimer R T →ₗ[R] M)) (g := D₂) fun F ↦ ?_) x
  induction F using Multiset.induction_on with
  | empty =>
    change D₁ (of' 0) = D₂ (of' 0)
    rw [of'_zero, Derivation.map_one_eq_zero, Derivation.map_one_eq_zero]
  | cons t F ih =>
    simp only [Derivation.coeFn_coe] at ih ⊢
    rw [of'_cons, Derivation.leibniz, Derivation.leibniz, ih, h]

end ConnesKreimer
