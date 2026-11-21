/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.Enveloping
public import Linglib.Core.Algebra.RootedTree.Derivation
public import Linglib.Core.Algebra.RootedTree.SymmetricAlgebra
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Tactic.Abel

/-!
# The Oudom–Guin product on a symmetric algebra with a basis of monomials

Let `L` be a right pre-Lie algebra with a basis `b` indexed by `ι`, so that its symmetric algebra
is `ConnesKreimer R ι`, the free commutative algebra on `ι`, by
`SymmetricAlgebra.equivConnesKreimer b`. This file carries the product of Oudom and Guin,
`RightPreLieAlgebra.product`, along that isomorphism to `OudomGuin.product b`. It is associative
with unit `1`, the product with a generator is multiplication by it plus the derivation that
multiplies one generator on the right by it (`OudomGuin.product_ofTree`), and on `L` it is the
commutative product plus the pre-Lie product (`OudomGuin.product_incl_incl`), so that `L` maps
into its commutator Lie algebra (`OudomGuin.product_incl_incl_sub`).

## References

* [oudom-guin-2008]
-/

@[expose] public section

noncomputable section

namespace OudomGuin

open ConnesKreimer RightPreLieRing UnorderedTree

variable {R ι L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]
  (b : Module.Basis ι R L)

/-- The pre-Lie algebra in its symmetric algebra: a basis vector goes to its generator. -/
def incl : L →ₗ[R] ConnesKreimer R ι := b.constr R ofTree

@[simp] theorem incl_basis (i : ι) : incl b (b i) = ofTree i := b.constr_basis R _ i

theorem equivConnesKreimer_ι (X : L) :
    SymmetricAlgebra.equivConnesKreimer b (SymmetricAlgebra.ι R L X) = incl b X :=
  SymmetricAlgebra.lift_ι_apply _ X

theorem equivConnesKreimer_symm_incl (X : L) :
    (SymmetricAlgebra.equivConnesKreimer b).symm (incl b X) = SymmetricAlgebra.ι R L X :=
  (AlgEquiv.symm_apply_eq _).mpr (equivConnesKreimer_ι b X).symm

/-- The derivation of the symmetric algebra that multiplies one generator on the right by
`X`. -/
def derivation (X : L) : Derivation R (ConnesKreimer R ι) (ConnesKreimer R ι) :=
  mkDerivation fun i ↦ incl b (b i * X)

@[simp] theorem derivation_ofTree (X : L) (i : ι) :
    derivation b X (ofTree i) = incl b (b i * X) :=
  mkDerivation_ofTree _ i

@[simp] theorem derivation_incl (X Y : L) : derivation b X (incl b Y) = incl b (Y * X) := by
  have h : (derivation b X : ConnesKreimer R ι →ₗ[R] _) ∘ₗ incl b =
      incl b ∘ₗ LinearMap.mulRight R X := b.ext fun i ↦ by simp
  exact LinearMap.congr_fun h Y

/-- The isomorphism with the symmetric algebra carries the derivation of `X` to the derivation of
`X`. -/
theorem equivConnesKreimer_derivation (X : L) (a : SymmetricAlgebra R L) :
    SymmetricAlgebra.equivConnesKreimer b (RightPreLieAlgebra.derivation R X a) =
      derivation b X (SymmetricAlgebra.equivConnesKreimer b a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => rw [AlgEquiv.commutes, Derivation.map_algebraMap, Derivation.map_algebraMap,
      map_zero]
  | ι Y => rw [RightPreLieAlgebra.derivation_ι, equivConnesKreimer_ι, equivConnesKreimer_ι,
      derivation_incl]
  | mul a c ha hc =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, map_add, map_mul, map_mul, ha, hc]
  | add a c ha hc => rw [map_add, map_add, map_add, map_add, ha, hc]

/-- The product of Oudom and Guin on the symmetric algebra, in the basis of monomials. -/
def product : ConnesKreimer R ι →ₗ[R] ConnesKreimer R ι →ₗ[R] ConnesKreimer R ι :=
  ((RightPreLieAlgebra.product R (L := L)).compl₁₂
    (SymmetricAlgebra.equivConnesKreimer b).symm.toLinearMap
    (SymmetricAlgebra.equivConnesKreimer b).symm.toLinearMap).compr₂
    (SymmetricAlgebra.equivConnesKreimer b).toLinearMap

theorem product_apply (x y : ConnesKreimer R ι) :
    product b x y = SymmetricAlgebra.equivConnesKreimer b
      (RightPreLieAlgebra.product R ((SymmetricAlgebra.equivConnesKreimer b).symm x)
        ((SymmetricAlgebra.equivConnesKreimer b).symm y)) := rfl

@[simp] theorem product_one_right (x : ConnesKreimer R ι) : product b x 1 = x := by
  rw [product_apply, map_one, RightPreLieAlgebra.product_one_right, AlgEquiv.apply_symm_apply]

@[simp] theorem product_one_left (y : ConnesKreimer R ι) : product b 1 y = y := by
  rw [product_apply, map_one, RightPreLieAlgebra.product_one_left, AlgEquiv.apply_symm_apply]

/-- The product of Oudom and Guin is associative. -/
theorem product_assoc (x y z : ConnesKreimer R ι) :
    product b (product b x y) z = product b x (product b y z) := by
  simp only [product_apply, AlgEquiv.symm_apply_apply, RightPreLieAlgebra.product_assoc]

/-- The product with an element of `L` is its action. -/
theorem product_incl (x : ConnesKreimer R ι) (Y : L) :
    product b x (incl b Y) = x * incl b Y + derivation b Y x := by
  rw [product_apply, equivConnesKreimer_symm_incl, RightPreLieAlgebra.product_ι, map_add, map_mul,
    equivConnesKreimer_derivation, equivConnesKreimer_ι, AlgEquiv.apply_symm_apply]

/-- The product with a generator is the action of its basis vector. -/
theorem product_ofTree (x : ConnesKreimer R ι) (i : ι) :
    product b x (ofTree i) = x * ofTree i + derivation b (b i) x := by
  rw [← incl_basis b i, product_incl]

/-- The recursion of the product in its second argument: `x ⋆ (y Xᵢ) = (x ⋆ y) ⋆ Xᵢ - x ⋆ (y ∘ Xᵢ)`,
where `y ∘ Xᵢ` multiplies one generator of `y` on the right by `Xᵢ`. -/
theorem product_mul_ofTree (x y : ConnesKreimer R ι) (i : ι) :
    product b x (y * ofTree i) =
      product b (product b x y) (ofTree i) - product b x (derivation b (b i) y) := by
  rw [product_assoc, product_ofTree b y, map_add, add_sub_cancel_right]

/-- Linear maps that agree on the monomials of degree `n` agree on the derivation of a monomial
of degree `n`. -/
theorem eqOn_derivation_of' {M : Type*} [AddCommGroup M] [Module R M]
    {f g : ConnesKreimer R ι →ₗ[R] M} {n : ℕ}
    (h : ∀ E : Forest ι, Multiset.card E = n → f (of' E) = g (of' E)) (X : L) (E : Forest ι)
    (hE : Multiset.card E = n) :
    f (derivation b X (of' E)) = g (derivation b X (of' E)) := by
  classical
  rw [derivation, mkDerivation_of', map_multiset_sum, map_multiset_sum, Multiset.map_map,
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun t ht ↦ ?_)
  have hfg : f ∘ₗ LinearMap.mulLeft R (of' (E.erase t)) ∘ₗ incl b =
      g ∘ₗ LinearMap.mulLeft R (of' (E.erase t)) ∘ₗ incl b := b.ext fun j ↦ by
    simp only [LinearMap.comp_apply, incl_basis, LinearMap.mulLeft_apply]
    rw [mul_comm, ← of'_cons]
    refine h _ ?_
    rw [Multiset.card_cons, Multiset.card_erase_of_mem ht, ← hE]
    exact Nat.succ_pred_eq_of_pos (Multiset.card_pos_iff_exists_mem.mpr ⟨t, ht⟩)
  simpa [smul_eq_mul] using LinearMap.congr_fun hfg (b t * X)

/-- On `L` the product is the commutative product plus the pre-Lie product. -/
theorem product_incl_incl (X Y : L) :
    product b (incl b X) (incl b Y) = incl b X * incl b Y + incl b (X * Y) := by
  rw [product_incl, derivation_incl]

/-- The commutator of the product on `L` is the commutator of the pre-Lie product. -/
theorem product_incl_incl_sub (X Y : L) :
    product b (incl b X) (incl b Y) - product b (incl b Y) (incl b X) =
      incl b (X * Y - Y * X) := by
  rw [product_incl_incl, product_incl_incl, mul_comm (incl b Y), map_sub]
  abel

end OudomGuin
