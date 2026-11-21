/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.Brace
public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Derivation
public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Grading
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
public import Mathlib.Algebra.NonAssoc.PreLie.Basic
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Tactic.LinearCombination

/-!
# The enveloping algebra of a pre-Lie algebra acts on its symmetric algebra

Let `L` be a right pre-Lie algebra over a commutative ring `R`. Each `X` in `L` acts on the
symmetric algebra `S(L)` by `a ↦ a * ι X + D_X a`, where `D_X` is the derivation that multiplies
one generator on the right by `X` (`RightPreLieAlgebra.derivation`). The pre-Lie identity makes
this a right action of the commutator Lie algebra of `L` (`RightPreLieAlgebra.act_act`), so it
extends to a right action of the enveloping algebra, and acting on `1` gives a linear map
`RightPreLieAlgebra.toSymmetricAlgebra` from the enveloping algebra to `S(L)`.

That map is surjective (`RightPreLieAlgebra.toSymmetricAlgebra_surjective`): the action of `X`
on an element of degree `n` is its product with `ι X` plus an element of degree `n`.

## TODO

* `toSymmetricAlgebra` is injective. With surjectivity this identifies the enveloping algebra of
  the commutator Lie algebra of `L` with `S(L)`, as [oudom-guin-2008] show, and transports the
  product of the enveloping algebra to their product on `S(L)`.

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

/-! ### Surjectivity -/

/-- A derivation of `X` that preserves a submodule preserves its powers. -/
theorem derivation_mem_pow_of {N : Submodule R (SymmetricAlgebra R L)} (X : L)
    (hN : ∀ a ∈ N, derivation R X a ∈ N) {n : ℕ} {a : SymmetricAlgebra R L} (ha : a ∈ N ^ n) :
    derivation R X a ∈ N ^ n := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [Derivation.map_algebraMap]; exact zero_mem _
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem ((pow_succ' N i).symm ▸ Submodule.mul_mem_mul hm ih)
      ((pow_succ N i).symm ▸ Submodule.mul_mem_mul hx (hN m hm))

/-- The derivation of `X` preserves degree. -/
theorem derivation_mem_pow (X : L) {n : ℕ} {a : SymmetricAlgebra R L}
    (ha : a ∈ LinearMap.range (ι R L) ^ n) : derivation R X a ∈ LinearMap.range (ι R L) ^ n :=
  derivation_mem_pow_of R X (by rintro _ ⟨Y, rfl⟩; exact ⟨Y * X, (derivation_ι R X Y).symm⟩) ha

theorem pow_le_range_toSymmetricAlgebra (n : ℕ) :
    LinearMap.range (ι R L) ^ n ≤ LinearMap.range (toSymmetricAlgebra R (L := L)) := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_le]
    exact ⟨1, toSymmetricAlgebra_one R⟩
  | succ n ih =>
    rw [pow_succ, Submodule.mul_le]
    rintro a ha _ ⟨X, rfl⟩
    obtain ⟨u, rfl⟩ := ih ha
    obtain ⟨v, hv⟩ := ih (derivation_mem_pow R X ha)
    refine ⟨u * UniversalEnvelopingAlgebra.ι R X - v, ?_⟩
    rw [map_sub, toSymmetricAlgebra_mul_ι, act_apply, hv, add_sub_cancel_right]

/-- Every element of the symmetric algebra is the enveloping algebra acting on `1`. -/
theorem toSymmetricAlgebra_surjective :
    Function.Surjective (toSymmetricAlgebra R (L := L)) := by
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  intro a
  induction a using DirectSum.Decomposition.inductionOn
    fun n : ℕ ↦ LinearMap.range (ι R L) ^ n with
  | zero => exact zero_mem _
  | homogeneous m => exact pow_le_range_toSymmetricAlgebra R _ m.2
  | add _ _ hm hm' => exact add_mem hm hm'

/-! ### Filtrations

The enveloping algebra and the symmetric algebra are filtered by the powers of `1 ⊔ M`, for `M`
the range of the generators: the `n`-th power is spanned by the products of at most `n`
generators. -/

private theorem pow_le_one_sup_pow {A : Type*} [Semiring A] [Algebra R A] (M : Submodule R A)
    (k : ℕ) : M ^ k ≤ (1 ⊔ M) ^ k :=
  pow_le_pow_left' le_sup_right k

private theorem one_sup_pow_succ {A : Type*} [Semiring A] [Algebra R A] (M : Submodule R A)
    (m : ℕ) : (1 ⊔ M) ^ (m + 1) = (1 ⊔ M) ^ m ⊔ M ^ (m + 1) := by
  have hmono : ∀ k, M ^ k ≤ (1 ⊔ M) ^ k := pow_le_one_sup_pow R M
  have hstep : ∀ k, (1 ⊔ M) ^ k ≤ (1 ⊔ M) ^ (k + 1) := fun k ↦ by
    rw [pow_succ, Submodule.mul_sup, mul_one]
    exact le_sup_left
  refine le_antisymm ?_ (sup_le (hstep m) (hmono _))
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Submodule.mul_sup, mul_one]
    refine sup_le le_sup_left ?_
    refine (mul_le_mul' ih le_rfl).trans ?_
    rw [Submodule.sup_mul, ← pow_succ]
    exact sup_le (le_sup_of_le_left ((mul_le_mul' le_rfl le_sup_right).trans (pow_succ _ _).ge))
      le_sup_right

theorem toSymmetricAlgebra_algebraMap (r : R) :
    toSymmetricAlgebra R (algebraMap R (UniversalEnvelopingAlgebra R L) r) =
      algebraMap R (SymmetricAlgebra R L) r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, toSymmetricAlgebra_one,
    Algebra.algebraMap_eq_smul_one]

/-- The generators of the enveloping algebra, as a submodule. -/
local notation "M_U" =>
  LinearMap.range
    ((UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L) : L →ₗ[R] _)

/-- The generators of the symmetric algebra, as a submodule. -/
local notation "M_S" => LinearMap.range (ι R L)

theorem derivation_mem_one_sup_pow (X : L) {k : ℕ} {a : SymmetricAlgebra R L}
    (ha : a ∈ (1 ⊔ M_S) ^ k) : derivation R X a ∈ (1 ⊔ M_S) ^ k :=
  derivation_mem_pow_of R X (fun b hb ↦ by
    obtain ⟨c, hc, d, ⟨Y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    rw [map_add, Derivation.map_algebraMap, zero_add, derivation_ι]
    exact Submodule.mem_sup_right ⟨_, rfl⟩) ha

/-- A product of at most `m` generators of the enveloping algebra goes to a sum of products of
at most `m` generators of the symmetric algebra. -/
theorem toSymmetricAlgebra_mem_pow {m : ℕ} {u : UniversalEnvelopingAlgebra R L}
    (hu : u ∈ (1 ⊔ M_U) ^ m) : toSymmetricAlgebra R u ∈ (1 ⊔ M_S) ^ m := by
  induction hu using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    rw [toSymmetricAlgebra_algebraMap, pow_zero]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mul_mem i x hx ih w hw =>
    obtain ⟨c, hc, d, ⟨X, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    have hle : (1 ⊔ M_S) ^ i ≤ (1 ⊔ M_S) ^ (i + 1) := by
      rw [one_sup_pow_succ]; exact le_sup_left
    rw [mul_add, map_add, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
    refine add_mem (hle (Submodule.smul_mem _ r ih)) ?_
    change toSymmetricAlgebra R (x * UniversalEnvelopingAlgebra.ι R X) ∈ _
    rw [toSymmetricAlgebra_mul_ι, act_apply]
    refine add_mem ?_ (hle (derivation_mem_one_sup_pow R X ih))
    rw [pow_succ]
    exact Submodule.mul_mem_mul ih (Submodule.mem_sup_right ⟨X, rfl⟩)

/-- The generators of the tensor algebra, as a submodule. -/
local notation "M_T" => LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L)

theorem mkAlgHom_mem_pow {k : ℕ} {t : TensorAlgebra R L} (ht : t ∈ M_T ^ k) :
    UniversalEnvelopingAlgebra.mkAlgHom R L t ∈ M_U ^ k := by
  induction ht using Submodule.pow_induction_on_right' with
  | algebraMap r => rw [AlgHom.commutes, pow_zero]; exact Submodule.mem_one.mpr ⟨r, rfl⟩
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mul_mem i x hx ih m hm =>
    obtain ⟨Y, rfl⟩ := hm
    rw [map_mul]
    exact Submodule.mul_mem_mul ih ⟨Y, rfl⟩

/-- A product of `n + 1` generators of the enveloping algebra goes to the product of the same
generators in the symmetric algebra, up to products of at most `n` generators. -/
theorem toSymmetricAlgebra_mkAlgHom_sub_mem (n : ℕ) {t : TensorAlgebra R L}
    (ht : t ∈ M_T ^ (n + 1)) :
    toSymmetricAlgebra R (UniversalEnvelopingAlgebra.mkAlgHom R L t) - algHom R L t ∈
      (1 ⊔ M_S) ^ n := by
  induction n generalizing t with
  | zero =>
    rw [zero_add, pow_one] at ht
    obtain ⟨Y, rfl⟩ := ht
    have h : UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R Y) =
        1 * UniversalEnvelopingAlgebra.ι R Y := (one_mul _).symm
    rw [h, toSymmetricAlgebra_mul_ι, toSymmetricAlgebra_one, act_apply, one_mul,
      Derivation.map_one_eq_zero, add_zero, show algHom R L (TensorAlgebra.ι R Y) = ι R L Y from rfl,
      sub_self]
    exact zero_mem _
  | succ n ih =>
    rw [pow_succ] at ht
    refine Submodule.mul_induction_on ht (fun x hx m hm ↦ ?_) (fun x y hx hy ↦ ?_)
    · obtain ⟨Y, rfl⟩ := hm
      have hU : UniversalEnvelopingAlgebra.mkAlgHom R L (x * TensorAlgebra.ι R Y) =
          UniversalEnvelopingAlgebra.mkAlgHom R L x * UniversalEnvelopingAlgebra.ι R Y := by
        rw [map_mul]; rfl
      have hW : UniversalEnvelopingAlgebra.mkAlgHom R L x ∈ (1 ⊔ M_U) ^ (n + 1) :=
        pow_le_one_sup_pow R _ _ (mkAlgHom_mem_pow R hx)
      rw [hU, toSymmetricAlgebra_mul_ι, act_apply, map_mul,
        show algHom R L (TensorAlgebra.ι R Y) = ι R L Y from rfl, add_sub_right_comm, ← sub_mul]
      refine add_mem ?_ (derivation_mem_one_sup_pow R Y (toSymmetricAlgebra_mem_pow R hW))
      rw [pow_succ]
      exact Submodule.mul_mem_mul (ih hx) (Submodule.mem_sup_right ⟨Y, rfl⟩)
    · rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy

end RightPreLieAlgebra
