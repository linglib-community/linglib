/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.Lie.UniversalEnveloping.Rees
public import Linglib.Core.Algebra.NonAssoc.PreLie.SymmetricAlgebra
public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Basic
public import Linglib.Core.LinearAlgebra.SymmetricAlgebra.Grading
public import Linglib.Core.RingTheory.Derivation.Basic

/-!
# The enveloping algebra of a pre-Lie algebra

Let `L` be a right pre-Lie algebra over a commutative ring `R`. The enveloping algebra of its
commutator Lie algebra acts on the symmetric algebra `S(L)`, and acting on `1` is a linear map
`RightPreLieAlgebra.toSymmetricAlgebra`. This file shows that it is bijective,
`RightPreLieAlgebra.equivSymmetricAlgebra`: the enveloping algebra is `S(L)` as a module, which is
the Poincaré–Birkhoff–Witt theorem for these Lie algebras, with no hypothesis on `L` as a module.
In particular `L` embeds in its enveloping algebra (`RightPreLieAlgebra.ι_injective`).

A product of `n + 1` elements of `L` in the enveloping algebra goes to the product of the same
elements in `S(L)`, up to products of at most `n`
(`RightPreLieAlgebra.toSymmetricAlgebra_mkAlgHom_sub_mem`). Surjectivity follows by induction on
the degree. For injectivity, an element of the kernel in `filtration R L (n + 1)` has its part of
degree `n + 1` vanish in `S(L)`, so that part is in `filtration R L n` by
`UniversalEnvelopingAlgebra.mkAlgHom_mem_of_algHom_eq_zero`.

## Implementation notes

[oudom-guin-2008] first build an associative product on `S(L)` and compare associated graded
algebras. Here `S(L)` is shown to be a free module of rank one over the enveloping algebra,
comparing the filtrations directly; the product is defined afterwards, in
`Linglib/Core/Algebra/NonAssoc/PreLie/Product.lean`.

## References

* [oudom-guin-2008]
-/

@[expose] public section

noncomputable section

namespace RightPreLieAlgebra

open SymmetricAlgebra RightPreLieRing

variable (R : Type*) {L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Surjectivity -/

/-- The derivation of `X` preserves degree. -/
theorem derivation_mem_pow (X : L) {n : ℕ} {a : SymmetricAlgebra R L}
    (ha : a ∈ LinearMap.range (ι R L) ^ n) : derivation R X a ∈ LinearMap.range (ι R L) ^ n :=
  (derivation R X).mem_pow_of_forall_mem
    (by rintro _ ⟨Y, rfl⟩; exact ⟨Y * X, (derivation_ι R X Y).symm⟩) ha

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

/-! ### The filtrations

The image of `UniversalEnvelopingAlgebra.filtration R L m` consists of sums of products of at
most `m` generators of the symmetric algebra, and a product of `n + 1` elements of `L` goes to
the product of the same elements up to such a sum for `n`. -/

/-- The generators of the symmetric algebra, as a submodule. -/
local notation "M_S" => LinearMap.range (ι R L)

theorem derivation_mem_one_sup_pow (X : L) {k : ℕ} {a : SymmetricAlgebra R L}
    (ha : a ∈ (1 ⊔ M_S) ^ k) : derivation R X a ∈ (1 ⊔ M_S) ^ k :=
  (derivation R X).mem_pow_of_forall_mem (fun b hb ↦ by
    obtain ⟨c, hc, d, ⟨Y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    rw [map_add, Derivation.map_algebraMap, zero_add, derivation_ι]
    exact Submodule.mem_sup_right ⟨_, rfl⟩) ha

/-- A product of at most `m` generators of the enveloping algebra goes to a sum of products of
at most `m` generators of the symmetric algebra. -/
theorem toSymmetricAlgebra_mem_pow {m : ℕ} {u : UniversalEnvelopingAlgebra R L}
    (hu : u ∈ UniversalEnvelopingAlgebra.filtration R L m) :
    toSymmetricAlgebra R u ∈ (1 ⊔ M_S) ^ m := by
  rw [UniversalEnvelopingAlgebra.filtration] at hu
  induction hu using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    rw [toSymmetricAlgebra_algebraMap, pow_zero]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mul_mem i x hx ih w hw =>
    obtain ⟨c, hc, d, ⟨X, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    have hle : (1 ⊔ M_S) ^ i ≤ (1 ⊔ M_S) ^ (i + 1) := by
      rw [Submodule.one_sup_pow_succ]; exact le_sup_left
    rw [mul_add, map_add, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
    refine add_mem (hle (Submodule.smul_mem _ r ih)) ?_
    change toSymmetricAlgebra R (x * UniversalEnvelopingAlgebra.ι R X) ∈ _
    rw [toSymmetricAlgebra_mul_ι, act_apply]
    refine add_mem ?_ (hle (derivation_mem_one_sup_pow R X ih))
    rw [pow_succ]
    exact Submodule.mul_mem_mul ih (Submodule.mem_sup_right ⟨X, rfl⟩)

/-- The generators of the tensor algebra, as a submodule. -/
local notation "M_T" => LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L)

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
      Derivation.map_one_eq_zero, add_zero,
      show algHom R L (TensorAlgebra.ι R Y) = ι R L Y from rfl, sub_self]
    exact zero_mem _
  | succ n ih =>
    rw [pow_succ] at ht
    refine Submodule.mul_induction_on ht (fun x hx m hm ↦ ?_) (fun x y hx hy ↦ ?_)
    · obtain ⟨Y, rfl⟩ := hm
      have hU : UniversalEnvelopingAlgebra.mkAlgHom R L (x * TensorAlgebra.ι R Y) =
          UniversalEnvelopingAlgebra.mkAlgHom R L x * UniversalEnvelopingAlgebra.ι R Y := by
        rw [map_mul]; rfl
      have hW : UniversalEnvelopingAlgebra.mkAlgHom R L x ∈
          UniversalEnvelopingAlgebra.filtration R L (n + 1) :=
        UniversalEnvelopingAlgebra.pow_range_ι_le_filtration R L _ (by
          rw [← UniversalEnvelopingAlgebra.map_mkAlgHom_pow]
          exact Submodule.mem_map_of_mem hx)
      rw [hU, toSymmetricAlgebra_mul_ι, act_apply, map_mul,
        show algHom R L (TensorAlgebra.ι R Y) = ι R L Y from rfl, add_sub_right_comm, ← sub_mul]
      refine add_mem ?_ (derivation_mem_one_sup_pow R Y (toSymmetricAlgebra_mem_pow R hW))
      rw [pow_succ]
      exact Submodule.mul_mem_mul (ih hx) (Submodule.mem_sup_right ⟨Y, rfl⟩)
    · rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy

/-! ### Injectivity -/

/-- An element of the symmetric algebra that is a sum of products of at most `m` generators has
no component of degree above `m`. -/
private theorem decompose_eq_zero_of_mem {m : ℕ} {s : SymmetricAlgebra R L}
    (hs : s ∈ (1 ⊔ M_S) ^ m) {j : ℕ} (hj : m < j) :
    (DirectSum.decompose (fun n : ℕ ↦ M_S ^ n) s j : SymmetricAlgebra R L) = 0 := by
  induction m generalizing s with
  | zero =>
    rw [pow_zero] at hs
    exact DirectSum.decompose_of_mem_ne _ (i := 0) (by rwa [pow_zero]) hj.ne
  | succ m ih =>
    rw [Submodule.one_sup_pow_succ] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hs
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      ih ha (Nat.lt_of_succ_lt hj), DirectSum.decompose_of_mem_ne _ hb hj.ne, add_zero]

/-- A homogeneous element of degree `m + 1` that is a sum of products of at most `m` generators
is zero. -/
private theorem eq_zero_of_mem_pow_of_mem {m : ℕ} {s : SymmetricAlgebra R L}
    (hs : s ∈ M_S ^ (m + 1)) (hs' : s ∈ (1 ⊔ M_S) ^ m) : s = 0 := by
  rw [← DirectSum.decompose_of_mem_same (fun n : ℕ ↦ M_S ^ n) hs]
  exact decompose_eq_zero_of_mem R hs' (Nat.lt_succ_self m)

theorem eq_zero_of_toSymmetricAlgebra_eq_zero {m : ℕ} {u : UniversalEnvelopingAlgebra R L}
    (hu : u ∈ UniversalEnvelopingAlgebra.filtration R L m) (h : toSymmetricAlgebra R u = 0) :
    u = 0 := by
  induction m generalizing u with
  | zero =>
    rw [UniversalEnvelopingAlgebra.filtration_zero] at hu
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hu
    rw [toSymmetricAlgebra_algebraMap, SymmetricAlgebra.algebraMap_eq_zero_iff] at h
    rw [h, map_zero]
  | succ m ih =>
    rw [UniversalEnvelopingAlgebra.filtration_succ] at hu
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    rw [← UniversalEnvelopingAlgebra.map_mkAlgHom_pow] at hw
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hw
    change toSymmetricAlgebra R (v + UniversalEnvelopingAlgebra.mkAlgHom R L t) = 0 at h
    change v + UniversalEnvelopingAlgebra.mkAlgHom R L t = 0
    rw [map_add] at h
    have hS : algHom R L t ∈ (1 ⊔ M_S) ^ m := by
      have e : algHom R L t = -toSymmetricAlgebra R v -
          (toSymmetricAlgebra R (UniversalEnvelopingAlgebra.mkAlgHom R L t) - algHom R L t) := by
        linear_combination h
      rw [e]
      exact sub_mem (neg_mem (toSymmetricAlgebra_mem_pow R hv))
        (toSymmetricAlgebra_mkAlgHom_sub_mem R m ht)
    have h0 := eq_zero_of_mem_pow_of_mem R
      (by rw [← SymmetricAlgebra.map_algHom_pow]; exact Submodule.mem_map_of_mem ht) hS
    exact ih (add_mem hv (UniversalEnvelopingAlgebra.mkAlgHom_mem_of_algHom_eq_zero R L ht h0))
      ((map_add _ _ _).trans h)

/-- The enveloping algebra acts freely on `1` in the symmetric algebra. -/
theorem toSymmetricAlgebra_injective :
    Function.Injective (toSymmetricAlgebra R (L := L)) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨m, hm⟩ := UniversalEnvelopingAlgebra.exists_mem_filtration R L u
  exact eq_zero_of_toSymmetricAlgebra_eq_zero R hm hu

/-- The enveloping algebra of the commutator Lie algebra of a pre-Lie algebra is its symmetric
algebra, as a module: the Poincaré–Birkhoff–Witt theorem for these Lie algebras. -/
def equivSymmetricAlgebra : UniversalEnvelopingAlgebra R L ≃ₗ[R] SymmetricAlgebra R L :=
  LinearEquiv.ofBijective (toSymmetricAlgebra R)
    ⟨toSymmetricAlgebra_injective R, toSymmetricAlgebra_surjective R⟩

@[simp] theorem equivSymmetricAlgebra_apply (u : UniversalEnvelopingAlgebra R L) :
    equivSymmetricAlgebra R u = toSymmetricAlgebra R u := rfl

/-- A pre-Lie algebra embeds in the enveloping algebra of its commutator Lie algebra. -/
theorem ι_injective :
    Function.Injective (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L) :=
  fun X Y h ↦ SymmetricAlgebra.ι_injective <| by
    rw [← toSymmetricAlgebra_ι, ← toSymmetricAlgebra_ι, h]

end RightPreLieAlgebra
