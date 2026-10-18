/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.HopfAlgebra
public import Linglib.Core.Algebra.RotaBaxter

/-!
# Birkhoff factorization on the Connes–Kreimer Hopf algebra

Let `φ : H → ℛ` be a linear map from the Connes–Kreimer Hopf algebra into a commutative algebra
and `P` an additive operator on `ℛ`. The Bogolyubov recursion over the cuts `(F, T')` of a tree
defines the preparation `φ̃(T) = Σ (Π_{t ∈ F} φ₋(t)) · φ(T')`, the negative part `φ₋(T) = P (φ̃(T))`
and the renormalized part `φ₊(T) = φ̃(T) + φ₋(T)`, each extended multiplicatively to forests.
Connes and Kreimer's construction over a ring, with a Rota–Baxter operator `R` of weight `-1`, is
the case `P = -R`, where `φ₋ = -R(φ̃)` and `φ₊ = (1 - R)(φ̃)`; over a semiring, as in Marcolli and
Tedeschi, `P` is itself the operator, of weight `+1`. Either way `P` has weight `+1`.

For a unital `φ`, `φ₊ = φ₋ ⋆ φ` holds on trees for every `P`, and on all of `H` when `φ` is a
character. The Rota–Baxter identity puts the two parts in subalgebras: if `P` has weight `+1`, then
`φ₋` sends every nonempty forest into the range of `P` and `φ₊` into the range of `id + P`. Over a
ring the antipode `S` turns `φ₊ = φ₋ ⋆ φ` into the Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊`, and
at `φ = id`, `P = -id` the negative part is the antipode itself.

## Main definitions

* `ConnesKreimer.birkhoffMinus`: the negative part `φ₋`.
* `ConnesKreimer.birkhoffPrepTree`: the Bogolyubov preparation `φ̃` on a tree.
* `ConnesKreimer.birkhoffPlus`: the renormalized part `φ₊`.

## Main results

* `ConnesKreimer.convMul_birkhoffMinus_apply_ofTree`, `ConnesKreimer.birkhoffPlus_eq_convMul`:
  `φ₊ = φ₋ ⋆ φ`, on trees and for characters.
* `ConnesKreimer.birkhoffMinus_of'_mem_range`, `ConnesKreimer.birkhoffPlus_of'_mem_range`: for `P`
  of weight `+1`, the two parts land in the ranges of `P` and of `id + P`.
* `ConnesKreimer.birkhoffPlus_eq_self`: a character that `P` kills on every tree is its own
  renormalized part.
* `ConnesKreimer.birkhoffFactorization`: `φ = (φ₋ ∘ S) ⋆ φ₊` for a character `φ`.
* `ConnesKreimer.birkhoffMinus_id_neg_eq_antipodeAlgHomN`: at `φ = id` and `P = -id`, `φ₋` is the
  antipode.

## Implementation notes

The weight of `P` is stated in `ℕ`, which acts canonically on every semiring. On Laurent series
the base ring also acts through `HahnSeries.powerSeriesAlgebra`, an action not definitionally
equal to the coefficientwise one.

Mathlib's convolution group `AlgHom.convGroup` asks the target to be a bialgebra, so the inverse
`φ₋ ∘ S` of `φ₋` comes from the antipode law directly (`antipodeComp_convMul_self`).

## References

* [connes-kreimer-2000]
* [ebrahimi-fard-guo-kreimer-2004]
* [marcolli-tedeschi-2015]
-/

@[expose] public section

open RoseTree UnorderedTree WithConv

namespace ConnesKreimer

open scoped TensorProduct

section Semiring

variable {R ℛ : Type*} [CommSemiring R] [CommSemiring ℛ] [Algebra R ℛ] {α : Type*}
  (φ : ConnesKreimer R (UnorderedTree α) →ₗ[R] ℛ) (P : ℛ →+ ℛ)

/-- The negative part on a tree,
`φ₋(T) = P (Σ_{(F, T') ∈ cutSummandsN T} (Π_{t ∈ F} φ₋(t)) · φ(T'))`, by recursion on the number
of vertices. -/
noncomputable def birkhoffMinusTree (T : UnorderedTree α) : ℛ :=
  P ((cutSummandsN T).attach.map fun p ↦
    (p.1.1.attach.map fun t ↦ birkhoffMinusTree t.1).prod * φ (ofTree p.1.2)).sum
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt p.2 t.2

/-- The negative part `φ₋`, the multiplicative extension of `birkhoffMinusTree` to forests. -/
noncomputable def birkhoffMinus : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ :=
  aeval (birkhoffMinusTree φ P)

@[simp] theorem birkhoffMinus_apply_of' (F : Forest (UnorderedTree α)) :
    birkhoffMinus φ P (of' F) = (F.map (birkhoffMinusTree φ P)).prod :=
  aeval_of' _ F

@[simp] theorem birkhoffMinus_apply_ofTree (T : UnorderedTree α) :
    birkhoffMinus φ P (ofTree T) = birkhoffMinusTree φ P T :=
  aeval_ofTree _ T

/-- The Bogolyubov preparation on a tree,
`φ̃(T) = Σ_{(F, T') ∈ cutSummandsN T} (Π_{t ∈ F} φ₋(t)) · φ(T')`. -/
noncomputable def birkhoffPrepTree (T : UnorderedTree α) : ℛ :=
  ((cutSummandsN T).map fun p ↦ (p.1.map (birkhoffMinusTree φ P)).prod * φ (ofTree p.2)).sum

theorem birkhoffMinusTree_eq (T : UnorderedTree α) :
    birkhoffMinusTree φ P T = P (birkhoffPrepTree φ P T) := by
  rw [birkhoffMinusTree]
  simp only [Multiset.attach_map_val' _ (birkhoffMinusTree φ P)]
  exact congrArg (fun s ↦ P s.sum) (Multiset.attach_map_val' _
    fun p : Forest (UnorderedTree α) × UnorderedTree α ↦
      (p.1.map (birkhoffMinusTree φ P)).prod * φ (ofTree p.2))

/-- The renormalized part on a tree, `φ₊(T) = φ̃(T) + φ₋(T)`. -/
noncomputable def birkhoffPlusTree (T : UnorderedTree α) : ℛ :=
  birkhoffPrepTree φ P T + birkhoffMinusTree φ P T

/-- The renormalized part `φ₊`, the multiplicative extension of `birkhoffPlusTree` to forests. -/
noncomputable def birkhoffPlus : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ :=
  aeval (birkhoffPlusTree φ P)

@[simp] theorem birkhoffPlus_apply_of' (F : Forest (UnorderedTree α)) :
    birkhoffPlus φ P (of' F) = (F.map (birkhoffPlusTree φ P)).prod :=
  aeval_of' _ F

@[simp] theorem birkhoffPlus_apply_ofTree (T : UnorderedTree α) :
    birkhoffPlus φ P (ofTree T) = birkhoffPlusTree φ P T :=
  aeval_ofTree _ T

/-! ### The factorization `φ₊ = φ₋ ⋆ φ` -/

/-- For a unital `φ`, `φ₊ = φ₋ ⋆ φ` on trees, since the term `T ⊗ 1` of the coproduct contributes
`φ₋(T)` and the cuts contribute the preparation `φ̃(T)`. -/
theorem convMul_birkhoffMinus_apply_ofTree (hφ : φ 1 = 1) (T : UnorderedTree α) :
    (toConv (birkhoffMinus φ P).toLinearMap * toConv φ) (ofTree T) = birkhoffPlusTree φ P T := by
  rw [LinearMap.convMul_apply, coalgebra_comul_apply, comulAlgHomN_apply_ofTree, comulTreeN,
    comulTreeNG]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    birkhoffMinus_apply_ofTree, birkhoffMinus_apply_of', hφ, mul_one]
  rw [← birkhoffPrepTree, birkhoffPlusTree, add_comm]

/-- `φ₊ = φ₋ ⋆ φ` for a character `φ`, both sides being characters that agree on trees. -/
theorem birkhoffPlus_eq_convMul (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    toConv (birkhoffMinus φ.toLinearMap P) * toConv φ
      = toConv (birkhoffPlus φ.toLinearMap P) := by
  refine ofConv_injective (algHom_ext_ofTree fun T ↦ ?_)
  rw [ofConv_toConv, birkhoffPlus_apply_ofTree]
  exact convMul_birkhoffMinus_apply_ofTree φ.toLinearMap P (map_one φ) T

/-! ### The subalgebras of the factorization -/

variable {φ P}

/-- For `P` of weight `+1`, the negative part sends every nonempty forest into the range of `P`. -/
theorem birkhoffMinus_of'_mem_range (hP : IsRotaBaxter (1 : ℕ) ⇑P)
    {F : Forest (UnorderedTree α)} (hF : F ≠ 0) : birkhoffMinus φ P (of' F) ∈ Set.range P := by
  rw [birkhoffMinus_apply_of']
  refine Multiset.prod_induction_nonempty _ (fun _ _ ↦ hP.mul_mem_range) (by simpa using hF) ?_
  simp only [Multiset.mem_map]
  rintro _ ⟨T, -, rfl⟩
  exact ⟨_, (birkhoffMinusTree_eq φ P T).symm⟩

/-- For `P` of weight `+1`, the renormalized part sends every nonempty forest into the range of
`id + P`. -/
theorem birkhoffPlus_of'_mem_range (hP : IsRotaBaxter (1 : ℕ) ⇑P)
    {F : Forest (UnorderedTree α)} (hF : F ≠ 0) :
    birkhoffPlus φ P (of' F) ∈ Set.range fun x ↦ x + P x := by
  have h (a b : ℛ) := hP.mul_mem_range_smul_add (a := a) (b := b)
  simp only [one_smul] at h
  rw [birkhoffPlus_apply_of']
  refine Multiset.prod_induction_nonempty _ h (by simpa using hF) ?_
  simp only [Multiset.mem_map]
  rintro _ ⟨T, -, rfl⟩
  exact ⟨_, by rw [birkhoffPlusTree, birkhoffMinusTree_eq]⟩

/-- If `P` kills `φ` on every tree, the negative part vanishes: the empty cut contributes
`P (φ T) = 0`, and every other cut has a crown tree, where `φ₋` vanishes by recursion. -/
theorem birkhoffMinusTree_eq_zero (h : ∀ T, P (φ (ofTree T)) = 0) (T : UnorderedTree α) :
    birkhoffMinusTree φ P T = 0 := by
  rw [birkhoffMinusTree_eq, birkhoffPrepTree, map_multiset_sum]
  refine Multiset.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hy
  rcases eq_or_ne p.1 0 with hempty | hne
  · rw [hempty, Multiset.map_zero, Multiset.prod_zero, one_mul]
    exact h p.2
  · obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hne
    rw [Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨t, ht, birkhoffMinusTree_eq_zero h t⟩),
      zero_mul, map_zero]
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt hp ht

/-- If `P` kills `φ` on every tree, the renormalized part on a tree is the value of `φ`. -/
theorem birkhoffPlusTree_eq_of_forall (h : ∀ T, P (φ (ofTree T)) = 0) (T : UnorderedTree α) :
    birkhoffPlusTree φ P T = φ (ofTree T) := by
  rw [birkhoffPlusTree, birkhoffMinusTree_eq_zero h, add_zero, birkhoffPrepTree,
    ← Multiset.filter_add_not (·.1.card = 0) (cutSummandsN T), Multiset.map_add, Multiset.sum_add,
    cutSummandsN_filter_empty, Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero,
    Multiset.prod_zero, one_mul]
  refine (congrArg _ (Multiset.sum_eq_zero fun x hx ↦ ?_)).trans (add_zero _)
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.mp
    (Nat.pos_of_ne_zero (Multiset.mem_filter.mp hp).2)
  rw [Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨t, ht, birkhoffMinusTree_eq_zero h t⟩),
    zero_mul]

/-- A character that `P` kills on every tree is its own renormalized part. -/
theorem birkhoffPlus_eq_self {φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ}
    (h : ∀ T, P (φ (ofTree T)) = 0) : birkhoffPlus φ.toLinearMap P = φ :=
  algHom_ext_ofTree fun T ↦ by
    rw [birkhoffPlus_apply_ofTree, birkhoffPlusTree_eq_of_forall h, AlgHom.toLinearMap_apply]

end Semiring

/-! ### The factorization `φ = (φ₋ ∘ S) ⋆ φ₊` over a ring -/

section Ring

variable {R ℛ : Type*} [CommRing R] [CommSemiring ℛ] [Algebra R ℛ] {α : Type*} (P : ℛ →+ ℛ)

/-- For a character `ψ : H →ₐ[R] ℛ`, the composite `ψ ∘ S` is a left convolution inverse of `ψ`,
by the antipode law `S ⋆ id = 1` transported along `ψ`. -/
theorem antipodeComp_convMul_self (ψ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    toConv (ψ.comp (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
        * toConv ψ
      = (1 : WithConv (ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ)) := by
  have h := AlgHom.comp_convMul_distrib ψ
    (toConv (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
    (toConv (AlgHom.id R (ConnesKreimer R (UnorderedTree α))))
  rw [AlgHom.antipode_id_cancel, AlgHom.comp_id] at h
  apply ofConv_injective
  rw [← h]
  simp only [AlgHom.convOne_def, ofConv_toConv, ← AlgHom.comp_assoc,
    Subsingleton.elim (ψ.comp (Algebra.ofId R (ConnesKreimer R (UnorderedTree α))))
      (Algebra.ofId R ℛ)]

/-- The Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊` of a character, from `φ₊ = φ₋ ⋆ φ` and the
inverse `φ₋ ∘ S` of `φ₋`. -/
theorem birkhoffFactorization (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    toConv φ
      = toConv ((birkhoffMinus φ.toLinearMap P).comp
            (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
          * toConv (birkhoffPlus φ.toLinearMap P) := by
  rw [← birkhoffPlus_eq_convMul, ← mul_assoc, antipodeComp_convMul_self, one_mul]

/-- At `φ = id` and `P = -id`, the negative part on a tree is the antipode: the two recursions
coincide summand by summand. -/
theorem birkhoffMinusTree_id_neg_eq_antipodeTreeN (T : UnorderedTree α) :
    birkhoffMinusTree (LinearMap.id : ConnesKreimer R (UnorderedTree α) →ₗ[R] _)
      (-AddMonoidHom.id _) T = antipodeTreeN T := by
  rw [birkhoffMinusTree_eq, birkhoffPrepTree, antipodeTreeN_unfold, AddMonoidHom.neg_apply,
    AddMonoidHom.id_apply, neg_inj]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp ↦ ?_)
  rw [LinearMap.id_apply]
  exact congrArg (· * ofTree p.2) (congrArg Multiset.prod (Multiset.map_congr rfl
    fun t ht ↦ birkhoffMinusTree_id_neg_eq_antipodeTreeN t))
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt hp ht

/-- At `φ = id` and `P = -id`, the negative part is the antipode. -/
theorem birkhoffMinus_id_neg_eq_antipodeAlgHomN :
    birkhoffMinus (LinearMap.id : ConnesKreimer R (UnorderedTree α) →ₗ[R] _) (-AddMonoidHom.id _)
      = antipodeAlgHomN :=
  congrArg aeval (funext birkhoffMinusTree_id_neg_eq_antipodeTreeN)

end Ring

end ConnesKreimer
