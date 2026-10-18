/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.BirkhoffFactorization
public import Linglib.Core.RingTheory.HopfAlgebra.Convolution

/-!
# The Connes–Kreimer Hopf algebra of nonplanar rooted trees

The pruning bialgebra on `ConnesKreimer R (UnorderedTree α)` (`Coproduct/Pruning.lean`) is a Hopf
algebra over any commutative ring: the Connes–Kreimer Hopf algebra of nonplanar, not necessarily
binary, rooted trees.

The antipode is the inductive formula `S(x) = −x − Σ S(x′) · x″` of a graded connected bialgebra
(Foissy's notes, §1.3, Lemma 2). As the algebra is commutative, the antipode is an algebra map,
so it is determined by its values on trees. Summing over every admissible cut `(F, T')` of a tree
`T` (crown forest `F`, trunk `T'`), including the empty cut `(0, T)` that supplies the `−T` term,

  `S(T) = −Σ_{(F, T')} (Π_{t ∈ F} S(t)) · T'`.

This is the Bogolyubov recursion of `ConnesKreimer.birkhoffMinus` for the identity character and
the operator `P = -id`, so the antipode is defined as that negative part, and `S ⋆ id = 1` is the
statement that at `P = -id` the negative part is a convolution inverse. With the antipode in hand,
`φ₊ = φ₋ ⋆ φ` becomes the Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊` of a character.

## Main definitions

* `ConnesKreimer.antipodeAlgHomN`: the antipode, the negative part of the identity at `P = -id`.

## Main results

* `ConnesKreimer.antipodeAlgHomN_convMul_id`, `ConnesKreimer.id_convMul_antipodeAlgHomN`:
  `S ⋆ id = 1 = id ⋆ S` in the convolution monoid of algebra endomorphisms.
* The `HopfAlgebra R (ConnesKreimer R (UnorderedTree α))` instance, over any commutative ring.
* `ConnesKreimer.antipode_ofTree`: the inductive formula for the antipode on a tree.
* `ConnesKreimer.birkhoffFactorization`: `φ = (φ₋ ∘ S) ⋆ φ₊` for a character `φ`.

## Implementation notes

The construction needs only a commutative ring (for the negation), and the bialgebra only a
commutative semiring.

The recursion descends on `UnorderedTree.numNodes`, the grading by weight: every crown tree has
fewer vertices than `T` (`cutSummandsN_crown_numNodes_lt`). The recursion makes `S` a left
convolution inverse of the identity. Foissy's proof also takes a right antipode, realized here by
the recursion `R(T) = −T − Σ_{F ≠ 0} F · R(T')` on the trunk; the two agree by
`left_inv_eq_right_inv` in the convolution monoid `WithConv (H →ₐ[R] H)`.

## TODO

* State the Bogolyubov recursion, and with it the antipode, for any connected graded bialgebra
  once mathlib has one (mathlib4#39849).
* Foissy's closed form `S(t) = Σ (−1)^(n_c + 1) W^c(t)` over the non-total cuts `c` of `t`
  ([foissy-introduction-hopf-algebras-trees] §1.3, Theorem 2).

## References

* [connes-kreimer-1998]
* [connes-kreimer-2000]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open UnorderedTree WithConv

namespace ConnesKreimer

variable {R : Type*} [CommRing R] {α : Type*}

/-- The antipode, the Bogolyubov negative part of the identity character at `P = -id`. -/
noncomputable def antipodeAlgHomN :
    ConnesKreimer R (UnorderedTree α) →ₐ[R] ConnesKreimer R (UnorderedTree α) :=
  birkhoffMinus LinearMap.id (-AddMonoidHom.id _)

/-- `S ⋆ id = 1`, the left inverse law of the negative part at `P = -id`. An input to the instance;
afterwards this is `AlgHom.antipode_id_cancel`. -/
theorem antipodeAlgHomN_convMul_id :
    toConv (antipodeAlgHomN (R := R) (α := α)) * toConv (AlgHom.id R _) = 1 :=
  birkhoffMinus_neg_id_convMul (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))

/-- The right antipode on a tree, recursing on the trunk of the nonempty cuts:
`R(T) = −T − Σ_{(F, T'), F ≠ 0} F · R(T')`. -/
private noncomputable def antipodeRightTreeN (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) :=
  -ofTree T - (((cutSummandsN T).filter (¬ ·.1.card = 0)).attach.map fun p ↦
    of' p.1.1 * antipodeRightTreeN p.1.2).sum
termination_by T.numNodes
decreasing_by
  obtain ⟨hp, h⟩ := Multiset.mem_filter.1 p.2
  exact cutSummandsN_trunk_numNodes_lt hp (Multiset.card_eq_zero.not.1 h)

private theorem antipodeRightTreeN_unfold (T : UnorderedTree α) :
    antipodeRightTreeN (R := R) T = -ofTree T -
      (((cutSummandsN T).filter (¬ ·.1.card = 0)).map fun p ↦
        of' p.1 * antipodeRightTreeN p.2).sum := by
  rw [antipodeRightTreeN]
  exact congrArg (fun s ↦ -ofTree T - s.sum) (Multiset.attach_map_val' _
    fun p : Forest (UnorderedTree α) × UnorderedTree α ↦ of' p.1 * antipodeRightTreeN (R := R) p.2)

/-- `id ⋆ R = 1`, since the empty cut contributes `R(T)`, which cancels the rest. -/
private theorem id_convMul_aeval_antipodeRightTreeN :
    toConv (AlgHom.id R _) * toConv (aeval (antipodeRightTreeN (R := R) (α := α))) = 1 := by
  refine ofConv_injective (algHom_ext_ofTree fun T ↦ ?_)
  simp only [AlgHom.convMul_apply, coalgebra_comul_apply, comulAlgHomN_apply_ofTree, comulTreeN,
    comulTreeNG, map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one, aeval_ofTree]
  rw [← Multiset.filter_add_not (·.1.card = 0) (cutSummandsN T), Multiset.map_add,
    Multiset.sum_add, cutSummandsN_filter_empty, Multiset.map_singleton, Multiset.sum_singleton,
    of'_zero, one_mul, antipodeRightTreeN_unfold T, AlgHom.convOne_apply, coalgebra_counit_apply,
    counit_ofTree, map_zero]
  abel

/-- `id ⋆ S = 1`, since `S` equals the right antipode. An input to
the instance; afterwards this is `LinearMap.id_mul_antipode`. -/
theorem id_convMul_antipodeAlgHomN :
    toConv (AlgHom.id R _) * toConv (antipodeAlgHomN (R := R) (α := α)) = 1 :=
  left_inv_eq_right_inv antipodeAlgHomN_convMul_id (id_convMul_aeval_antipodeRightTreeN (R := R))
    ▸ id_convMul_aeval_antipodeRightTreeN

noncomputable instance : HopfAlgebra R (ConnesKreimer R (UnorderedTree α)) :=
  .ofConvInverse antipodeAlgHomN.toLinearMap
    congr(toConv ($(antipodeAlgHomN_convMul_id (R := R) (α := α))).ofConv.toLinearMap)
    congr(toConv ($(id_convMul_antipodeAlgHomN (R := R) (α := α))).ofConv.toLinearMap)

theorem antipodeAlgHom_eq_antipodeAlgHomN :
    HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α)) = antipodeAlgHomN :=
  rfl

/-- The antipode on a tree, `S(T) = −Σ_{(F, T') ∈ cutSummandsN T} (Π_{t ∈ F} S(t)) · T'`. -/
theorem antipode_ofTree (T : UnorderedTree α) :
    HopfAlgebra.antipode R (ofTree T : ConnesKreimer R (UnorderedTree α)) =
      -((cutSummandsN T).map fun p ↦
        (p.1.map fun t ↦ HopfAlgebra.antipode R (ofTree t)).prod * ofTree p.2).sum := by
  change antipodeAlgHomN (R := R) (ofTree T) = -((cutSummandsN T).map fun p ↦
    (p.1.map fun t ↦ antipodeAlgHomN (ofTree t)).prod * ofTree p.2).sum
  rw [antipodeAlgHomN, birkhoffMinus_apply_ofTree, birkhoffMinusTree_eq, birkhoffPrepTree]
  simp only [birkhoffMinus_apply_ofTree, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    LinearMap.id_apply]

/-! ### Birkhoff factorization through the antipode -/

variable {ℛ : Type*} [CommSemiring ℛ] [Algebra R ℛ]

/-- The Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊` of a character, from `φ₊ = φ₋ ⋆ φ` and the
left inverse `φ₋ ∘ S` of `φ₋`. -/
theorem birkhoffFactorization (P : ℛ →+ ℛ) (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    toConv φ
      = toConv ((birkhoffMinus φ.toLinearMap P).comp
            (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
          * toConv (birkhoffPlus φ.toLinearMap P) := by
  rw [← birkhoffPlus_eq_convMul, ← mul_assoc, AlgHom.comp_antipode_cancel, one_mul]

end ConnesKreimer
