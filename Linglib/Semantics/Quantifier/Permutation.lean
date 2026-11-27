module

public import Linglib.Semantics.Quantifier.Negation
public import Linglib.Semantics.Quantifier.NumberTree
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The permutations of the universe acting on quantifiers

The permutations of a universe `α` act on its subsets, and so on the quantifiers `Set α → Prop`
through the scope: `(DomMulAct.mk σ • Q) B = Q (σ • B)`. A quantifier is quantity invariant
exactly when this action fixes it. The action commutes with the two negations of a quantifier, so
the negations of a quantity-invariant quantifier are quantity invariant. On a finite universe the
orbits of the subsets are the sets of subsets with a given number of elements, so a quantifier is
quantity invariant exactly when it depends only on the number of elements of its scope.

## Main results

* `Quantifier.quantityInvariant_iff_mem_fixedPoints`: quantity invariance as being a fixed point.
* `Quantifier.QuantityInvariant.smul`: the negations preserve quantity invariance.
* `Quantifier.mem_orbit_perm_iff_ncard_eq`: the orbits of the subsets of a finite universe.
* `Quantifier.quantityInvariant_iff_forall_ncard_eq`: a quantifier on a finite universe is
  quantity invariant if and only if it depends only on the number of elements of its scope.

## Implementation notes

The action through the scope is mathlib's action of `DomMulAct M` on a function type whose domain
`M` acts on, as for the negations, here with the permutations acting on sets by image.

## References

* [mostowski-1957]
* [van-benthem-1984]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
-/

@[expose] public section

open Pointwise DomMulAct

namespace Quantifier

variable {α : Type*} {Q : Quantifier α}

/-- A permutation of the universe acts on a quantifier through its scope. -/
theorem mk_perm_smul_apply (σ : Equiv.Perm α) (Q : Quantifier α) (B : Set α) :
    (mk σ • Q) B = Q (σ • B) := rfl

/-- A quantifier is quantity invariant if and only if the permutations of the universe, acting
through the scope, fix it. -/
theorem quantityInvariant_iff_mem_fixedPoints :
    Q.QuantityInvariant ↔ Q ∈ MulAction.fixedPoints (Equiv.Perm α)ᵈᵐᵃ (Quantifier α) := by
  have e (σ : Equiv.Perm α) (B : Set α) : σ • B = ⇑σ.symm ⁻¹' B := σ.image_eq_preimage_symm B
  simp only [MulAction.mem_fixedPoints, mk.surjective.forall, QuantityInvariant, funext_iff,
    mk_perm_smul_apply, eq_iff_iff]
  exact ⟨fun h σ B ↦ e σ B ▸ h σ.symm B, fun h σ B ↦ by simpa [e] using h σ.symm B⟩

/-- Permuting the universe commutes with complementing a set. -/
instance : SMulCommClass (Equiv.Perm α) Polarity (Set α) := ⟨fun σ p B ↦ by
  cases p <;> simp [Set.smul_set_compl]⟩

/-- The negations of a quantity-invariant quantifier are quantity invariant. -/
theorem QuantityInvariant.smul (h : Q.QuantityInvariant) (p : Polarity × DomMulAct Polarity) :
    (p • Q).QuantityInvariant := by
  rw [quantityInvariant_iff_mem_fixedPoints] at h ⊢
  obtain ⟨o, i⟩ := p
  intro c
  change c • o • i • Q = o • i • Q
  rw [smul_comm c o, smul_comm c i, h c]

/-- The inner negation of a quantity-invariant quantifier is quantity invariant. -/
theorem QuantityInvariant.innerNeg (h : Q.QuantityInvariant) : Q.innerNeg.QuantityInvariant :=
  h.smul (1, mk Polarity.negative)

/-- The dual of a quantity-invariant quantifier is quantity invariant. -/
theorem QuantityInvariant.dual (h : Q.QuantityInvariant) : Q.dual.QuantityInvariant :=
  h.smul (Polarity.negative, mk Polarity.negative)

/-- On a finite universe, two sets are related by a permutation of the universe if and only if
they have the same number of elements. -/
theorem mem_orbit_perm_iff_ncard_eq [Finite α] {B B' : Set α} :
    B' ∈ MulAction.orbit (Equiv.Perm α) B ↔ B'.ncard = B.ncard := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨σ, rfl⟩
    exact Set.ncard_image_of_injective B σ.injective
  · have hQ : QuantityInvariant (· ∈ MulAction.orbit (Equiv.Perm α) B) := by
      rw [quantityInvariant_iff_mem_fixedPoints]
      refine mk.surjective.forall.2 fun σ ↦ funext fun C ↦ propext ?_
      change σ • C ∈ MulAction.orbit (Equiv.Perm α) B ↔ C ∈ MulAction.orbit (Equiv.Perm α) B
      rw [← MulAction.orbit_eq_iff, MulAction.orbit_smul, MulAction.orbit_eq_iff]
    exact (hQ.iff_of_ncard_eq h.symm).1 (MulAction.mem_orbit_self B)

/-- On a finite universe, a quantifier is quantity invariant if and only if it depends only on the
number of elements of its scope. -/
theorem quantityInvariant_iff_forall_ncard_eq [Finite α] :
    Q.QuantityInvariant ↔ ∀ B B' : Set α, B.ncard = B'.ncard → (Q B ↔ Q B') :=
  ⟨fun h _ _ hB ↦ h.iff_of_ncard_eq hB, fun h σ B ↦ h _ _ <| by
    rw [show ⇑σ ⁻¹' B = σ.symm '' B from (σ.symm.image_eq_preimage_symm B).symm]
    exact Set.ncard_image_of_injective B σ.symm.injective⟩

end Quantifier
