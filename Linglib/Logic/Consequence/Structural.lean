/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.RelClasses

/-!
# Structural rules

A relation $\Gamma \vdash \Delta$ between sets of formulas, read as "if every member of $\Gamma$
holds then some member of $\Delta$ does", may obey the three structural rules of [scott-1974]:
it is monotone when it survives added premises and conclusions, reflexive when each formula
yields itself, and [transitive](##IsTransitive) when it is closed under cut. A monotone reflexive
relation [holds between overlapping sets](##overlap). A transitive one admits [cut on a single
formula](##IsTransitive.cut), and if also monotone it [passes through sets of intermediate
conclusions](##IsTransitive.trans), so that its restriction to single formulas [is transitive in
the ordinary sense](##IsTransitive.isTrans).

## Implementation notes

For a relation `r` between sets of formulas, monotonicity is `Monotone (Function.uncurry r)`
and reflexivity is `Std.Refl fun φ ψ ↦ r {φ} {ψ}`. Transitivity is the cut for sets of
[shoesmith-smiley-1978], which quantifies over the partitions of a set `Z` of cut formulas; a
partition is given by its first block `Z₁ ⊆ Z`, the second being `Z \ Z₁`. Transitivity of `r` as
a binary relation on sets would be a different rule, since a set is read conjunctively as premises
and disjunctively as conclusions.

## References

* [scott-1974]
* [shoesmith-smiley-1978]
-/

@[expose] public section

namespace Consequence

variable {Formula : Type*} {r : Set Formula → Set Formula → Prop} {Γ Δ Θ : Set Formula}
  {φ : Formula}

/-- A relation between sets of formulas is transitive when it is closed under cut for sets
([shoesmith-smiley-1978], §2.1): `Γ ⇒ Δ` holds if `Γ, Z₁ ⇒ Z₂, Δ` holds for every partition
`Z₁, Z₂` of a set `Z` of cut formulas. -/
def IsTransitive (r : Set Formula → Set Formula → Prop) : Prop :=
  ∀ ⦃Γ Δ : Set Formula⦄ (Z : Set Formula), (∀ Z₁ ⊆ Z, r (Γ ∪ Z₁) (Z \ Z₁ ∪ Δ)) → r Γ Δ

/-- A monotone relation that holds between each formula and itself holds between overlapping
sets, rule (R) of [scott-1974]. -/
theorem overlap (hm : Monotone (Function.uncurry r)) (hr : Std.Refl fun φ ψ ↦ r {φ} {ψ})
    (h : (Γ ∩ Δ).Nonempty) : r Γ Δ :=
  let ⟨φ, hΓ, hΔ⟩ := h
  hm (show (({φ}, {φ}) : Set Formula × Set Formula) ≤ (Γ, Δ) from
    ⟨Set.singleton_subset_iff.2 hΓ, Set.singleton_subset_iff.2 hΔ⟩) (hr.refl φ)

namespace IsTransitive

/-- Cut on one formula, rule (T) of [scott-1974]. -/
theorem cut (ht : IsTransitive r) (h₁ : r (insert φ Γ) Δ) (h₂ : r Γ (insert φ Δ)) : r Γ Δ :=
  ht {φ} fun Z₁ hZ ↦ by
    rcases Set.subset_singleton_iff_eq.1 hZ with rfl | rfl
    · simpa using h₂
    · simpa using h₁

/-- Whatever follows from single conclusions of `Γ` follows from `Γ`. -/
theorem trans (ht : IsTransitive r) (hm : Monotone (Function.uncurry r))
    (h₁ : ∀ θ ∈ Θ, r Γ {θ}) (h₂ : r Θ Δ) : r Γ Δ :=
  ht Θ fun Z₁ _ ↦ by
    by_cases h : Θ ⊆ Z₁
    · exact hm (show (Θ, Δ) ≤ (Γ ∪ Z₁, Θ \ Z₁ ∪ Δ) from
        ⟨h.trans Set.subset_union_right, Set.subset_union_right⟩) h₂
    · obtain ⟨θ, hθ, hn⟩ := Set.not_subset.1 h
      exact hm (show ((Γ, {θ}) : Set Formula × Set Formula) ≤ (Γ ∪ Z₁, Θ \ Z₁ ∪ Δ) from
        ⟨Set.subset_union_left, Set.singleton_subset_iff.2 (.inl ⟨hθ, hn⟩)⟩) (h₁ θ hθ)

/-- The restriction of a monotone transitive relation to single formulas is transitive. -/
theorem isTrans (ht : IsTransitive r) (hm : Monotone (Function.uncurry r)) :
    IsTrans Formula fun φ ψ ↦ r {φ} {ψ} :=
  ⟨fun _ _ _ h₁ h₂ ↦ ht.trans hm (Set.forall_mem_singleton.2 h₁) h₂⟩

end IsTransitive

end Consequence
