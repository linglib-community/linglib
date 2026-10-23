module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Notation.Lemmas
public import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Holley's inequality for upper sets

[UPSTREAM] Holley's inequality, a two-weight form of the Fortuin–Kasteleyn–Ginibre
inequality, compares weights `f` and `g` on a finite distributive lattice with
`f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)`: then `g` puts relatively more weight on every upper set
than `f` does. This file states it for an upper set, without normalizing the weights, as a
corollary of the four functions theorem.

## References

* [fortuin-kasteleyn-ginibre-1971]
* [holley-1974]
-/

@[expose] public section

open Finset

variable {α β : Type*} [DistribLattice α] [Fintype α] [DecidableEq α] [CommSemiring β]
  [LinearOrder β] [IsStrictOrderedRing β] [ExistsAddOfLE β] {f g : α → β} {s : Finset α}

theorem holley_isUpperSet (hf : 0 ≤ f) (hg : 0 ≤ g) (hs : IsUpperSet (s : Set α))
    (h : ∀ a b, f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)) :
    (∑ a ∈ s, f a) * ∑ a, g a ≤ (∑ a, f a) * ∑ a ∈ s, g a := by
  have h' (a b : α) :
      (if a ∈ s then f a else 0) * g b ≤ f (a ⊓ b) * if a ⊔ b ∈ s then g (a ⊔ b) else 0 := by
    split_ifs with ha hab
    · exact h a b
    · exact absurd (hs le_sup_left ha) hab
    · simpa using mul_nonneg (hf _) (hg _)
    · simp
  simpa [sum_ite_mem] using four_functions_theorem_univ _ g f _
    (fun a ↦ ite_nonneg (hf a) le_rfl) hg hf (fun a ↦ ite_nonneg (hg a) le_rfl) h'
