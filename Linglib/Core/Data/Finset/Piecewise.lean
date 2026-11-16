module

public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Set.Function

/-!
# Piecewise functions on finite sets

[UPSTREAM] Where `s.piecewise f g` agrees with `f` and with `g`: on every subset of `s`, and on
every set disjoint from `s`.
-/

public section

namespace Finset

variable {ι β : Type*} {s t : Finset ι} [∀ i, Decidable (i ∈ s)] {f g : ι → β}

theorem eqOn_piecewise_of_subset (h : t ⊆ s) : Set.EqOn (s.piecewise f g) f t :=
  fun _ hi ↦ piecewise_eq_of_mem _ _ _ (h hi)

theorem eqOn_piecewise_of_disjoint (h : Disjoint s t) : Set.EqOn (s.piecewise f g) g t :=
  fun _ hi ↦ piecewise_eq_of_notMem _ _ _ (disjoint_right.1 h hi)

end Finset
