module

public import Linglib.Semantics.Modality.OrderingSemantics
public import Mathlib.Order.Filter.Map

/-!
# The filter of necessities

The necessities of ordering semantics over a domain are the sets of a filter: the propositions
that hold at every world of the domain from some point on, as the worlds come closer. Lewis's
variably strict conditional is membership in this filter for the accessible antecedent-worlds, and
its *might* is the dual, frequent truth. The filter is proper exactly when the domain is nonempty.
Under the Limit Assumption, that every world of the domain lies above a minimal one, it is the
principal filter of the minimal worlds, and when one world of the domain lies strictly below every
other it is the point filter of that world.

## Main definitions

* `OrderingSemantics.necessityFilter p s`: the filter of necessities over `s` under `p`.

## Main statements

* `OrderingSemantics.necessityFilter_neBot_iff`: the filter is proper exactly when `s` is
  nonempty.
* `OrderingSemantics.necessityFilter_eq_principal`: under the Limit Assumption it is the
  principal filter of the minimal worlds.
* `OrderingSemantics.necessityFilter_eq_pure`: when one world of `s` lies strictly below every
  other, it is the point filter of that world.

## References

* [lewis-1973b]
* [lewis-1981]
-/

@[expose] public section

open Filter

namespace OrderingSemantics

variable {W : Type*} {p : Preorder W} {s t : Set W} {v : W}

/-- The filter of necessities over `s` under `p`. -/
def necessityFilter (p : Preorder W) (s : Set W) : Filter W where
  sets := {t | IsNecessity p s t}
  univ_sets := isNecessity_univ p s
  sets_of_superset h hst := h.mono hst
  inter_sets h h' := h.inter h'

@[simp] theorem mem_necessityFilter : t ∈ necessityFilter p s ↔ IsNecessity p s t := Iff.rfl

theorem self_mem_necessityFilter : s ∈ necessityFilter p s :=
  fun u hu ↦ ⟨u, hu, p.le_refl u, fun _ hw _ ↦ hw⟩

theorem necessityFilter_neBot_iff : (necessityFilter p s).NeBot ↔ s.Nonempty := by
  rw [← forall_mem_nonempty_iff_neBot]
  refine ⟨fun h ↦ h s self_mem_necessityFilter, fun ⟨u, hu⟩ t ht ↦ ?_⟩
  obtain ⟨v, hv, -, hvt⟩ := ht u hu
  exact ⟨v, hvt v hv (p.le_refl v)⟩

theorem necessityFilter_eq_principal (hlim : ∀ u ∈ s, ∃ v ∈ p.minimals s, p.le v u) :
    necessityFilter p s = 𝓟 (p.minimals s) :=
  Filter.ext fun _ ↦ (isNecessity_iff_minimals_subset hlim).trans mem_principal.symm

theorem necessityFilter_eq_pure (hv : v ∈ s) (hle : ∀ u ∈ s, p.le v u)
    (hlt : ∀ u ∈ s, p.le u v → u = v) : necessityFilter p s = pure v := by
  have hmin : p.minimals s = {v} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨hv, fun u hu _ ↦ hle u hu⟩,
      fun u hu ↦ hlt u hu.1 (hu.2 hv (hle u hu.1))⟩
  rw [necessityFilter_eq_principal fun u hu ↦ ⟨v, hmin ▸ rfl, hle u hu⟩, hmin,
    principal_singleton]

end OrderingSemantics
