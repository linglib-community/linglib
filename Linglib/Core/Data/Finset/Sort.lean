/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Sort

/-!
# The rank of a member of a finite set

The *rank* of a member `c` of a finite set `s` in a linear order is the number of members of `s`
less than `c`. This file defines the rank `s.rank c` and shows that it is an order isomorphism
from `s` onto `Fin #s`, the inverse of `Finset.orderIsoOfFin`.

## Main definitions

* `Finset.rank`: the number of members of a finite set less than a given member.
* `Finset.rankOrderIso`: the rank as an order isomorphism onto `Fin #s`.

## Implementation notes

`Finset.orderIsoOfFin` enumerates a finite set by sorting it with `List.mergeSort`, and its
inverse does not reduce by evaluation. The rank is defined by counting, so that `decide` evaluates
it on a concrete finite set.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [LinearOrder α] (s : Finset α)

/-- The rank of a member of a finite set is the number of members less than it. -/
def rank (c : s) : Fin #s :=
  ⟨#{d ∈ s | d < (c : α)}, card_lt_card (filter_ssubset.2 ⟨c, c.2, lt_irrefl _⟩)⟩

theorem rank_strictMono : StrictMono s.rank := fun c d hcd ↦ by
  have hcd' : (c : α) < d := Subtype.coe_lt_coe.2 hcd
  simp only [rank, Fin.mk_lt_mk]
  exact card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun _ _ he ↦ lt_trans he hcd')).2
    ⟨c, mem_filter.2 ⟨c.2, hcd'⟩, by simp⟩)

/-- The rank as an order isomorphism from a finite set onto `Fin #s`. -/
noncomputable def rankOrderIso : s ≃o Fin #s where
  toEquiv := Equiv.ofBijective s.rank
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨s.rank_strictMono.injective, by simp⟩)
  map_rel_iff' := s.rank_strictMono.le_iff_le

@[simp] theorem coe_rankOrderIso : ⇑s.rankOrderIso = s.rank := rfl

theorem symm_rankOrderIso : s.rankOrderIso.symm = s.orderIsoOfFin rfl :=
  Subsingleton.elim _ _

end Finset
