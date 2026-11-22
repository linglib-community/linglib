/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Finite
public import Linglib.Syntax.WordOrder
public import Mathlib.Data.Finset.Sort

/-!
# Local subtrees

The *local subtree* of a position `v` is `v` together with its dependents. This file defines the
local subtree `G.localSubtree v` and the rank `G.localRank v c` of a member `c`, the number of
members that precede `c` in the sentence. The rank is an order isomorphism from the local subtree
onto `Fin k`, where `k` is the size of the local subtree (`Digraph.localOrderIso`). Read as an
arrangement (`Digraph.localArrangement`), it is the order in which a head and its dependents
appear.

## Implementation notes

The rank is defined by counting, so that the kernel evaluates it. It inverts mathlib's enumeration
`Finset.orderIsoOfFin` of a finite set in increasing order (`Digraph.symm_localOrderIso`), which
sorts with `List.mergeSort` and does not reduce.

## References

* [futrell-levy-gibson-2020]
-/

@[expose] public section

variable {n : ℕ}

section LocalSubtree

open Finset WordOrder

variable (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)

/-- The local subtree of `v`: the head `v` together with its dependents. -/
def Digraph.localSubtree : Finset (Fin n) := insert v (G.outNeighborFinset v)

/-- The rank of a member of a local subtree counts the members before it. -/
def Digraph.localRank (c : G.localSubtree v) : Fin #(G.localSubtree v) :=
  ⟨#{d ∈ G.localSubtree v | d < (c : Fin n)}, card_lt_card (filter_ssubset.2 ⟨c, c.2, lt_irrefl _⟩)⟩

theorem Digraph.localRank_strictMono : StrictMono (G.localRank v) := fun c d hcd ↦ by
  have hcd' : (c : Fin n) < d := Subtype.coe_lt_coe.2 hcd
  simp only [Digraph.localRank, Fin.mk_lt_mk]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun _ _ he ↦ lt_trans he hcd')).2
    ⟨c, mem_filter.2 ⟨c.2, hcd'⟩, by simp⟩)

/-- The rank as an order isomorphism from a local subtree to an initial segment of the positions. -/
noncomputable def Digraph.localOrderIso : G.localSubtree v ≃o Fin #(G.localSubtree v) where
  toEquiv := Equiv.ofBijective (G.localRank v)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(G.localRank_strictMono v).injective, by simp⟩)
  map_rel_iff' := (G.localRank_strictMono v).le_iff_le

@[simp] theorem Digraph.coe_localOrderIso : ⇑(G.localOrderIso v) = G.localRank v := rfl

theorem Digraph.symm_localOrderIso :
    (G.localOrderIso v).symm = (G.localSubtree v).orderIsoOfFin rfl :=
  Subsingleton.elim _ _

/-- The arrangement of a local subtree in the order of its positions. -/
noncomputable def Digraph.localArrangement : Arrangement (G.localSubtree v) #(G.localSubtree v) :=
  (G.localOrderIso v).toEquiv

@[simp] theorem Digraph.self_mem_localSubtree : v ∈ G.localSubtree v := mem_insert_self _ _

variable {G v}

theorem Digraph.mem_localSubtree_iff {w : Fin n} : w ∈ G.localSubtree v ↔ w = v ∨ G.Adj v w := by
  simp [Digraph.localSubtree]

theorem Digraph.mem_localSubtree_of_adj {w : Fin n} (h : G.Adj v w) : w ∈ G.localSubtree v :=
  Digraph.mem_localSubtree_iff.2 (.inr h)

@[simp] theorem Digraph.localArrangement_precedes {c d : G.localSubtree v} :
    (G.localArrangement v).Precedes c d ↔ (c : Fin n) < d :=
  (G.localOrderIso v).lt_iff_lt.trans Subtype.coe_lt_coe.symm

end LocalSubtree
