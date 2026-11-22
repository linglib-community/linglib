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

The local subtree of a head is the head together with its dependents. Its members stand in the
order of their positions. This file defines the local subtree, `Digraph.localSubtree`, and the
rank of each member in it, `Digraph.localRank`, the number of members before it. The rank is an
order isomorphism onto an initial segment of the positions (`Digraph.localOrderIso`), and as an
arrangement (`Digraph.localArrangement`) it is the order in which the head and the phrases of its
dependents follow one another.

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

/-- The rank is an order isomorphism from a head and its dependents to an initial segment of the
positions. The inverse is classical, but an order isomorphism is applied through
`Digraph.localRank`, which the kernel reduces. -/
noncomputable def Digraph.localOrderIso : G.localSubtree v ≃o Fin #(G.localSubtree v) where
  toEquiv := Equiv.ofBijective (G.localRank v)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(G.localRank_strictMono v).injective, by simp⟩)
  map_rel_iff' := (G.localRank_strictMono v).le_iff_le

@[simp] theorem Digraph.coe_localOrderIso : ⇑(G.localOrderIso v) = G.localRank v := rfl

/-- The rank inverts mathlib's enumeration of a finite set in increasing order. -/
theorem Digraph.symm_localOrderIso :
    (G.localOrderIso v).symm = (G.localSubtree v).orderIsoOfFin rfl :=
  Subsingleton.elim _ _

/-- A head and its dependents arranged by position. -/
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
