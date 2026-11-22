/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Basic
public import Linglib.Syntax.WordOrder
public import Mathlib.Data.Finset.Sort

/-!
# A head and its dependents

A head and its dependents stand in the order of their positions. This file defines the set of a
head with its dependents, `Digraph.siblings`, and the rank of each among them,
`Digraph.siblingRank`, the number of siblings before it. The rank is an order isomorphism onto an
initial segment of the positions (`Digraph.siblingOrderIso`), and as an arrangement
(`Digraph.siblingArrangement`) it is the order in which the head's phrases follow one another.

## Implementation notes

The rank is defined by counting, so that the kernel evaluates it. It inverts mathlib's enumeration
`Finset.orderIsoOfFin` of a finite set in increasing order (`Digraph.symm_siblingOrderIso`), which
sorts with `List.mergeSort` and does not reduce.
-/

@[expose] public section

variable {n : ℕ}

section Siblings

open Finset WordOrder

variable (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)

/-- A head together with its dependents. -/
def Digraph.siblings : Finset (Fin n) := insert v (G.children v)

/-- The rank of a sibling counts the siblings before it. -/
def Digraph.siblingRank (c : G.siblings v) : Fin #(G.siblings v) :=
  ⟨#{d ∈ G.siblings v | d < (c : Fin n)}, card_lt_card (filter_ssubset.2 ⟨c, c.2, lt_irrefl _⟩)⟩

theorem Digraph.siblingRank_strictMono : StrictMono (G.siblingRank v) := fun c d hcd ↦ by
  have hcd' : (c : Fin n) < d := Subtype.coe_lt_coe.2 hcd
  simp only [Digraph.siblingRank, Fin.mk_lt_mk]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun _ _ he ↦ lt_trans he hcd')).2
    ⟨c, mem_filter.2 ⟨c.2, hcd'⟩, by simp⟩)

/-- The rank is an order isomorphism from a head and its dependents to an initial segment of the
positions. The inverse is classical, but an order isomorphism is applied through
`Digraph.siblingRank`, which the kernel reduces. -/
noncomputable def Digraph.siblingOrderIso : G.siblings v ≃o Fin #(G.siblings v) where
  toEquiv := Equiv.ofBijective (G.siblingRank v)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(G.siblingRank_strictMono v).injective, by simp⟩)
  map_rel_iff' := (G.siblingRank_strictMono v).le_iff_le

@[simp] theorem Digraph.coe_siblingOrderIso : ⇑(G.siblingOrderIso v) = G.siblingRank v := rfl

/-- The rank inverts mathlib's enumeration of a finite set in increasing order. -/
theorem Digraph.symm_siblingOrderIso :
    (G.siblingOrderIso v).symm = (G.siblings v).orderIsoOfFin rfl :=
  Subsingleton.elim _ _

/-- A head and its dependents arranged by position. -/
noncomputable def Digraph.siblingArrangement : Arrangement (G.siblings v) #(G.siblings v) :=
  (G.siblingOrderIso v).toEquiv

@[simp] theorem Digraph.self_mem_siblings : v ∈ G.siblings v := mem_insert_self _ _

variable {G v}

theorem Digraph.mem_siblings_iff {w : Fin n} : w ∈ G.siblings v ↔ w = v ∨ G.Adj v w := by
  simp [Digraph.siblings]

theorem Digraph.mem_siblings_of_adj {w : Fin n} (h : G.Adj v w) : w ∈ G.siblings v :=
  Digraph.mem_siblings_iff.2 (.inr h)

@[simp] theorem Digraph.siblingArrangement_precedes {c d : G.siblings v} :
    (G.siblingArrangement v).Precedes c d ↔ (c : Fin n) < d :=
  (G.siblingOrderIso v).lt_iff_lt.trans Subtype.coe_lt_coe.symm

end Siblings
