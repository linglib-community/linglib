/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Multiset.Antidiagonal
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Multiset.Antidiagonal
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring

/-!
# Automorphism cardinality for rooted nonplanar trees

For a rooted nonplanar tree whose children form the multiset `M = {c₁ × k₁, …, cₙ × kₙ}`
(distinct subtrees `cᵢ` with multiplicity `kᵢ`), the automorphism group has cardinality
`∏ᵢ kᵢ! · |Aut(cᵢ)| ^ kᵢ`; the same formula applied to the top-level multiset counts the
automorphisms of a forest.

## Main definitions

* `UnorderedTree.autCard`: the automorphism count `|Aut(t)|` of a rooted nonplanar tree.
* `UnorderedTree.forestAutCard`: the automorphism count of a forest (multiset of rooted
  nonplanar trees).

## Main results

* `UnorderedTree.autCard_node`: the recursion `autCard (node a M) = forestAutCard M`.
* `UnorderedTree.forestAutCard_add`: the multinomial split identity
  `forestAutCard (F + G) = (antidiagonal (F + G)).count (F, G) * (forestAutCard F *
  forestAutCard G)`, the combinatorial core of the pairing's product-coproduct adjunction.
-/

@[expose] public section

namespace UnorderedTree

variable {α : Type*} [DecidableEq α]

/-- Symmetry-factor at one node: `∏_{distinct c ∈ M} (M.count c)!`. -/
def multinomialFactor (M : Multiset (UnorderedTree α)) : ℕ :=
  M.toFinset.prod fun t => (M.count t).factorial

/-- The cardinality `|Aut(t)|` of the automorphism group of a rooted nonplanar tree: the product of
the children's counts times the symmetry factor of the children (`autCard_node`). -/
def autCard : UnorderedTree α → ℕ :=
  para fun _ ps ↦ (ps.map Prod.snd).prod * multinomialFactor (ps.map Prod.fst)

/-- The automorphism count `|Aut(F)|` of a forest of nonplanar trees,
`∏_{distinct T ∈ F} (F.count T)! · autCard T ^ F.count T`. -/
def forestAutCard (F : Multiset (UnorderedTree α)) : ℕ :=
  F.toFinset.prod fun t => (F.count t).factorial * autCard t ^ F.count t

@[simp] theorem forestAutCard_zero :
    forestAutCard (0 : Multiset (UnorderedTree α)) = 1 := by
  simp [forestAutCard]

@[simp] theorem forestAutCard_singleton (T : UnorderedTree α) :
    forestAutCard ({T} : Multiset (UnorderedTree α)) = autCard T := by
  simp [forestAutCard]

theorem forestAutCard_eq_prod_mul_multinomialFactor (F : Multiset (UnorderedTree α)) :
    forestAutCard F = (F.map autCard).prod * multinomialFactor F := by
  unfold forestAutCard multinomialFactor
  rw [Finset.prod_multiset_map_count, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t _ => mul_comm _ _

@[simp] theorem autCard_node (a : α) (F : Multiset (UnorderedTree α)) :
    autCard (UnorderedTree.node a F) = forestAutCard F := by
  simp [autCard, forestAutCard_eq_prod_mul_multinomialFactor]

@[simp] theorem autCard_leaf (a : α) : autCard (UnorderedTree.leaf a : UnorderedTree α) = 1 := by
  rw [← node_zero, autCard_node, forestAutCard_zero]

theorem autCard_pos (t : UnorderedTree α) : 0 < autCard t := by
  induction t with
  | node a F ih =>
    rw [autCard_node]
    exact Finset.prod_pos fun t ht ↦
      Nat.mul_pos (Nat.factorial_pos _) (pow_pos (ih t (Multiset.mem_toFinset.1 ht)) _)

theorem forestAutCard_pos (F : Multiset (UnorderedTree α)) : 0 < forestAutCard F :=
  Finset.prod_pos fun t _ ↦ Nat.mul_pos (Nat.factorial_pos _) (pow_pos (autCard_pos t) _)

/-! ### Multinomial split identity

`Multiset.count_antidiagonal_eq_count_powerset` and `Multiset.count_powerset_of_le`
compute the split multiplicity; `Nat.add_choose_mul_factorial_mul_factorial` recombines
it with the factorials per distinct tree. This identity is the combinatorial core of the
pairing's product-coproduct adjunction (`GrossmanLarson.pairing_of'_mul_of'`). -/

theorem forestAutCard_add (F G : Multiset (UnorderedTree α)) :
    forestAutCard (F + G) = (Multiset.antidiagonal (F + G)).count (F, G) *
      (forestAutCard F * forestAutCard G) := by
  have hext : ∀ M : Multiset (UnorderedTree α), M ≤ F + G →
      forestAutCard M
        = (F + G).toFinset.prod (fun t => (M.count t).factorial * autCard t ^ M.count t) := by
    intro M hM
    refine Finset.prod_subset
      (Multiset.toFinset_subset.mpr (Multiset.subset_of_le hM)) fun x _ hx => ?_
    rw [Multiset.count_eq_zero.mpr fun hm => hx (Multiset.mem_toFinset.mpr hm)]
    simp
  rw [Multiset.count_antidiagonal_eq_count_powerset,
      Multiset.count_powerset_of_le (Multiset.le_add_left G F),
      hext F (Multiset.le_add_right F G), hext G (Multiset.le_add_left G F),
      hext (F + G) le_rfl, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Multiset.count_add, pow_add,
      ← Nat.add_choose_mul_factorial_mul_factorial (F.count t) (G.count t)]
  ring

end UnorderedTree

