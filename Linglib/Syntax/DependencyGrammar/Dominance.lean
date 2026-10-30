/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Dominance, dependency forests and dependency trees

A position of a dependency graph dominates another when a chain of arcs leads from the first to
the second. The graph is a forest when no position dominates its own head and no position has two
heads, and a tree when in addition its root dominates every position. On a forest dominance is a
partial order in which the dominators of a position form a chain, so positions neither of which
dominates the other have disjoint yields.

## Main definitions

* `Dominates`: the reflexive-transitive closure of the arc relation. `Graph.yield` is the set of
  positions a position dominates, and `Graph.projection` lists it in ascending order.
* `Graph.IsForest`: no position dominates its own head, and no position has two heads.
* `Graph.IsTree`: a forest whose root dominates every position.
* `DominanceOrder`: the positions ordered by dominance, on a forest a partial order with the head
  as predecessor and on a tree one with the root as bottom.
* `Tree`: a graph bundled with a proof that it is a tree.

## Main statements

* `Graph.isTree_iff_forall_not_adj_iff`: a tree is a forest whose only headless position is its
  root.
* `Graph.isTree_iff_leftUnique_adj`: a graph is a tree when no position has two heads, the root
  has none, and the root dominates every position, so that acyclicity need not be assumed.
* `Graph.IsForest.disjoint_yield`: on a forest, positions neither of which dominates the other
  have disjoint yields.
* `exists_adj_adj_of_not_dominates`: positions under a common dominator, neither dominating the
  other, lie under distinct dependents of one position.

## Implementation notes

* `Dominates` is an `abbrev` for `Relation.ReflTransGen g.Adj`, so mathlib's closure API applies
  to dominance directly and decidability comes from `Core/Relation/ReflTransGen.lean`. Dot
  notation on a dominance hypothesis therefore resolves in `Relation.ReflTransGen`.
* `Decidable g.IsTree` goes through `Graph.isTree_iff_leftUnique_adj`, which searches from the
  root alone instead of looking for a cycle from every position.
* `DominanceOrder g` carries the instances that mathlib's `Order/SuccPred/Tree.lean` and the
  command relations of `Syntax/Command.lean` are stated over. Its archimedean property is
  inferred from finiteness.

## References

* [kuhlmann-nivre-2006]
-/

@[expose] public section

namespace DependencyGrammar

open Relation

variable {L : Type*} {n : ℕ} {g : Graph L n} {u v w x y : Fin n}

/-! ### Dominance -/

/-- `v` dominates `x` when a possibly empty chain of arcs leads from `v` to `x`. -/
abbrev Dominates (g : Graph L n) : Fin n → Fin n → Prop :=
  ReflTransGen g.Adj

/-- The yield of `v` is the set of positions `v` dominates, `v` itself included. -/
def Graph.yield (g : Graph L n) (v : Fin n) : Set (Fin n) :=
  {x | Dominates g v x}

@[simp] theorem Graph.mem_yield : x ∈ g.yield v ↔ Dominates g v x := Iff.rfl

instance (g : Graph L n) (v : Fin n) : DecidablePred (· ∈ g.yield v) :=
  fun _ ↦ inferInstanceAs (Decidable (Dominates g v _))

/-- The projection of `v` is its yield in ascending order of position. -/
def Graph.projection (g : Graph L n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun x ↦ decide (x ∈ g.yield v))

@[simp] theorem Graph.mem_projection : x ∈ g.projection v ↔ Dominates g v x := by
  simp [Graph.projection]

theorem Graph.exists_adj_mem_yield (hx : x ∈ g.yield v) (hne : x ≠ v) :
    ∃ u, g.Adj v u ∧ x ∈ g.yield u :=
  (ReflTransGen.cases_head hx).resolve_left hne.symm

theorem exists_link_across {S : Set (Fin n)} (hx : Dominates g v x) (hy : Dominates g v y)
    (hxS : x ∈ S) (hyS : y ∉ S) :
    ∃ p q, g.Linked p q ∧ Dominates g v p ∧ Dominates g v q ∧ p ∈ S ∧ q ∉ S := by
  by_cases hv : v ∈ S
  · obtain ⟨p, q, hpq, hpS, hqS, hvp, -⟩ := hy.exists_boundary hv hyS
    exact ⟨p, q, .inl hpq, hvp, hvp.tail hpq, hpS, hqS⟩
  · obtain ⟨p, q, hpq, hpS, hqS, hvp, -⟩ := hx.exists_boundary (S := Sᶜ) hv (not_not_intro hxS)
    exact ⟨q, p, .inr hpq, hvp.tail hpq, hvp, not_not.1 hqS, hpS⟩

/-- Positions under a common dominator, neither of which dominates the other, lie under distinct
dependents of one position, their lowest common governor. -/
theorem exists_adj_adj_of_not_dominates (hu : Dominates g x u) (hv : Dominates g x v)
    (huv : ¬ Dominates g u v) (hvu : ¬ Dominates g v u) :
    ∃ p u' v', g.Adj p u' ∧ g.Adj p v' ∧ u' ≠ v' ∧ Dominates g u' u ∧ Dominates g v' v := by
  obtain ⟨p, u', hpu', hp, hu', -, hu'u⟩ :=
    hu.exists_boundary (S := {z | Dominates g z v}) hv huv
  obtain rfl | ⟨v', hpv', hv'v⟩ := ReflTransGen.cases_head hp
  · exact absurd (hu'u.head hpu') hvu
  · exact ⟨p, u', v', hpu', hpv', fun h ↦ hu' (h ▸ hv'v), hu'u, hv'v⟩

/-! ### Forests and trees -/

/-- A dependency graph is a forest when no position dominates its own head and no position has
two heads ([kuhlmann-nivre-2006], Definition 2). -/
structure Graph.IsForest (g : Graph L n) : Prop where
  /-- The graph is acyclic: a dependent does not dominate its head. -/
  not_dominates_of_adj ⦃v w : Fin n⦄ : g.Adj v w → ¬ Dominates g w v
  /-- A position has at most one head. -/
  leftUnique_adj : Relator.LeftUnique g.Adj

/-- A dependency graph is a tree when it is a forest whose root dominates every position. -/
structure Graph.IsTree (g : Graph L n) : Prop extends g.IsForest where
  /-- The root dominates every position. -/
  root_dominates (v : Fin n) : Dominates g g.root v

instance (g : Graph L n) : Decidable g.IsForest :=
  decidable_of_iff ((∀ v w, g.Adj v w → ¬ Dominates g w v) ∧
      ∀ w u, g.Adj u w → ∀ v, g.Adj v w → u = v)
    ⟨fun h ↦ ⟨fun _ _ ↦ h.1 _ _, fun _ _ _ hu hv ↦ h.2 _ _ hu _ hv⟩,
      fun h ↦ ⟨fun _ _ ↦ @h.1 _ _, fun _ _ hu _ hv ↦ h.2 hu hv⟩⟩

namespace Graph.IsForest

variable (hF : g.IsForest)
include hF

theorem not_adj_self : ¬ g.Adj v v := fun h ↦ hF.not_dominates_of_adj h .refl

theorem ne_of_adj (h : g.Adj v w) : v ≠ w := by
  rintro rfl
  exact hF.not_adj_self h

theorem acyclic (v : Fin n) : ¬ TransGen g.Adj v v := fun h ↦
  have ⟨_, hvw, hwv⟩ := TransGen.head'_iff.1 h
  hF.not_dominates_of_adj hvw hwv

theorem dominates_antisymm (hvw : Dominates g v w) (hwv : Dominates g w v) : v = w := by
  obtain rfl | ⟨u, hvu, huw⟩ := ReflTransGen.cases_head hvw
  · rfl
  · exact absurd (huw.trans hwv) (hF.not_dominates_of_adj hvu)

theorem dominates_head (hvw : Dominates g v w) (hne : v ≠ w) (hu : g.Adj u w) :
    Dominates g v u := by
  obtain rfl | ⟨z, hvz, hzw⟩ := ReflTransGen.cases_tail hvw
  · exact absurd rfl hne
  · exact hF.leftUnique_adj hzw hu ▸ hvz

theorem dominates_total (hv : Dominates g v x) (hw : Dominates g w x) :
    Dominates g v w ∨ Dominates g w v :=
  ReflTransGen.total_of_left_unique hF.leftUnique_adj hv hw

/-- Positions of a forest neither of which dominates the other have disjoint yields. -/
theorem disjoint_yield (hvw : ¬ Dominates g v w) (hwv : ¬ Dominates g w v) :
    Disjoint (g.yield v) (g.yield w) :=
  Set.disjoint_left.2 fun _ hv hw ↦ (hF.dominates_total hv hw).elim hvw hwv

theorem disjoint_yield_of_adj (hw : g.Adj v w) (hu : g.Adj v u) (hne : w ≠ u) :
    Disjoint (g.yield w) (g.yield u) :=
  hF.disjoint_yield (fun hd ↦ hF.not_dominates_of_adj hw (hF.dominates_head hd hne hu))
    fun hd ↦ hF.not_dominates_of_adj hu (hF.dominates_head hd hne.symm hw)

end Graph.IsForest

theorem Graph.not_isForest_enhance (hv : g.Adj v w) (hx : x ≠ v) (r : L)
    (extra : List (Fin n × Fin n × L)) (hmem : (x, w, r) ∈ extra) :
    ¬ (g.enhance extra).IsForest := fun hF ↦
  hx (hF.leftUnique_adj (enhance_adj.2 (.inr ⟨r, hmem⟩)) (enhance_adj.2 (.inl hv)))

namespace Graph.IsTree

variable (hT : g.IsTree)
include hT

theorem not_adj_root (v : Fin n) : ¬ g.Adj v g.root := fun h ↦
  hT.not_dominates_of_adj h (hT.root_dominates v)

theorem exists_adj (hw : w ≠ g.root) : ∃ v, g.Adj v w :=
  ((ReflTransGen.cases_tail (hT.root_dominates w)).resolve_left hw).imp fun _ h ↦ h.2

end Graph.IsTree

/-- A tree is a forest whose only headless position is its root, a forest with exactly one root
([kuhlmann-nivre-2006], Definition 2). -/
theorem Graph.isTree_iff_forall_not_adj_iff :
    g.IsTree ↔ g.IsForest ∧ ∀ w, (∀ v, ¬ g.Adj v w) ↔ w = g.root := by
  refine ⟨fun hT ↦ ⟨hT.toIsForest, fun w ↦ ⟨fun hw ↦ ?_, fun hw ↦ hw ▸ hT.not_adj_root⟩⟩,
    fun ⟨hF, h⟩ ↦ ⟨hF, ReflTransGen.of_forall_exists hF.acyclic fun w hw ↦ ?_⟩⟩
  · by_contra hne
    exact (hT.exists_adj hne).elim hw
  · by_contra hno
    exact hw ((h w).1 fun v hv ↦ hno ⟨v, hv⟩)

/-- A graph is a tree when no position has two heads, the root has none, and the root dominates
every position: a cycle would have to be entered from the root's side through a second head. -/
theorem Graph.isTree_iff_leftUnique_adj :
    g.IsTree ↔
      Relator.LeftUnique g.Adj ∧ (∀ v, ¬ g.Adj v g.root) ∧ ∀ v, Dominates g g.root v := by
  refine ⟨fun hT ↦ ⟨hT.leftUnique_adj, hT.not_adj_root, hT.root_dominates⟩,
    fun ⟨hU, hr, hd⟩ ↦ ⟨⟨fun v w hvw hwv ↦ ?_, hU⟩, hd⟩⟩
  have hroot : ¬ TransGen g.Adj g.root g.root := fun h ↦
    have ⟨y, _, hy⟩ := TransGen.tail'_iff.1 h
    hr y hy
  obtain ⟨c, d, hcd, hc, hdS, -, -⟩ :=
    (hd v).exists_boundary (S := {z | ¬ TransGen g.Adj z z}) hroot
      (not_not_intro (TransGen.head' hvw hwv))
  obtain ⟨y, hdy, hyd⟩ := TransGen.tail'_iff.1 (not_not.1 hdS)
  exact hc (TransGen.head' hcd (hU hyd hcd ▸ hdy))

instance (g : Graph L n) : Decidable g.IsTree :=
  decidable_of_iff ((∀ w u, g.Adj u w → ∀ v, g.Adj v w → u = v) ∧
      (∀ v, ¬ g.Adj v g.root) ∧ ∀ v, Dominates g g.root v)
    ⟨fun h ↦ g.isTree_iff_leftUnique_adj.2 ⟨fun _ _ _ hu hv ↦ h.1 _ _ hu _ hv, h.2⟩,
      fun h ↦ ⟨fun _ _ hu _ hv ↦ h.leftUnique_adj hu hv, h.not_adj_root, h.root_dominates⟩⟩

/-! ### The head function -/

/-- The least head of `v`, and `v` itself when it has none. In a forest it is the head of every
position that has one. -/
def Graph.headOf (g : Graph L n) (v : Fin n) : Fin n :=
  (g.parents v).min.untopD v

theorem Graph.headOf_of_forall_not_adj (h : ∀ u, ¬ g.Adj u v) : g.headOf v = v := by
  have hp : g.parents v = ∅ :=
    Finset.eq_empty_of_forall_notMem fun u hu ↦ h u (mem_parents.1 hu)
  simp [headOf, hp]

theorem Graph.IsForest.headOf_eq (hF : g.IsForest) (h : g.Adj u v) : g.headOf v = u := by
  have hp : g.parents v = {u} := Finset.eq_singleton_iff_unique_mem.2
    ⟨mem_parents.2 h, fun _ hw ↦ hF.leftUnique_adj (mem_parents.1 hw) h⟩
  simp [headOf, hp]

/-! ### The dominance order -/

/-- The positions of `g` ordered by dominance instead of by position. -/
def DominanceOrder (_g : Graph L n) := Fin n

instance [hT : Fact g.IsTree] : Fact g.IsForest := ⟨hT.out.toIsForest⟩

namespace DominanceOrder

instance : Fintype (DominanceOrder g) := inferInstanceAs (Fintype (Fin n))
instance : DecidableEq (DominanceOrder g) := inferInstanceAs (DecidableEq (Fin n))

instance {i : ℕ} [OfNat (Fin n) i] : OfNat (DominanceOrder g) i :=
  inferInstanceAs (OfNat (Fin n) i)

section Forest

variable [hF : Fact g.IsForest]

instance : PartialOrder (DominanceOrder g) where
  le v w := Dominates g v w
  le_refl _ := .refl
  le_trans _ _ _ := .trans
  le_antisymm _ _ := hF.out.dominates_antisymm

instance : DecidableLE (DominanceOrder g) :=
  fun v w ↦ inferInstanceAs (Decidable (Dominates g v w))

/-- The predecessor of a position is its head, and a headless position is its own. -/
instance : PredOrder (DominanceOrder g) where
  pred := g.headOf
  pred_le v := by
    by_cases h : ∃ u, g.Adj u v
    · obtain ⟨u, hu⟩ := h
      exact (hF.out.headOf_eq hu).symm ▸ ReflTransGen.single hu
    · exact (Graph.headOf_of_forall_not_adj (not_exists.1 h)).symm ▸ ReflTransGen.refl
  min_of_le_pred {v} h w hw := by
    obtain rfl | ⟨u, -, hu⟩ := ReflTransGen.cases_tail hw
    · exact le_rfl
    · exact absurd (hF.out.headOf_eq hu ▸ h) (hF.out.not_dominates_of_adj hu)
  le_pred_of_lt {v w} h := by
    obtain rfl | ⟨u, hvu, hu⟩ := ReflTransGen.cases_tail h.le
    · exact absurd rfl h.ne
    · exact (hF.out.headOf_eq hu).symm ▸ hvu

end Forest

instance [hT : Fact g.IsTree] : OrderBot (DominanceOrder g) where
  bot := g.root
  bot_le := hT.out.root_dominates

end DominanceOrder

/-! ### Bundled trees -/

/-- A dependency tree is a graph bundled with a proof that it is a tree. -/
structure Tree (L : Type*) (n : ℕ) extends Graph L n where
  /-- The underlying graph is a tree. -/
  isTree : toGraph.IsTree

namespace Tree

attribute [coe] toGraph

instance : CoeOut (Tree L n) (Graph L n) := ⟨toGraph⟩

/-- Bundle a graph with its tree-hood, decided by default. -/
def mk' (g : Graph L n) (h : g.IsTree := by decide) : Tree L n := ⟨g, h⟩

/-- A bundled tree's tree-hood, which makes the instances of its dominance order available. -/
instance instFact (t : Tree L n) : Fact t.toGraph.IsTree := ⟨t.isTree⟩

end Tree

end DependencyGrammar
