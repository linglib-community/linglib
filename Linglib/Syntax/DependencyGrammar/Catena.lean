/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Tree
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Catenae

A catena is a word or a combination of words that is connected in the undirected view of a
dependency graph. Every constituent, the dominance cone of a word, is a catena, and a head with
one of several dependents is a catena that is not a constituent.

## Main definitions

* `Graph.IsCatena`: the words of `s` induce a connected subgraph.
* `Graph.IsConstituent`: `s` is the yield of a word.

## Main statements

* `Graph.IsConstituent.isCatena`: every constituent is a catena.
* `Graph.IsForest.isCatena_iff_existsUnique`: in a forest, a catena is a set of positions
  exactly one of which, its root, has no head among them.
* `Graph.IsForest.card_isConstituent`: a forest has as many constituents as positions.
* `Graph.not_isConstituent_pair`: in a forest, a head with one of two dependents is
  not a constituent.
* `DependencyGrammar.Graph.IsTree.isTree_toSimpleGraph`: the undirected view of a dependency tree
  is a tree.

## References

* [osborne-2019]
-/

@[expose] public section

open Finset

namespace DependencyGrammar

variable {L : Type*} {n : ℕ}

/-- `s` is a **catena** if the subgraph induced on `s` is connected. -/
def Graph.IsCatena (g : Graph L n) (s : Finset (Fin n)) : Prop :=
  (g.toSimpleGraph.induce ↑s).Connected

/-- `s` is a **constituent** if it is the yield of some position, a principal upper set of the
dominance order. -/
def Graph.IsConstituent (g : Graph L n) (s : Finset (Fin n)) : Prop :=
  ∃ v, (↑s : Set (Fin n)) = g.yield v

theorem Graph.isConstituent_iff {g : Graph L n} {s : Finset (Fin n)} :
    g.IsConstituent s ↔ ∃ v, ∀ w, w ∈ s ↔ g.Dominates v w := by
  simp [Graph.IsConstituent, Set.ext_iff]

instance (g : Graph L n) (s : Finset (Fin n)) : Decidable (g.IsCatena s) :=
  inferInstanceAs (Decidable (SimpleGraph.Connected _))

instance (g : Graph L n) (s : Finset (Fin n)) : Decidable (g.IsConstituent s) :=
  decidable_of_iff _ Graph.isConstituent_iff.symm

theorem Graph.singleton_isCatena (g : Graph L n) (v : Fin n) : g.IsCatena {v} := by
  rw [Graph.IsCatena, Finset.coe_singleton]
  exact .of_subsingleton

theorem Graph.connected_induce_cone (g : Graph L n) (v : Fin n) :
    (g.toSimpleGraph.induce {x | g.Dominates v x}).Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨⟨v, .refl⟩, ?_⟩
  rintro ⟨w, hw⟩
  induction hw with
  | refl => exact .rfl
  | @tail b c hb hbc ih =>
    rcases eq_or_ne b c with rfl | hne
    · exact ih
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨hne, Or.inl hbc⟩)

/-- Every constituent is a catena, since a constituent is the dominance cone of some position
and cones induce connected subgraphs. -/
theorem Graph.IsConstituent.isCatena {g : Graph L n} {s : Finset (Fin n)}
    (h : g.IsConstituent s) : g.IsCatena s := by
  obtain ⟨v, hv⟩ := h
  rw [Graph.IsCatena, hv]
  exact Graph.connected_induce_cone g v

theorem Graph.isCatena_pair (g : Graph L n) {v w : Fin n} (h : g.Adj v w) (hne : v ≠ w) :
    g.IsCatena {v, w} := by
  rw [Graph.IsCatena, Finset.coe_pair]
  exact SimpleGraph.induce_pair_connected_of_adj ⟨hne, .inl h⟩

/-- In a forest, a head with one of its dependents is not a constituent when the head has
another dependent, since the head's cone contains the other dependent and the dependent's cone
does not contain the head. -/
theorem Graph.not_isConstituent_pair {g : Graph L n} (hF : g.IsForest) {v w u : Fin n}
    (hw : g.Adj v w) (hu : g.Adj v u) (huw : u ≠ w) : ¬ g.IsConstituent {v, w} := by
  rw [Graph.isConstituent_iff]
  rintro ⟨c, hc⟩
  rcases Finset.mem_insert.mp ((hc c).2 Relation.ReflTransGen.refl) with rfl | hcw
  · rcases Finset.mem_insert.mp ((hc u).2 (Relation.ReflTransGen.single hu)) with rfl | hu'
    · exact hF.not_adj_self hu
    · exact huw (Finset.mem_singleton.mp hu')
  · rw [Finset.mem_singleton] at hcw; subst hcw
    exact hF.not_dominates_of_adj hw ((hc v).1 (by simp))

/-- In a forest, a position of a catena with no head in the catena dominates the whole catena:
it is the catena's root. -/
theorem Graph.IsCatena.dominates_of_forall_not_adj {g : Graph L n} {s : Finset (Fin n)}
    (h : g.IsCatena s) (hF : g.IsForest) {a : Fin n} (ha : a ∈ s)
    (hroot : ∀ u ∈ s, ¬ g.Adj u a) {b : Fin n} (hb : b ∈ s) : g.Dominates a b := by
  suffices ∀ y : (↑s : Set (Fin n)), Relation.ReflTransGen
      (g.toSimpleGraph.induce ↑s).Adj ⟨a, ha⟩ y → g.Dominates a y from
    this ⟨b, hb⟩ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (h.preconnected _ _))
  intro y hy
  induction hy with
  | refl => exact .refl
  | @tail x y _ hxy ih =>
    obtain ⟨-, hxy | hyx⟩ := hxy
    · exact ih.tail hxy
    · rcases eq_or_ne a x with rfl | hne
      · exact absurd hyx (hroot y y.2)
      · exact hF.dominates_head ih hne hyx

/-- In a forest a set of positions is a catena iff exactly one of them, its root, has no head
among them. -/
theorem Graph.IsForest.isCatena_iff_existsUnique {g : Graph L n} (hF : g.IsForest)
    {s : Finset (Fin n)} : g.IsCatena s ↔ ∃! v, v ∈ s ∧ ∀ u ∈ s, ¬ g.Adj u v := by
  have wf := hF.wellFounded_transGen
  refine ⟨fun h ↦ ?_, fun ⟨r, ⟨hr, hroot⟩, huniq⟩ ↦ ?_⟩
  · obtain ⟨⟨x, hx⟩⟩ := h.nonempty
    obtain ⟨r, hr, hmin⟩ := wf.has_min (↑s : Set (Fin n)) ⟨x, hx⟩
    have hroot : ∀ u ∈ s, ¬ g.Adj u r := fun u hu hur ↦ hmin u hu (.single hur)
    exact ⟨r, ⟨hr, hroot⟩, fun r' ⟨hr', hroot'⟩ ↦ hF.dominates_antisymm
      (h.dominates_of_forall_not_adj hF hr' hroot' hr)
      (h.dominates_of_forall_not_adj hF hr hroot hr')⟩
  · refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨⟨r, hr⟩, ?_⟩
    rintro ⟨x, hx⟩
    induction x using wf.induction with
    | _ x ih =>
      by_cases hx' : ∀ u ∈ s, ¬ g.Adj u x
      · obtain rfl := huniq x ⟨hx, hx'⟩
        exact .rfl
      · push Not at hx'
        obtain ⟨u, hu, hux⟩ := hx'
        exact (ih u (.single hux) hu).trans
          (SimpleGraph.Adj.reachable ⟨hF.ne_of_adj hux, .inl hux⟩)

/-- In a forest a set of positions is a catena iff it has exactly one position with no head in
it. -/
theorem Graph.IsForest.isCatena_iff {g : Graph L n} (hF : g.IsForest) {s : Finset (Fin n)} :
    g.IsCatena s ↔ #{v ∈ s | ∀ u ∈ s, ¬ g.Adj u v} = 1 := by
  simp [hF.isCatena_iff_existsUnique, Finset.card_eq_one, Finset.eq_singleton_iff_unique_mem,
    ExistsUnique]

/-- A forest has as many constituents as positions. -/
theorem Graph.IsForest.card_isConstituent {g : Graph L n} (hF : g.IsForest) :
    #{s : Finset (Fin n) | g.IsConstituent s} = n := by
  have h : ({s | g.IsConstituent s} : Finset (Finset (Fin n))) =
      Finset.univ.image fun v ↦ ({w | g.Dominates v w} : Finset (Fin n)) := by
    ext s
    simp [Graph.isConstituent_iff, Finset.ext_iff, eq_comm]
  rw [h, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  exact fun v w hvw ↦ hF.yield_injective (Set.ext fun x ↦ by simpa using Finset.ext_iff.1 hvw x)

theorem Graph.isConstituent_univ {g : Graph L n} (hT : g.IsTree) :
    g.IsConstituent Finset.univ :=
  Graph.isConstituent_iff.2
    ⟨g.root, fun w ↦ ⟨fun _ ↦ hT.root_dominates w, fun _ ↦ Finset.mem_univ w⟩⟩

theorem Graph.isCatena_univ {g : Graph L n} (hT : g.IsTree) : g.IsCatena Finset.univ :=
  (Graph.isConstituent_univ hT).isCatena

/-- The undirected view of a dependency tree is a tree: it is connected, the whole sentence being
a catena, and its edges are the links from each position other than the root to its head. -/
theorem Graph.IsTree.isTree_toSimpleGraph {g : Graph L n} (hT : g.IsTree) :
    g.toSimpleGraph.IsTree := by
  have hhead {w : Fin n} (hw : w ≠ g.root) : g.Adj (g.headOf w) w :=
    have ⟨_, h⟩ := hT.exists_adj hw
    hT.headOf_eq h ▸ h
  refine SimpleGraph.isTree_iff_connected_and_card.2 ⟨?_, ?_⟩
  · have h := Graph.isCatena_univ hT
    rw [Graph.IsCatena, Finset.coe_univ] at h
    exact g.toSimpleGraph.induceUnivIso.connected_iff.1 h
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  refine .trans (congrArg (· + 1) ?_) (Finset.card_erase_add_one (Finset.mem_univ g.root))
  refine (Finset.card_bij (fun w _ ↦ s(g.headOf w, w)) (fun w hw ↦ ?_) (fun w hw w' hw' h ↦ ?_)
    fun e he ↦ ?_).symm
  · have hw := hhead (Finset.ne_of_mem_erase hw)
    simpa using ⟨hT.ne_of_adj hw, Or.inl hw⟩
  · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h₁, h₂⟩
    · exact h
    · have h₁' := hhead (Finset.ne_of_mem_erase hw)
      have h₂' := hhead (Finset.ne_of_mem_erase hw')
      rw [h₁] at h₁'
      rw [← h₂] at h₂'
      exact absurd (Relation.ReflTransGen.single h₂') (hT.not_dominates_of_adj h₁')
  · induction e using Sym2.ind with
    | _ a b =>
    obtain ⟨-, hl⟩ := (g.toSimpleGraph_adj a b).1 (SimpleGraph.mem_edgeFinset.1 he)
    rcases hl with h | h
    · exact ⟨b, Finset.mem_erase.2 ⟨fun hb ↦ hT.not_adj_root a (hb ▸ h), Finset.mem_univ _⟩,
        by rw [hT.headOf_eq h]⟩
    · exact ⟨a, Finset.mem_erase.2 ⟨fun ha ↦ hT.not_adj_root b (ha ▸ h), Finset.mem_univ _⟩,
        by rw [hT.headOf_eq h, Sym2.eq_swap]⟩

end DependencyGrammar
