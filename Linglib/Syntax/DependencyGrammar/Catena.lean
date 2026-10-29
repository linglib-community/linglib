/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Dominance
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Catenae

A catena is a word or a combination of words that is connected in the undirected view of a
dependency graph. Every constituent, the dominance cone of a word, is a catena, and a head with
one of several dependents is a catena that is not a constituent.

## Main definitions

* `DependencyGrammar.IsCatena`: the words of `s` induce a connected subgraph.
* `DependencyGrammar.IsConstituent`: `s` is the dominance cone of a word.

## Main statements

* `DependencyGrammar.IsConstituent.isCatena`: every constituent is a catena.
* `DependencyGrammar.not_isConstituent_pair`: in a forest, a head with one of two dependents is
  not a constituent.
* `DependencyGrammar.Graph.IsTree.isTree_toSimpleGraph`: the undirected view of a dependency tree
  is a tree.

## References

* [osborne-2019]
-/

@[expose] public section

namespace DependencyGrammar

variable {L : Type*} {n : ℕ}

/-- `s` is a **catena** if the subgraph induced on `s` is connected. -/
def IsCatena (g : Graph L n) (s : Finset (Fin n)) : Prop :=
  (g.toSimpleGraph.induce ↑s).Connected

/-- `s` is a **constituent** if it is the dominance cone of some position. -/
def IsConstituent (g : Graph L n) (s : Finset (Fin n)) : Prop :=
  ∃ v, ∀ w, w ∈ s ↔ Dominates g v w

instance (g : Graph L n) (s : Finset (Fin n)) : Decidable (IsCatena g s) :=
  inferInstanceAs (Decidable (SimpleGraph.Connected _))

instance (g : Graph L n) (s : Finset (Fin n)) : Decidable (IsConstituent g s) :=
  inferInstanceAs (Decidable (∃ _, _))

theorem singleton_isCatena (g : Graph L n) (v : Fin n) : IsCatena g {v} := by
  rw [IsCatena, Finset.coe_singleton]
  exact .of_subsingleton

theorem connected_induce_cone (g : Graph L n) (v : Fin n) :
    (g.toSimpleGraph.induce {x | Dominates g v x}).Connected := by
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
theorem IsConstituent.isCatena {g : Graph L n} {s : Finset (Fin n)}
    (h : IsConstituent g s) : IsCatena g s := by
  obtain ⟨v, hv⟩ := h
  rw [IsCatena, show (↑s : Set (Fin n)) = {x | Dominates g v x} from Set.ext hv]
  exact connected_induce_cone g v

theorem isCatena_pair (g : Graph L n) {v w : Fin n} (h : g.Adj v w) (hne : v ≠ w) :
    IsCatena g {v, w} := by
  rw [IsCatena, Finset.coe_pair]
  exact SimpleGraph.induce_pair_connected_of_adj ⟨hne, .inl h⟩

/-- In a forest, a head with one of its dependents is not a constituent when the head has
another dependent, since the head's cone contains the other dependent and the dependent's cone
does not contain the head. -/
theorem not_isConstituent_pair {g : Graph L n} (hF : g.IsForest) {v w u : Fin n} (hw : g.Adj v w)
    (hu : g.Adj v u) (huw : u ≠ w) : ¬ IsConstituent g {v, w} := by
  rintro ⟨c, hc⟩
  rcases Finset.mem_insert.mp ((hc c).2 Relation.ReflTransGen.refl) with rfl | hcw
  · rcases Finset.mem_insert.mp ((hc u).2 (Relation.ReflTransGen.single hu)) with rfl | hu'
    · exact hF.not_adj_self hu
    · exact huw (Finset.mem_singleton.mp hu')
  · rw [Finset.mem_singleton] at hcw; subst hcw
    exact hF.not_dominates_of_adj hw ((hc v).1 (by simp))

theorem isConstituent_univ {g : Graph L n} (hT : g.IsTree) :
    IsConstituent g Finset.univ :=
  ⟨g.root, fun w ↦ ⟨fun _ ↦ hT.root_dominates w, fun _ ↦ Finset.mem_univ w⟩⟩

theorem isCatena_univ {g : Graph L n} (hT : g.IsTree) : IsCatena g Finset.univ :=
  (isConstituent_univ hT).isCatena

/-- The undirected view of a dependency tree is a tree: it is connected, the whole sentence being
a catena, and its edges are the links from each position other than the root to its head. -/
theorem Graph.IsTree.isTree_toSimpleGraph {g : Graph L n} (hT : g.IsTree) :
    g.toSimpleGraph.IsTree := by
  have hhead {w : Fin n} (hw : w ≠ g.root) : g.Adj (g.headOf w) w :=
    have ⟨_, h⟩ := hT.exists_adj hw
    hT.headOf_eq h ▸ h
  refine SimpleGraph.isTree_iff_connected_and_card.2 ⟨?_, ?_⟩
  · have h := isCatena_univ hT
    rw [IsCatena, Finset.coe_univ] at h
    exact g.toSimpleGraph.induceUnivIso.connected_iff.1 h
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  refine .trans (congrArg (· + 1) ?_) (Finset.card_erase_add_one (Finset.mem_univ g.root))
  refine (Finset.card_bij (fun w _ ↦ s(g.headOf w, w)) (fun w hw ↦ ?_) (fun w hw w' hw' h ↦ ?_)
    fun e he ↦ ?_).symm
  · have hw := hhead (Finset.ne_of_mem_erase hw)
    simpa using ⟨fun h ↦ hT.not_adj_self (h ▸ hw), Or.inl hw⟩
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
