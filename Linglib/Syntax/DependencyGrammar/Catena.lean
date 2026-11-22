/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Arborescence
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Catenae

A catena is a word or a combination of words that is connected in the undirected view of a
dependency graph. Every constituent, the yield of a word, is a catena, and a head with
one of several dependents is a catena that is not a constituent.

## Main definitions

* `Digraph.IsCatena`: the words of `s` induce a connected subgraph.
* `Digraph.IsConstituent`: `s` is the yield of a word.

## Main statements

* `Digraph.IsConstituent.isCatena`: every constituent is a catena.
* `Digraph.IsBranching.isCatena_iff_existsUnique`: in a forest, a catena is a set of positions
  exactly one of which, its root, has no head among them.
* `Digraph.IsBranching.card_isConstituent`: a forest has as many constituents as positions.
* `Digraph.not_isConstituent_pair`: in a forest, a head with one of two dependents is
  not a constituent.
* `Digraph.IsArborescence.isTree_toSimpleGraphInclusive`: the undirected view of an arborescence
  is a tree.

## References

* [osborne-2019]
-/

@[expose] public section

open Finset


variable {n : ℕ}

/-- A set of positions is a *catena* if it induces a connected subgraph of the undirected view. -/
def Digraph.IsCatena (G : Digraph (Fin n)) [DecidableRel G.Adj] (s : Finset (Fin n)) : Prop :=
  (G.toSimpleGraphInclusive.induce ↑s).Connected

/-- A set of positions is a *constituent* if it is the yield of a position. -/
def Digraph.IsConstituent (G : Digraph (Fin n)) [DecidableRel G.Adj] (s : Finset (Fin n)) : Prop :=
  ∃ v, (↑s : Set (Fin n)) = G.reachSet v

theorem Digraph.isConstituent_iff {G : Digraph (Fin n)} [DecidableRel G.Adj] {s : Finset (Fin n)} :
    G.IsConstituent s ↔ ∃ v, ∀ w, w ∈ s ↔ G.Reachable v w := by
  simp [Digraph.IsConstituent, Set.ext_iff]

instance (G : Digraph (Fin n)) [DecidableRel G.Adj] (s : Finset (Fin n)) :
    Decidable (G.IsCatena s) :=
  inferInstanceAs (Decidable (SimpleGraph.Connected _))

instance (G : Digraph (Fin n)) [DecidableRel G.Adj] (s : Finset (Fin n)) :
    Decidable (G.IsConstituent s) :=
  decidable_of_iff _ Digraph.isConstituent_iff.symm

theorem Digraph.isCatena_singleton (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    G.IsCatena {v} := by
  rw [Digraph.IsCatena, Finset.coe_singleton]
  exact .of_subsingleton

theorem Digraph.connected_induce_reachSet (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (G.toSimpleGraphInclusive.induce {x | G.Reachable v x}).Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨⟨v, .refl⟩, ?_⟩
  rintro ⟨w, hw⟩
  induction hw with
  | refl => exact .rfl
  | @tail b c hb hbc ih =>
    rcases eq_or_ne b c with rfl | hne
    · exact ih
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨hne, Or.inl hbc⟩)

theorem Digraph.IsConstituent.isCatena {G : Digraph (Fin n)} [DecidableRel G.Adj]
    {s : Finset (Fin n)}
    (h : G.IsConstituent s) : G.IsCatena s := by
  obtain ⟨v, hv⟩ := h
  rw [Digraph.IsCatena, hv]
  exact Digraph.connected_induce_reachSet G v

theorem Digraph.isCatena_pair (G : Digraph (Fin n)) [DecidableRel G.Adj] {v w : Fin n}
    (h : G.Adj v w) (hne : v ≠ w) :
    G.IsCatena {v, w} := by
  rw [Digraph.IsCatena, Finset.coe_pair]
  exact SimpleGraph.induce_pair_connected_of_adj ⟨hne, .inl h⟩

theorem Digraph.not_isConstituent_pair {G : Digraph (Fin n)} [DecidableRel G.Adj]
    (hF : G.IsBranching) {v w u : Fin n}
    (hw : G.Adj v w) (hu : G.Adj v u) (huw : u ≠ w) : ¬ G.IsConstituent {v, w} := by
  rw [Digraph.isConstituent_iff]
  rintro ⟨c, hc⟩
  rcases Finset.mem_insert.mp ((hc c).2 Relation.ReflTransGen.refl) with rfl | hcw
  · rcases Finset.mem_insert.mp ((hc u).2 (Relation.ReflTransGen.single hu)) with rfl | hu'
    · exact hF.not_adj_self hu
    · exact huw (Finset.mem_singleton.mp hu')
  · rw [Finset.mem_singleton] at hcw; subst hcw
    exact hF.not_reachable_of_adj hw ((hc v).1 (by simp))

theorem Digraph.IsCatena.reachable_of_forall_not_adj {G : Digraph (Fin n)} [DecidableRel G.Adj]
    {s : Finset (Fin n)}
    (h : G.IsCatena s) (hF : G.IsBranching) {a : Fin n} (ha : a ∈ s)
    (hroot : ∀ u ∈ s, ¬ G.Adj u a) {b : Fin n} (hb : b ∈ s) : G.Reachable a b := by
  suffices ∀ y : (↑s : Set (Fin n)), Relation.ReflTransGen
      (G.toSimpleGraphInclusive.induce ↑s).Adj ⟨a, ha⟩ y → G.Reachable a y from
    this ⟨b, hb⟩ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (h.preconnected _ _))
  intro y hy
  induction hy with
  | refl => exact .refl
  | @tail x y _ hxy ih =>
    obtain ⟨-, hxy | hyx⟩ := hxy
    · exact ih.tail hxy
    · rcases eq_or_ne a x with rfl | hne
      · exact absurd hyx (hroot y y.2)
      · exact hF.reachable_of_reachable_of_adj ih hne hyx

/-- In a forest a set of positions is a catena iff exactly one of them, its root, has no head
among them. -/
theorem Digraph.IsBranching.isCatena_iff_existsUnique {G : Digraph (Fin n)} [DecidableRel G.Adj]
    (hF : G.IsBranching)
    {s : Finset (Fin n)} : G.IsCatena s ↔ ∃! v, v ∈ s ∧ ∀ u ∈ s, ¬ G.Adj u v := by
  have wf := hF.wellFounded_transGen
  refine ⟨fun h ↦ ?_, fun ⟨r, ⟨hr, hroot⟩, huniq⟩ ↦ ?_⟩
  · obtain ⟨⟨x, hx⟩⟩ := h.nonempty
    obtain ⟨r, hr, hmin⟩ := wf.has_min (↑s : Set (Fin n)) ⟨x, hx⟩
    have hroot : ∀ u ∈ s, ¬ G.Adj u r := fun u hu hur ↦ hmin u hu (.single hur)
    exact ⟨r, ⟨hr, hroot⟩, fun r' ⟨hr', hroot'⟩ ↦ hF.reachable_antisymm
      (h.reachable_of_forall_not_adj hF hr' hroot' hr)
      (h.reachable_of_forall_not_adj hF hr hroot hr')⟩
  · refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨⟨r, hr⟩, ?_⟩
    rintro ⟨x, hx⟩
    induction x using wf.induction with
    | _ x ih =>
      by_cases hx' : ∀ u ∈ s, ¬ G.Adj u x
      · obtain rfl := huniq x ⟨hx, hx'⟩
        exact .rfl
      · push Not at hx'
        obtain ⟨u, hu, hux⟩ := hx'
        exact (ih u (.single hux) hu).trans
          (SimpleGraph.Adj.reachable ⟨hF.ne_of_adj hux, .inl hux⟩)

theorem Digraph.IsBranching.isCatena_iff_card_eq_one {G : Digraph (Fin n)} [DecidableRel G.Adj]
    (hF : G.IsBranching) {s : Finset (Fin n)} :
    G.IsCatena s ↔ #{v ∈ s | ∀ u ∈ s, ¬ G.Adj u v} = 1 := by
  simp [hF.isCatena_iff_existsUnique, Finset.card_eq_one, Finset.eq_singleton_iff_unique_mem,
    ExistsUnique]

/-- A forest has as many constituents as positions. -/
theorem Digraph.IsBranching.card_isConstituent {G : Digraph (Fin n)} [DecidableRel G.Adj]
    (hF : G.IsBranching) :
    #{s : Finset (Fin n) | G.IsConstituent s} = n := by
  have h : ({s | G.IsConstituent s} : Finset (Finset (Fin n))) =
      Finset.univ.image fun v ↦ ({w | G.Reachable v w} : Finset (Fin n)) := by
    ext s
    simp [Digraph.isConstituent_iff, Finset.ext_iff, eq_comm]
  rw [h, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  exact fun v w hvw ↦ hF.reachSet_injective (Set.ext fun x ↦ by simpa using Finset.ext_iff.1 hvw x)

theorem Digraph.IsArborescence.isConstituent_univ {G : Digraph (Fin n)} [DecidableRel G.Adj]
    {r : Fin n} (hT : G.IsArborescence r) : G.IsConstituent Finset.univ :=
  Digraph.isConstituent_iff.2
    ⟨r, fun w ↦ ⟨fun _ ↦ hT.reachable w, fun _ ↦ Finset.mem_univ w⟩⟩

theorem Digraph.IsArborescence.isCatena_univ {G : Digraph (Fin n)} [DecidableRel G.Adj]
    {r : Fin n} (hT : G.IsArborescence r) : G.IsCatena Finset.univ :=
  hT.isConstituent_univ.isCatena

/-- The undirected view of an arborescence is a tree. -/
theorem Digraph.IsArborescence.isTree_toSimpleGraphInclusive {G : Digraph (Fin n)}
    [DecidableRel G.Adj] {r : Fin n} (hT : G.IsArborescence r) :
    G.toSimpleGraphInclusive.IsTree := by
  choose! p hp using fun w (hw : w ≠ r) ↦ hT.exists_adj_of_ne_root hw
  have hpeq {u w : Fin n} (h : G.Adj u w) : p w = u :=
    hT.leftUnique_adj (hp w fun e ↦ hT.not_adj_root u (e ▸ h)) h
  refine SimpleGraph.isTree_iff_connected_and_card.2 ⟨?_, ?_⟩
  · have h := hT.isCatena_univ
    rw [Digraph.IsCatena, Finset.coe_univ] at h
    exact G.toSimpleGraphInclusive.induceUnivIso.connected_iff.1 h
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  refine .trans (congrArg (· + 1) ?_) (Finset.card_erase_add_one (Finset.mem_univ r))
  refine (Finset.card_bij (fun w _ ↦ s(p w, w)) (fun w hw ↦ ?_) (fun w hw w' hw' h ↦ ?_)
    fun e he ↦ ?_).symm
  · have hw := hp w (Finset.ne_of_mem_erase hw)
    exact SimpleGraph.mem_edgeFinset.2 ⟨hT.ne_of_adj hw, Or.inl hw⟩
  · rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h₁, h₂⟩
    · exact h
    · have h₁' := hp w (Finset.ne_of_mem_erase hw)
      have h₂' := hp w' (Finset.ne_of_mem_erase hw')
      rw [h₁] at h₁'
      rw [← h₂] at h₂'
      exact absurd (Relation.ReflTransGen.single h₂') (hT.not_reachable_of_adj h₁')
  · induction e using Sym2.ind with
    | _ a b =>
    obtain ⟨-, hl⟩ : a ≠ b ∧ (G.Adj a b ∨ G.Adj b a) := SimpleGraph.mem_edgeFinset.1 he
    rcases hl with h | h
    · exact ⟨b, Finset.mem_erase.2 ⟨fun hb ↦ hT.not_adj_root a (hb ▸ h), Finset.mem_univ _⟩,
        by rw [hpeq h]⟩
    · exact ⟨a, Finset.mem_erase.2 ⟨fun ha ↦ hT.not_adj_root b (ha ▸ h), Finset.mem_univ _⟩,
        by rw [hpeq h, Sym2.eq_swap]⟩
