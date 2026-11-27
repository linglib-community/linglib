/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.MarkerCut
public import Linglib.Core.Data.UnorderedTree.Leaves
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Vertex, edge and marker counts of marker cuts

A marker cut contracts each subtree it extracts to a marker leaf. Its crown and trunk therefore
have, between them, the vertices of the tree and one more for each extracted subtree, the edges of
the tree exactly, and the markers of the tree and one more for each extracted subtree. The
conservation of edges makes the number of edges a grading of the marker coproduct.

## Main definitions

* `RoseTree.numMarkers`, `UnorderedTree.numMarkers`: the number of marker leaves.

## Main results

* `ConnesKreimer.markerCuts_numNodes`: crown and trunk vertices recover the tree's vertices plus
  one per extracted tree.
* `ConnesKreimer.markerCuts_numEdges`: crown and trunk edges recover the tree's edges.
* `ConnesKreimer.markerCuts_numMarkers`: markers are conserved up to one per extracted tree.
* `ConnesKreimer.markerCuts_crown_numEdges_lt`: a nonempty crown has fewer edges than the tree.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace RoseTree

variable {α β : Type*}

/-- The number of markers of a tree, its `Sum.inr`-labelled leaves. -/
def numMarkers (t : RoseTree (α ⊕ β)) : ℕ := t.leaves.countP (·.isRight = true)

@[simp] theorem numMarkers_leaf_inr (b : β) :
    numMarkers (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 1 := by
  simp [numMarkers, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem numMarkers_leaf_inl (a : α) :
    numMarkers (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := by
  simp [numMarkers, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

theorem numMarkers_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : numMarkers (.node v cs) = (cs.map numMarkers).sum :=
  countP_leaves_node_of_ne_nil _ v h

@[simp] theorem numMarkers_node_cons (v : α ⊕ β) (c : RoseTree (α ⊕ β))
    (cs : List (RoseTree (α ⊕ β))) :
    numMarkers (.node v (c :: cs)) = ((c :: cs).map numMarkers).sum :=
  countP_leaves_node_cons _ v c cs

@[simp] theorem numMarkers_node_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    numMarkers (.node (Sum.inl a) cs) = (cs.map numMarkers).sum :=
  countP_leaves_node_of_not _ cs (by simp)

end RoseTree

namespace UnorderedTree

variable {α β : Type*}

/-- The number of markers of a nonplanar tree, its `Sum.inr`-labelled leaves. -/
def numMarkers (t : UnorderedTree (α ⊕ β)) : ℕ := t.leaves.countP (·.isRight = true)

@[simp] theorem numMarkers_mk (t : RoseTree (α ⊕ β)) :
    (mk t).numMarkers = t.numMarkers := rfl

@[simp] theorem numMarkers_leaf_inl (a : α) :
    (leaf (Sum.inl a) : UnorderedTree (α ⊕ β)).numMarkers = 0 := by
  simp [numMarkers, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem numMarkers_leaf_inr (b : β) :
    (leaf (Sum.inr b) : UnorderedTree (α ⊕ β)).numMarkers = 1 := by
  simp [numMarkers, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem numMarkers_node_inl (a : α) (F : Multiset (UnorderedTree (α ⊕ β))) :
    (UnorderedTree.node (Sum.inl a) F).numMarkers
      = (F.map UnorderedTree.numMarkers).sum :=
  countP_leaves_node_of_not _ _ F (by simp)

theorem numMarkers_lt_numNodes_of_isLeft {t : UnorderedTree (α ⊕ β)} (h : t.value.isLeft) :
    t.numMarkers < t.numNodes :=
  countP_leaves_lt_numNodes_of_not_root _ t <| by
    obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp h
    simp [ha]

end UnorderedTree

namespace ConnesKreimer

variable {α β : Type*}

/-! ### Marker conservation for a policy leaving one marker per cut -/

section Policy

variable (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))

private theorem remainder_ne_nil_of_mem_childrenCuts
    (hne : ∀ t r, extract t = some r → r ≠ []) :
    ∀ cs, ∀ q ∈ childrenCuts extract cs, cs ≠ [] → q.2 ≠ [] :=
  childrenCuts_induction extract (P := fun cs q ↦ cs ≠ [] → q.2 ≠ [])
    (fun h ↦ (h rfl).elim) (fun t r h _ ↦ hne t r h) (fun _ _ _ _ _ _ ↦ List.cons_ne_nil _ _)
    (fun _ _ _ _ _ _ ha _ _ ↦ List.append_ne_nil_of_left_ne_nil (ha (List.cons_ne_nil _ _)) _)

private theorem two_le_numNodes_of_mem_rootCuts (hne : ∀ t r, extract t = some r → r ≠ []) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ rootCuts extract t, p.1 ≠ 0 → 2 ≤ p.2.numNodes
  | .node a [], p, hp, h => by
    simp only [rootCuts_node, childrenCuts_nil, Multiset.map_singleton,
      Multiset.mem_singleton] at hp
    exact (h (congrArg Prod.fst hp)).elim
  | .node a (c :: cs), p, hp, _ => by
    rw [rootCuts_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil
      (remainder_ne_nil_of_mem_childrenCuts extract hne _ q hq (List.cons_ne_nil c cs))
    have := d.numNodes_pos
    simp only [hd, RoseTree.numNodes_node, List.map_cons, List.sum_cons]
    omega

/-- When each remainder carries one marker, the crown and the trunk of a cut carry the tree's
    markers and one more for each tree extracted. -/
theorem rootCuts_numMarkers
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numMarkers).sum = 1) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ rootCuts extract t,
      (Multiset.map RoseTree.numMarkers p.1).sum + RoseTree.numMarkers p.2 =
        RoseTree.numMarkers t + Multiset.card p.1 := fun t p hp ↦ by
  have hne : ∀ t r, extract t = some r → r ≠ [] := fun t r h hr ↦ by simpa [hr] using hext t r h
  simpa using rootCuts_induction extract
    (P := fun cs q ↦ (q.1.map RoseTree.numMarkers).sum + (q.2.map RoseTree.numMarkers).sum =
      (cs.map RoseTree.numMarkers).sum + Multiset.card q.1)
    (by simp) (fun t r h ↦ by simp [hext t r h])
    (fun a cs q hq hs ↦ by
      rcases eq_or_ne cs [] with rfl | hcs
      · rw [childrenCuts_nil, Multiset.mem_singleton] at hq
        subst hq
        simp
      · have h2 := remainder_ne_nil_of_mem_childrenCuts extract hne cs q hq hcs
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          RoseTree.numMarkers_node_of_ne_nil _ _ h2, RoseTree.numMarkers_node_of_ne_nil _ _ hcs]
        omega)
    (fun t ts a b _ _ ha hb ↦ by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Multiset.map_add,
        Multiset.sum_add, List.map_append, List.sum_append, Multiset.card_add] at *
      omega) t p hp

end Policy

/-! ### The marker cuts -/

variable (τ : UnorderedTree (α ⊕ β) → β)

/-- The marker cuts conserve vertices up to one marker leaf per extracted tree. -/
theorem markerCuts_numNodes (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ markerCuts τ T,
      (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes = T.numNodes + Multiset.card p.1 :=
  Quotient.inductionOn T fun t p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, markerCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projCut, Multiset.map_map, Function.comp_def] using
      rootCuts_numNodes (leaveMarker (τ ∘ UnorderedTree.mk)) (k := 1)
        (fun s _ h ↦ by obtain ⟨_ | _, _⟩ := s <;> simp at h; simp [← h, markerLeaf]) t q hq

/-- The marker cuts conserve edges. -/
theorem markerCuts_numEdges (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ markerCuts τ T,
      (p.1.map UnorderedTree.numEdges).sum + p.2.numEdges = T.numEdges := fun p hp ↦ by
  have := markerCuts_numNodes τ T p hp
  rw [UnorderedTree.sum_map_numNodes, ← p.2.numEdges_add_one, ← T.numEdges_add_one] at this
  omega

/-- The marker cuts conserve markers up to one per extracted tree. -/
theorem markerCuts_numMarkers (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ markerCuts τ T,
      (p.1.map UnorderedTree.numMarkers).sum + p.2.numMarkers =
        T.numMarkers + Multiset.card p.1 :=
  Quotient.inductionOn T fun t p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, markerCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projCut, Multiset.map_map, Function.comp_def] using
      rootCuts_numMarkers (leaveMarker (τ ∘ UnorderedTree.mk))
        (fun s _ h ↦ by obtain ⟨_ | _, _⟩ := s <;> simp at h; simp [← h, markerLeaf]) t q hq

/-- A marker cut of a tree without markers that leaves no marker is the empty cut, since each tree
it extracts leaves one. -/
theorem eq_zero_of_mem_markerCuts {T : UnorderedTree (α ⊕ β)} (hT : T.numMarkers = 0)
    {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)} (hp : p ∈ markerCuts τ T)
    (h : p.2.numMarkers = 0) : p = (0, T) := by
  have hcrown : (p.1.map UnorderedTree.numMarkers).sum = 0 :=
    Multiset.sum_eq_zero fun n hn ↦ by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hn
      have hxT := markerCuts_mem_subtrees_of_mem_crown τ hp hx
      induction T using Quotient.inductionOn with
      | h t =>
        rw [UnorderedTree.quot_mk_eq_mk, UnorderedTree.subtrees_mk,
          RoseTree.unorderedSubtrees_eq_map, Multiset.mem_coe, List.mem_map] at hxT
        obtain ⟨s, hs, rfl⟩ := hxT
        exact Nat.eq_zero_of_le_zero <|
          (Multiset.countP_le_of_le _ (RoseTree.mem_subtrees.1 hs).leaves_le).trans_eq hT
  have hcard := markerCuts_numMarkers τ T p hp
  rw [hcrown, h, hT, zero_add, zero_add] at hcard
  have hmem : p ∈ (markerCuts τ T).filter (fun p ↦ p.1.card = 0) :=
    Multiset.mem_filter.2 ⟨hp, hcard.symm⟩
  rwa [markerCuts_filter_empty, Multiset.mem_singleton] at hmem

/-- Every tree a marker cut extracts has an `inl` root, since markers are never cut. -/
theorem markerCuts_value_isLeft_of_mem_crown (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ markerCuts τ T, ∀ Tv ∈ p.1, Tv.value.isLeft :=
  Quotient.inductionOn T fun t p hp x hx ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, markerCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨⟨_ | _, cs⟩, hy, rfl⟩ := Multiset.mem_map.mp hx
    · rfl
    · simpa using isSome_of_mem_crown_rootCuts _ t q hq _ hy

/-- A marker cut never touches the root, so the trunk keeps the tree's root label. -/
theorem markerCuts_trunk_value (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ markerCuts τ T, p.2.value = T.value :=
  Quotient.inductionOn T fun ⟨a, cs⟩ p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, markerCuts_mk, rootCuts_node,
      Multiset.map_map] at hp
    obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp hp
    rfl

/-- A marker cut with a nonempty crown leaves a trunk with at least two vertices, the root and a
    marker. -/
theorem markerCuts_two_le_trunk_numNodes (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ markerCuts τ T, p.1 ≠ 0 → 2 ≤ p.2.numNodes :=
  Quotient.inductionOn T fun t p hp h ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, markerCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact two_le_numNodes_of_mem_rootCuts _
      (fun s _ h ↦ by obtain ⟨_ | _, _⟩ := s <;> simp at h; simp [← h]) t q hq
      fun h0 ↦ h (by simp [projCut, h0])

/-- A nonempty crown of a marker cut has fewer edges in total than the tree. -/
theorem markerCuts_crown_numEdges_lt {T : UnorderedTree (α ⊕ β)}
    {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)}
    (hp : p ∈ markerCuts τ T) (h : p.1 ≠ 0) :
    (p.1.map UnorderedTree.numEdges).sum < T.numEdges := by
  have := markerCuts_numEdges τ T p hp
  have := markerCuts_two_le_trunk_numNodes τ T p hp h
  have := p.2.numEdges_add_one
  omega

end ConnesKreimer
