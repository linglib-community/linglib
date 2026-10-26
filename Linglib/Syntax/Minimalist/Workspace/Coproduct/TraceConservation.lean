/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceCut
public import Linglib.Core.Data.UnorderedTree.Count
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Trace statistics of cuts

The size bookkeeping of the trace cuts `cutSummandsCN` of Marcolli, Chomsky and Berwick. A cut
contracts each tree it extracts to a leaf labelled by the trace of that tree, so its trunk is the
quotient by contraction of their Definition 1.2.4 (p. 30); here a trace is a `Sum.inr`-labelled
leaf. Vertices are then conserved up to one trace per extracted tree, the count in the proof of
their Lemma 1.6.3 (p. 65), and edges exactly, which makes the number of edges a grading of `Δ^c`
(their Lemma 1.2.10, p. 37). Traces are conserved up to one per extracted tree.

## Main definitions

* `RoseTree.numTraces`, `UnorderedTree.numTraces`: the number of traces.

## Main results

* `ConnesKreimer.cutSummandsCN_numNodes`: crown and trunk vertices recover the tree's vertices plus
  one per extracted tree.
* `ConnesKreimer.cutSummandsCN_numEdges`: crown and trunk edges recover the tree's edges.
* `ConnesKreimer.cutSummandsCN_numTraces`: traces are conserved up to one per extracted tree.
* `ConnesKreimer.cutSummandsCN_crown_numEdges_lt`: a nonempty crown has fewer edges than the tree.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace RoseTree

variable {α β : Type*}

/-- The number of traces of a tree, its `Sum.inr`-labelled leaves. -/
def numTraces (t : RoseTree (α ⊕ β)) : ℕ := t.leaves.countP (·.isRight = true)

@[simp] theorem numTraces_leaf_inr (b : β) :
    numTraces (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 1 := by
  simp [numTraces, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem numTraces_leaf_inl (a : α) :
    numTraces (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := by
  simp [numTraces, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

theorem numTraces_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : numTraces (.node v cs) = (cs.map numTraces).sum :=
  countP_leaves_node_of_ne_nil _ v h

@[simp] theorem numTraces_node_cons (v : α ⊕ β) (c : RoseTree (α ⊕ β))
    (cs : List (RoseTree (α ⊕ β))) :
    numTraces (.node v (c :: cs)) = ((c :: cs).map numTraces).sum :=
  countP_leaves_node_cons _ v c cs

@[simp] theorem numTraces_node_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    numTraces (.node (Sum.inl a) cs) = (cs.map numTraces).sum :=
  countP_leaves_node_of_not _ cs (by simp)

end RoseTree

namespace UnorderedTree

variable {α β : Type*}

/-- The number of traces of a nonplanar tree, its `Sum.inr`-labelled leaves. -/
def numTraces (t : UnorderedTree (α ⊕ β)) : ℕ := t.leaves.countP (·.isRight = true)

@[simp] theorem numTraces_mk (t : RoseTree (α ⊕ β)) :
    (mk t).numTraces = t.numTraces := rfl

@[simp] theorem numTraces_leaf_inl (a : α) :
    (leaf (Sum.inl a) : UnorderedTree (α ⊕ β)).numTraces = 0 := by
  simp [numTraces, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem numTraces_leaf_inr (b : β) :
    (leaf (Sum.inr b) : UnorderedTree (α ⊕ β)).numTraces = 1 := by
  simp [numTraces, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem numTraces_node_inl (a : α) (F : Multiset (UnorderedTree (α ⊕ β))) :
    (UnorderedTree.node (Sum.inl a) F).numTraces
      = (F.map UnorderedTree.numTraces).sum :=
  countP_leaves_node_of_not _ _ F (by simp)

theorem numTraces_lt_numNodes_of_isLeft {t : UnorderedTree (α ⊕ β)} (h : t.value.isLeft) :
    t.numTraces < t.numNodes :=
  countP_leaves_lt_numNodes_of_not_root _ t <| by
    obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp h
    simp [ha]

end UnorderedTree

namespace ConnesKreimer

variable {α β : Type*}

/-! ### Trace conservation for a policy leaving one trace per cut -/

section Policy

variable (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))

private theorem remainder_ne_nil_of_mem_cutListSummandsG
    (hne : ∀ t r, extract t = some r → r ≠ []) :
    ∀ cs, ∀ q ∈ cutListSummandsG extract cs, cs ≠ [] → q.2 ≠ [] :=
  cutListSummandsG_induction extract (P := fun cs q ↦ cs ≠ [] → q.2 ≠ [])
    (fun h ↦ (h rfl).elim) (fun t r h _ ↦ hne t r h) (fun _ _ _ _ _ _ ↦ List.cons_ne_nil _ _)
    (fun _ _ _ _ _ _ ha _ _ ↦ List.append_ne_nil_of_left_ne_nil (ha (List.cons_ne_nil _ _)) _)

private theorem two_le_numNodes_of_mem_cutSummandsG (hne : ∀ t r, extract t = some r → r ≠ []) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t, p.1 ≠ 0 → 2 ≤ p.2.numNodes
  | .node a [], p, hp, h => by
    simp only [cutSummandsG_node, cutListSummandsG_nil, Multiset.map_singleton,
      Multiset.mem_singleton] at hp
    exact (h (congrArg Prod.fst hp)).elim
  | .node a (c :: cs), p, hp, _ => by
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil
      (remainder_ne_nil_of_mem_cutListSummandsG extract hne _ q hq (List.cons_ne_nil c cs))
    have := d.numNodes_pos
    simp only [hd, RoseTree.numNodes_node, List.map_cons, List.sum_cons]
    omega

/-- When each remainder carries one trace, the crown and the trunk of a cut carry the tree's traces
    and one more for each tree extracted. -/
theorem cutSummandsG_numTraces
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numTraces).sum = 1) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.numTraces p.1).sum + RoseTree.numTraces p.2 =
        RoseTree.numTraces t + Multiset.card p.1 := fun t p hp ↦ by
  have hne : ∀ t r, extract t = some r → r ≠ [] := fun t r h hr ↦ by simpa [hr] using hext t r h
  simpa using cutSummandsG_induction extract
    (P := fun cs q ↦ (q.1.map RoseTree.numTraces).sum + (q.2.map RoseTree.numTraces).sum =
      (cs.map RoseTree.numTraces).sum + Multiset.card q.1)
    (by simp) (fun t r h ↦ by simp [hext t r h])
    (fun a cs q hq hs ↦ by
      rcases eq_or_ne cs [] with rfl | hcs
      · rw [cutListSummandsG_nil, Multiset.mem_singleton] at hq
        subst hq
        simp
      · have h2 := remainder_ne_nil_of_mem_cutListSummandsG extract hne cs q hq hcs
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          RoseTree.numTraces_node_of_ne_nil _ _ h2, RoseTree.numTraces_node_of_ne_nil _ _ hcs]
        omega)
    (fun t ts a b _ _ ha hb ↦ by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Multiset.map_add,
        Multiset.sum_add, List.map_append, List.sum_append, Multiset.card_add] at *
      omega) t p hp

end Policy

/-! ### The trace cuts -/

variable (τ : UnorderedTree (α ⊕ β) → β)

/-- The trace cuts conserve vertices up to one trace leaf per extracted tree. -/
theorem cutSummandsCN_numNodes (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes = T.numNodes + Multiset.card p.1 :=
  Quotient.inductionOn T fun t p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projSummand, Multiset.map_map, Function.comp_def] using
      cutSummandsG_numNodes (extractC (τ ∘ UnorderedTree.mk)) (k := 1)
        (fun s _ h ↦ by obtain ⟨_ | _, _⟩ := s <;> simp at h; simp [← h, traceLeaf]) t q hq

/-- The trace cuts conserve edges. -/
theorem cutSummandsCN_numEdges (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.numEdges).sum + p.2.numEdges = T.numEdges := fun p hp ↦ by
  have := cutSummandsCN_numNodes τ T p hp
  rw [UnorderedTree.sum_map_numNodes, ← p.2.numEdges_add_one, ← T.numEdges_add_one] at this
  omega

/-- The trace cuts conserve traces up to one per extracted tree. -/
theorem cutSummandsCN_numTraces (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.numTraces).sum + p.2.numTraces =
        T.numTraces + Multiset.card p.1 :=
  Quotient.inductionOn T fun t p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    simpa [projSummand, Multiset.map_map, Function.comp_def] using
      cutSummandsG_numTraces (extractC (τ ∘ UnorderedTree.mk))
        (fun s _ h ↦ by obtain ⟨_ | _, _⟩ := s <;> simp at h; simp [← h, traceLeaf]) t q hq

/-- Every tree a trace cut extracts has a lexical root, since traces are never cut. -/
theorem cutSummandsCN_value_isLeft_of_mem_crown (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, ∀ Tv ∈ p.1, Tv.value.isLeft :=
  Quotient.inductionOn T fun t p hp x hx ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨⟨_ | _, cs⟩, hy, rfl⟩ := Multiset.mem_map.mp hx
    · rfl
    · simpa using isSome_of_mem_crown_cutSummandsG _ t q hq _ hy

/-- A trace cut never touches the root, so the trunk keeps the tree's root label. -/
theorem cutSummandsCN_trunk_value (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, p.2.value = T.value :=
  Quotient.inductionOn T fun ⟨a, cs⟩ p hp ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk, cutSummandsCP_node,
      Multiset.map_map] at hp
    obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp hp
    rfl

/-- A trace cut with a nonempty crown leaves a trunk with at least two vertices, the root and a
    trace. -/
theorem cutSummandsCN_two_le_trunk_numNodes (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, p.1 ≠ 0 → 2 ≤ p.2.numNodes :=
  Quotient.inductionOn T fun t p hp h ↦ by
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact two_le_numNodes_of_mem_cutSummandsG _
      (fun s _ h ↦ by obtain ⟨_ | _, _⟩ := s <;> simp at h; simp [← h]) t q hq
      fun h0 ↦ h (by simp [projSummand, h0])

/-- A nonempty crown of a trace cut has fewer edges in total than the tree. -/
theorem cutSummandsCN_crown_numEdges_lt {T : UnorderedTree (α ⊕ β)}
    {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)}
    (hp : p ∈ cutSummandsCN τ T) (h : p.1 ≠ 0) :
    (p.1.map UnorderedTree.numEdges).sum < T.numEdges := by
  have := cutSummandsCN_numEdges τ T p hp
  have := cutSummandsCN_two_le_trunk_numNodes τ T p hp h
  have := p.2.numEdges_add_one
  omega

end ConnesKreimer
