/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Algebra.Coproduct.TraceConservation

/-!
# Trace-aware size measures of workspaces

A workspace `F` on the carrier `UnorderedTree (α ⊕ β)`, with `Sum.inr` marking a trace, is measured
by its number of components `Multiset.card F`, its number of accessible terms, which are the
non-root vertices `(F.map UnorderedTree.numEdges).sum`, and its number of vertices, the
summed `numNodes`, which is `card F` plus the summed `numEdges`. Under the trace-preserving
coproduct a cut leaves a trace leaf that is not an accessible term,
so the trace-aware count discounts trace leaves:
`accessibleCount T = numEdges T − traceLeafCount T` on a tree, summed over a forest, and
`accessibleSize F = card F + accessibleCount F`. The extraction identities say how a Δ^c cut of
a lexical-rooted object splits its accessible terms between crown and trunk, one contraction per
cut.

## Main definitions

* `UnorderedTree.accessibleCount`, `Forest.accessibleCount`, `Forest.accessibleSize`

## Main results

* `ConnesKreimer.cutSummandsCN_accessibleCount`, `cutSummandsCN_accessibleSize`: the extraction
  identities for the accessible terms and for the size; over a forest,
  `hasExtractionCost_accessibleCount_cutSummandsCN` and
  `hasExtractionCost_accessibleSize_cutSummandsCN`.

## References

* [marcolli-chomsky-berwick-2025], §1.6.1–1.6.2 (Lemma 1.6.3)
-/

@[expose] public section

open RoseTree UnorderedTree

namespace UnorderedTree

variable {α β : Type*}

/-- `accessibleCount T = numEdges T − traceLeafCount T`, the accessible terms of `T` that are
    not traces. -/
def accessibleCount (t : UnorderedTree (α ⊕ β)) : ℕ := t.numEdges - t.traceLeafCount

@[simp] theorem accessibleCount_leaf_inl (a : α) :
    (leaf (Sum.inl a) : UnorderedTree (α ⊕ β)).accessibleCount = 0 := rfl

@[simp] theorem accessibleCount_leaf_inr (b : β) :
    (leaf (Sum.inr b) : UnorderedTree (α ⊕ β)).accessibleCount = 0 := rfl

private theorem numEdges_sub_countP_leaves_node_pair (p : α → Prop) [DecidablePred p] (a : α)
    (l r : UnorderedTree α) (hpa : ¬p a)
    (hl : l.leaves.countP p < l.numNodes) (hr : r.leaves.countP p < r.numNodes) :
    (UnorderedTree.node a {l, r}).numEdges - (UnorderedTree.node a {l, r}).leaves.countP p
      = (l.numEdges - l.leaves.countP p) + (r.numEdges - r.leaves.countP p) + 2 := by
  have hw := numEdges_node_pair a l r
  have htl : (UnorderedTree.node a {l, r}).leaves.countP p
      = l.leaves.countP p + r.leaves.countP p := by
    rw [countP_leaves_node_of_not p a _ hpa]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl := countP_leaves_le_numEdges p l hl
  have hbr := countP_leaves_le_numEdges p r hr
  simp only [htl, hw]
  omega

/-- External Merge adds two accessible terms. -/
theorem accessibleCount_merge (a : α) (l r : UnorderedTree (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (UnorderedTree.node (Sum.inl a) {l, r}).accessibleCount
      = l.accessibleCount + r.accessibleCount + 2 :=
  numEdges_sub_countP_leaves_node_pair (fun x : α ⊕ β => x.isRight = true) _ l r (by simp) hl hr

end UnorderedTree

namespace Forest

variable {α β : Type*}

/-- The accessible terms of a workspace that are not traces, summed over its components. -/
def accessibleCount (F : Multiset (UnorderedTree (α ⊕ β))) : ℕ :=
  (F.map UnorderedTree.accessibleCount).sum

@[simp] theorem accessibleCount_zero : accessibleCount (0 : Multiset (UnorderedTree (α ⊕ β))) = 0 :=
  rfl
@[simp] theorem accessibleCount_cons (T : UnorderedTree (α ⊕ β)) (F : Multiset (UnorderedTree
    (α ⊕ β))) :
    accessibleCount (T ::ₘ F) = T.accessibleCount + accessibleCount F := by
  simp only [accessibleCount, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem accessibleCount_singleton (T : UnorderedTree (α ⊕ β)) :
    accessibleCount ({T} : Multiset (UnorderedTree (α ⊕ β))) = T.accessibleCount := by
  simp only [accessibleCount, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem accessibleCount_add (F G : Multiset (UnorderedTree (α ⊕ β))) :
    accessibleCount (F + G) = accessibleCount F + accessibleCount G := by
  simp only [accessibleCount, Multiset.map_add, Multiset.sum_add]

/-- `accessibleSize F = card F + accessibleCount F`, the trace-aware size of a workspace. -/
def accessibleSize (F : Multiset (UnorderedTree (α ⊕ β))) : ℕ :=
  Multiset.card F + accessibleCount F

@[simp] theorem accessibleSize_zero : accessibleSize (0 : Multiset (UnorderedTree (α ⊕ β))) = 0 :=
  rfl
@[simp] theorem accessibleSize_cons (T : UnorderedTree (α ⊕ β)) (F : Multiset (UnorderedTree
    (α ⊕ β))) :
    accessibleSize (T ::ₘ F) = T.accessibleCount + 1 + accessibleSize F := by
  simp only [accessibleSize, Multiset.card_cons, accessibleCount_cons]; omega
@[simp] theorem accessibleSize_singleton (T : UnorderedTree (α ⊕ β)) :
    accessibleSize ({T} : Multiset (UnorderedTree (α ⊕ β))) = T.accessibleCount + 1 := by
  simp only [accessibleSize, Multiset.card_singleton, accessibleCount_singleton]; omega
@[simp] theorem accessibleSize_add (F G : Multiset (UnorderedTree (α ⊕ β))) :
    accessibleSize (F + G) = accessibleSize F + accessibleSize G := by
  simp only [accessibleSize, Multiset.card_add, accessibleCount_add]; omega

end Forest

namespace ConnesKreimer

variable {α β : Type*}

/-- A tree that is not a single trace splits its vertices into the root, its accessible terms and
    its trace leaves. -/
private theorem accessibleCount_add_traceLeafCount_add_one {t : UnorderedTree (α ⊕ β)}
    (h : t.traceLeafCount < t.numNodes) :
    t.accessibleCount + t.traceLeafCount + 1 = t.numNodes := by
  simp only [UnorderedTree.accessibleCount, UnorderedTree.numEdges]
  omega

/-- `accessibleCount T` is the crown's and the trunk's accessible terms plus one per tree extracted
by a Δ^c cut ([marcolli-chomsky-berwick-2025] (1.6.8)). -/
theorem cutSummandsCN_accessibleCount (τ : UnorderedTree (α ⊕ β) → β)
    {T : UnorderedTree (α ⊕ β)} {a₀ : α} (hT : T.value = Sum.inl a₀)
    {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)} (hp : p ∈ cutSummandsCN τ T) :
    T.accessibleCount =
      (p.1.map UnorderedTree.accessibleCount).sum + p.2.accessibleCount + Multiset.card p.1 := by
  have hw := cutSummandsCN_numNodes τ T p hp
  have hl := cutSummandsCN_traceLeafCount τ T p hp
  have hT' := accessibleCount_add_traceLeafCount_add_one
    (UnorderedTree.traceLeafCount_lt_numNodes_of_rootInl T a₀ hT)
  have hp2 := accessibleCount_add_traceLeafCount_add_one
    (UnorderedTree.traceLeafCount_lt_numNodes_of_rootInl p.2 a₀
      ((cutSummandsCN_trunk_value τ T p hp).trans hT))
  have hcrown : ∀ m : Multiset (UnorderedTree (α ⊕ β)), (∀ c ∈ m, c.traceLeafCount < c.numNodes) →
      (m.map UnorderedTree.accessibleCount).sum + (m.map UnorderedTree.traceLeafCount).sum +
        Multiset.card m = (m.map UnorderedTree.numNodes).sum := by
    intro m hm
    induction m using Multiset.induction with
    | empty => simp
    | cons c m ih =>
      have := accessibleCount_add_traceLeafCount_add_one (hm c (Multiset.mem_cons_self _ _))
      have := ih fun d hd ↦ hm d (Multiset.mem_cons_of_mem hd)
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      omega
  have := hcrown p.1 fun c hc ↦ cutSummandsCN_crown_traceLeafCount_lt_numNodes τ T p hp c hc
  omega

/-- A Δ^c cut of a lexical-rooted object splits its size `σ` exactly between its crown and its
    trunk ([marcolli-chomsky-berwick-2025] (1.6.10)). -/
theorem cutSummandsCN_accessibleSize (τ : UnorderedTree (α ⊕ β) → β)
    {T : UnorderedTree (α ⊕ β)} {a₀ : α} (hT : T.value = Sum.inl a₀)
    {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)} (hp : p ∈ cutSummandsCN τ T) :
    (p.1.map fun c ↦ Forest.accessibleSize {c}).sum + Forest.accessibleSize {p.2} =
      Forest.accessibleSize {T} := by
  have h := cutSummandsCN_accessibleCount τ hT hp
  have hsum : ∀ m : Multiset (UnorderedTree (α ⊕ β)),
      (m.map fun c ↦ Forest.accessibleSize {c}).sum =
        (m.map UnorderedTree.accessibleCount).sum + Multiset.card m := by
    intro m
    induction m using Multiset.induction with
    | empty => simp
    | cons c m ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons, ih, Forest.accessibleSize_singleton]
      omega
  rw [hsum, Forest.accessibleSize_singleton, Forest.accessibleSize_singleton]
  omega

section CutChoice

variable {τ : UnorderedTree (α ⊕ β) → β} {F : Multiset (UnorderedTree (α ⊕ β))}
  {s : CutChoice (α ⊕ β)}

/-- A tree in the crown of a choice of trace cuts is not a trace, when the trees cut or taken whole
    are not traces. -/
theorem traceLeafCount_lt_numNodes_of_mem_crown (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → ∃ a, x.1.value = Sum.inl a)
    {S : UnorderedTree (α ⊕ β)} (hS : S ∈ s.crown) : S.traceLeafCount < S.numNodes := by
  obtain ⟨x, hx, hSx⟩ := CutChoice.mem_crown.mp hS
  rcases mem_treeCutsG.mp (mem_treeCutsG_of_mem_forestCutChoicesG hs hx) with h | ⟨p, hp, h⟩
  · obtain ⟨a, ha⟩ := hF x hx (by rw [h]; exact Multiset.singleton_ne_zero _)
    rw [h, Multiset.mem_singleton] at hSx
    exact hSx ▸ UnorderedTree.traceLeafCount_lt_numNodes_of_rootInl _ a ha
  · rw [← h] at hSx
    exact cutSummandsCN_crown_traceLeafCount_lt_numNodes τ x.1 p hp S hSx

/-- Merging the two trees of the crown of a choice of trace cuts adds two accessible terms, when
    the trees cut or taken whole are not traces. -/
theorem accessibleCount_merge_of_crown_eq (a : α) (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → ∃ a, x.1.value = Sum.inl a) {S S' : UnorderedTree (α ⊕ β)}
    (hK : s.crown = {S, S'}) :
    (UnorderedTree.node (Sum.inl a) {S, S'}).accessibleCount =
      S.accessibleCount + S'.accessibleCount + 2 :=
  UnorderedTree.accessibleCount_merge a S S'
    (traceLeafCount_lt_numNodes_of_mem_crown hs hF (hK ▸ Multiset.mem_cons_self _ _))
    (traceLeafCount_lt_numNodes_of_mem_crown hs hF
      (hK ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)))

/-- A choice of trace cuts costs one accessible term for each tree it extracts, when the trees it
    cuts or takes whole are not traces. -/
theorem hasExtractionCost_accessibleCount_cutSummandsCN
    (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → ∃ a, x.1.value = Sum.inl a) :
    s.HasExtractionCost UnorderedTree.accessibleCount 1 := by
  refine .of_mem_forestCutChoicesG hs fun x hx p hp hpx ↦ ?_
  rw [one_mul]
  by_cases h0 : p.1 = 0
  · have : p = (0, x.1) := Multiset.mem_singleton.mp <| cutSummandsCN_filter_empty τ x.1 ▸
      Multiset.mem_filter.mpr ⟨hp, by rw [h0, Multiset.card_zero]⟩
    subst this
    simp
  · exact cutSummandsCN_accessibleCount τ (hF x hx (by rw [← hpx]; exact h0)).choose_spec hp

/-- A choice of trace cuts conserves the size `σ`, when the trees it cuts or takes whole are not
    traces. -/
theorem hasExtractionCost_accessibleSize_cutSummandsCN
    (hs : s ∈ forestCutChoicesG (cutSummandsCN τ) F)
    (hF : ∀ x ∈ s, x.2.1 ≠ 0 → ∃ a, x.1.value = Sum.inl a) :
    s.HasExtractionCost (fun T ↦ Forest.accessibleSize {T}) 0 := by
  refine .of_mem_forestCutChoicesG hs fun x hx p hp hpx ↦ ?_
  rw [Nat.zero_mul, Nat.add_zero]
  by_cases h0 : p.1 = 0
  · have : p = (0, x.1) := Multiset.mem_singleton.mp <| cutSummandsCN_filter_empty τ x.1 ▸
      Multiset.mem_filter.mpr ⟨hp, by rw [h0, Multiset.card_zero]⟩
    subst this
    simp
  · exact (cutSummandsCN_accessibleSize τ (hF x hx (by rw [← hpx]; exact h0)).choose_spec hp).symm

end CutChoice

end ConnesKreimer
