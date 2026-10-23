/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Coproduct.TraceCut
public import Linglib.Core.Data.UnorderedTree.Count
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

@[expose] public section

open RoseTree UnorderedTree

/-!
# Trace statistics of cuts

The size bookkeeping of the trace cuts `cutSummandsCN` of Marcolli, Chomsky and Berwick. A trace is
a `Sum.inr`-labelled leaf; a cut splits a tree into a crown forest and a trunk carrying one trace
per cut. Vertices are conserved up to the new traces, traces up to one per cut, and lexical
vertices exactly.

## Main definitions

* `RoseTree.traceLeafCount`, `UnorderedTree.traceLeafCount`: the number of traces.

## Main results

* `ConnesKreimer.cutSummandsCN_numNodes`: crown and trunk vertices recover the tree's vertices
  plus one trace per cut (Lemma 1.6.3).
* `ConnesKreimer.cutSummandsCN_traceLeafCount`: traces are conserved up to one per cut.
* `ConnesKreimer.cutSummandsCN_lexical_conservation`: lexical vertices are conserved exactly.
* `ConnesKreimer.cutSummandsCN_crown_numEdges_lt`: a nonempty crown has fewer edges than the tree.

## References

* [marcolli-chomsky-berwick-2025]
-/

namespace RoseTree

variable {α β : Type*}

/-- The number of `Sum.inr`-labeled (trace-marker) leaves in a tree. -/
def traceLeafCount (t : RoseTree (α ⊕ β)) : ℕ := t.leaves.countP (·.isRight = true)

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    traceLeafCount (.node (Sum.inr b) [] : RoseTree (α ⊕ β)) = 1 := by
  simp [traceLeafCount, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    traceLeafCount (.node (Sum.inl a) [] : RoseTree (α ⊕ β)) = 0 := by
  simp [traceLeafCount, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

theorem traceLeafCount_node_of_ne_nil (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β)))
    (h : cs ≠ []) : traceLeafCount (.node v cs) = (cs.map traceLeafCount).sum :=
  countP_leaves_node_of_ne_nil _ v h

@[simp] theorem traceLeafCount_node_cons (v : α ⊕ β) (c : RoseTree (α ⊕ β))
    (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node v (c :: cs)) = ((c :: cs).map traceLeafCount).sum :=
  countP_leaves_node_cons _ v c cs

@[simp] theorem traceLeafCount_node_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (.node (Sum.inl a) cs) = (cs.map traceLeafCount).sum :=
  countP_leaves_node_of_not _ cs (by simp)

theorem traceLeafCount_perm {t s : RoseTree (α ⊕ β)} (h : Perm t s) :
    t.traceLeafCount = s.traceLeafCount :=
  congrArg (Multiset.countP _) (leaves_perm h)

theorem traceLeafCount_le_node (v : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    (cs.map traceLeafCount).sum ≤ traceLeafCount (.node v cs) :=
  sum_map_countP_leaves_le_node _ v cs

theorem traceLeafCount_le_numNodes (t : RoseTree (α ⊕ β)) :
    t.traceLeafCount ≤ t.numNodes :=
  countP_leaves_le_numNodes _ t

theorem traceLeafCount_lt_numNodes_of_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    traceLeafCount (RoseTree.node (Sum.inl a) cs) <
      numNodes (RoseTree.node (Sum.inl a) cs) :=
  countP_leaves_lt_numNodes_of_not _ cs (by simp)

end RoseTree


namespace UnorderedTree

variable {α β : Type*}

/-- The number of `Sum.inr`-labeled (trace-marker) leaves of a nonplanar tree. -/
def traceLeafCount (t : UnorderedTree (α ⊕ β)) : ℕ := t.leaves.countP (·.isRight = true)

@[simp] theorem traceLeafCount_mk (t : RoseTree (α ⊕ β)) :
    (mk t).traceLeafCount = t.traceLeafCount := rfl

@[simp] theorem traceLeafCount_leaf_inl (a : α) :
    (leaf (Sum.inl a) : UnorderedTree (α ⊕ β)).traceLeafCount = 0 := by
  simp [traceLeafCount, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem traceLeafCount_leaf_inr (b : β) :
    (leaf (Sum.inr b) : UnorderedTree (α ⊕ β)).traceLeafCount = 1 := by
  simp [traceLeafCount, Multiset.countP_eq_card_filter, Multiset.filter_singleton]

@[simp] theorem traceLeafCount_node_inl (a : α) (F : Multiset (UnorderedTree (α ⊕ β))) :
    (UnorderedTree.node (Sum.inl a) F).traceLeafCount
      = (F.map UnorderedTree.traceLeafCount).sum :=
  countP_leaves_node_of_not _ _ F (by simp)

theorem traceLeafCount_lt_numNodes_of_rootInl (t : UnorderedTree (α ⊕ β)) (x : α)
    (h : t.value = Sum.inl x) : t.traceLeafCount < t.numNodes :=
  countP_leaves_lt_numNodes_of_not_root _ t (by rw [h]; simp)

end UnorderedTree

namespace ConnesKreimer

variable {α β : Type*}

/-! ### Tree-level trace-leaf conservation -/

/-- Under nonempty-replacement extraction, every per-child action leaves a
    nonempty remainder. -/
private theorem augActionG_remainder_ne_nil
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ []) (t : RoseTree (α ⊕ β)) :
    ∀ a ∈ augActionG extract t, a.2 ≠ [] := by
  intro a ha
  rw [augActionG_eq] at ha
  rcases Multiset.mem_add.mp ha with h | h
  · cases hex : extract t with
    | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
    | some r =>
      rw [hex] at h
      obtain rfl := Multiset.mem_singleton.mp h
      exact hne t r hex
  · obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp h
    exact List.cons_ne_nil _ _

/-- Under nonempty-replacement extraction, a cut of a nonempty child list
    leaves a nonempty remainder list. -/
private theorem cutListSummandsG_remainder_ne_nil
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ [])
    (t : RoseTree (α ⊕ β)) (ts : List (RoseTree (α ⊕ β))) :
    ∀ q ∈ cutListSummandsG extract (t :: ts), q.2 ≠ [] := by
  intro q hq
  rw [cutListSummandsG_cons] at hq
  obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
  obtain ⟨ha, _⟩ := Multiset.mem_product.mp hpr
  have h1 := augActionG_remainder_ne_nil extract hne t pr.1 ha
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil h1
  show pr.1.2 ++ pr.2.2 ≠ []
  simp [hc]

/-- A unit-trace replacement `r` is nonempty. -/
private theorem ne_nil_of_traceLeafCount_sum_one
    (r : List (RoseTree (α ⊕ β))) (h : (r.map RoseTree.traceLeafCount).sum = 1) : r ≠ [] := by
  rintro rfl
  simp at h

mutual

/-- Under replacements carrying one trace each, crown traces plus trunk traces recover the
    tree's traces plus one per cut, since each contraction replaces an extracted subtree by one
    `Sum.inr` leaf. -/
theorem cutSummandsG_traceLeafCount
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.traceLeafCount).sum = 1) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.traceLeafCount p.1).sum + RoseTree.traceLeafCount p.2 =
        RoseTree.traceLeafCount t + Multiset.card p.1
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsG_traceLeafCount extract hext cs q hq
    cases a with
    | inl x =>
      simp only [RoseTree.traceLeafCount_node_inl]
      omega
    | inr y =>
      have hne : ∀ t r, extract t = some r → r ≠ [] :=
        fun t r h => ne_nil_of_traceLeafCount_sum_one r (hext t r h)
      rcases eq_or_ne cs [] with hcs | hcs
      · subst hcs
        rw [cutListSummandsG_nil] at hq
        obtain rfl := Multiset.mem_singleton.mp hq
        simp
      · have hq2 : q.2 ≠ [] := by
          obtain ⟨t', ts', rfl⟩ := List.exists_cons_of_ne_nil hcs
          exact cutListSummandsG_remainder_ne_nil extract hne t' ts' q hq
        rw [RoseTree.traceLeafCount_node_of_ne_nil (Sum.inr y) q.2 hq2,
            RoseTree.traceLeafCount_node_of_ne_nil (Sum.inr y) cs hcs]
        omega

/-- Trace-leaf conservation for the cut summands of a children list. -/
theorem cutListSummandsG_traceLeafCount
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.traceLeafCount).sum = 1) :
    ∀ (cs : List (RoseTree (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map RoseTree.traceLeafCount q.1).sum + (q.2.map RoseTree.traceLeafCount).sum =
        (cs.map RoseTree.traceLeafCount).sum + Multiset.card q.1
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    simp
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_traceLeafCount extract hext t pr.1 ha
    have h2 := cutListSummandsG_traceLeafCount extract hext ts pr.2 hq'
    rw [Multiset.map_add, Multiset.sum_add, List.map_append, List.sum_append,
        Multiset.card_add, List.map_cons, List.sum_cons]
    omega

/-- Trace-leaf conservation for the per-child actions. -/
theorem augActionG_traceLeafCount
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.traceLeafCount).sum = 1) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ a ∈ augActionG extract t,
      (Multiset.map RoseTree.traceLeafCount a.1).sum + (a.2.map RoseTree.traceLeafCount).sum =
        RoseTree.traceLeafCount t + Multiset.card a.1
  | t => by
    intro a ha
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        have hr := hext t r hex
        rw [Multiset.map_singleton, Multiset.sum_singleton, hr, Multiset.card_singleton]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      have h := cutSummandsG_traceLeafCount extract hext t p hp
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

end

mutual

/-- Crown trace leaves are bounded by the source's. The extracted
    crown forest of any cut has no more trace leaves than the whole tree, since
    each crown component is a subtree. Independent of the replacement policy
    (no `hext` hypothesis) — only the crown side is counted. Together with
    `cutSummandsG_traceLeafCount` this forces ≥ 1 fresh trace per cut into the
    trunk (`cutSummandsCN_trunk_traceLeafCount_ge_card`). -/
theorem cutSummandsG_crown_traceLeafCount_le
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.traceLeafCount p.1).sum ≤ RoseTree.traceLeafCount t
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact (cutListSummandsG_crown_traceLeafCount_le extract cs q hq).trans
      (RoseTree.traceLeafCount_le_node a cs)

/-- The crown trace-leaf bound for the cut summands of a children list. -/
theorem cutListSummandsG_crown_traceLeafCount_le
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (cs : List (RoseTree (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map RoseTree.traceLeafCount q.1).sum ≤ (cs.map RoseTree.traceLeafCount).sum
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    exact Nat.zero_le _
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_crown_traceLeafCount_le extract t pr.1 ha
    have h2 := cutListSummandsG_crown_traceLeafCount_le extract ts pr.2 hq'
    rw [Multiset.map_add, Multiset.sum_add, List.map_cons, List.sum_cons]
    omega

/-- The crown trace-leaf bound for the per-child actions. -/
theorem augActionG_crown_traceLeafCount_le
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ a ∈ augActionG extract t,
      (Multiset.map RoseTree.traceLeafCount a.1).sum ≤ RoseTree.traceLeafCount t
  | t => by
    intro a ha
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        simp only [Multiset.map_singleton, Multiset.sum_singleton, le_refl]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      exact cutSummandsG_crown_traceLeafCount_le extract t p hp

end

/-- The Δ^c extraction policy leaves unit-trace-count replacements. -/
private theorem extractC_traceLeafCount_sum_one (τ : RoseTree (α ⊕ β) → β) :
    ∀ t r, extractC τ t = some r → (r.map RoseTree.traceLeafCount).sum = 1 := by
  intro t r h
  cases t with
  | node x cs =>
    cases x with
    | inl a => rw [extractC_inl] at h; obtain rfl := Option.some.inj h; simp [traceLeaf]
    | inr b => rw [extractC_inr] at h; exact absurd h (by simp)

/-- The Δ^c node-count conservation (tree level), specializing the generic
    `cutSummandsG_numNodes` to `extractC`. -/
private theorem extractC_numNodes_sum_one (τ : RoseTree (α ⊕ β) → β) :
    ∀ t r, extractC τ t = some r → (r.map RoseTree.numNodes).sum = 1 := by
  intro t r h
  cases t with
  | node x cs =>
    cases x with
    | inl a => rw [extractC_inl] at h; obtain rfl := Option.some.inj h; simp [traceLeaf]
    | inr b => rw [extractC_inr] at h; exact absurd h (by simp)


/-! ### UnorderedTree descent -/

variable {α β : Type*}

/-- Traces are conserved by the nonplanar Δ^c cuts up to one per cut, since each contraction
    adds exactly one `Sum.inr` leaf to the trunk. -/
theorem cutSummandsCN_traceLeafCount (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.traceLeafCount).sum + p.2.traceLeafCount =
        T.traceLeafCount + Multiset.card p.1 := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := ConnesKreimer.cutSummandsG_traceLeafCount _
    (ConnesKreimer.extractC_traceLeafCount_sum_one (τ ∘ UnorderedTree.mk)) T₀ q hq
  show ((q.1.map UnorderedTree.mk).map UnorderedTree.traceLeafCount).sum +
      (UnorderedTree.mk q.2).traceLeafCount =
    (UnorderedTree.mk T₀).traceLeafCount + Multiset.card (q.1.map UnorderedTree.mk)
  rw [UnorderedTree.traceLeafCount_mk, UnorderedTree.traceLeafCount_mk, Multiset.card_map,
      Multiset.map_map,
      show q.1.map (UnorderedTree.traceLeafCount ∘ UnorderedTree.mk) =
          q.1.map RoseTree.traceLeafCount from
        Multiset.map_congr rfl (fun x _ => UnorderedTree.traceLeafCount_mk x)]
  exact hcons

/-- Vertices are conserved by the nonplanar Δ^c cuts up to traces. Crown
    vertices plus trunk vertices recover the tree vertices plus one
    replacement trace leaf per cut (MCB Lemma 1.6.3). -/
theorem cutSummandsCN_numNodes (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes =
        T.numNodes + Multiset.card p.1 := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hcons := ConnesKreimer.cutSummandsG_numNodes _
    (ConnesKreimer.extractC_numNodes_sum_one (τ ∘ UnorderedTree.mk)) T₀ q hq
  show ((q.1.map UnorderedTree.mk).map UnorderedTree.numNodes).sum +
      (UnorderedTree.mk q.2).numNodes =
    (UnorderedTree.mk T₀).numNodes + Multiset.card (q.1.map UnorderedTree.mk)
  rw [UnorderedTree.numNodes_mk, UnorderedTree.numNodes_mk, Multiset.card_map, Multiset.map_map,
      show q.1.map (UnorderedTree.numNodes ∘ UnorderedTree.mk) = q.1.map RoseTree.numNodes from
        Multiset.map_congr rfl (fun x _ => UnorderedTree.numNodes_mk x)]
  rwa [one_mul] at hcons

/-- Non-trace vertices are conserved exactly by the Δ^c cuts, since the trace leaf added at each
    cut replaces the root of the extracted subtree. Stated additively to avoid truncated subtraction. -/
theorem cutSummandsCN_lexical_conservation (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.traceLeafCount).sum + p.2.traceLeafCount + T.numNodes =
        (p.1.map UnorderedTree.numNodes).sum + p.2.numNodes + T.traceLeafCount := by
  intro p hp
  have hw := cutSummandsCN_numNodes τ T p hp
  have ht := cutSummandsCN_traceLeafCount τ T p hp
  omega

/-- The crown of a Δ^c cut has no more traces than the tree, each crown component being a subtree
    of it. -/
theorem cutSummandsCN_crown_traceLeafCount_le (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      (p.1.map UnorderedTree.traceLeafCount).sum ≤ T.traceLeafCount := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hle := ConnesKreimer.cutSummandsG_crown_traceLeafCount_le
    (ConnesKreimer.extractC (τ ∘ UnorderedTree.mk)) T₀ q hq
  show ((q.1.map UnorderedTree.mk).map UnorderedTree.traceLeafCount).sum ≤
    (UnorderedTree.mk T₀).traceLeafCount
  rw [UnorderedTree.traceLeafCount_mk, Multiset.map_map,
      show q.1.map (UnorderedTree.traceLeafCount ∘ UnorderedTree.mk) =
          q.1.map RoseTree.traceLeafCount from
        Multiset.map_congr rfl (fun x _ => UnorderedTree.traceLeafCount_mk x)]
  exact hle

/-- The trunk of a Δ^c cut has at least one trace per cut, by trace conservation and the crown
    bound. -/
theorem cutSummandsCN_trunk_traceLeafCount_ge_card (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, Multiset.card p.1 ≤ p.2.traceLeafCount := by
  intro p hp
  have hcons := cutSummandsCN_traceLeafCount τ T p hp
  have hle := cutSummandsCN_crown_traceLeafCount_le τ T p hp
  omega

/-! ### Crown components are policy-chosen (non-degeneracy substrate) -/

mutual
/-- Every crown component of a cut is one the policy chose to extract. -/
theorem cutSummandsG_crown_isSome
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t,
      ∀ Tv ∈ p.1, extract Tv ≠ none
  | .node a cs => by
    intro p hp Tv hTv
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact cutListSummandsG_crown_isSome extract cs q hq Tv hTv
theorem cutListSummandsG_crown_isSome
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (cs : List (RoseTree (α ⊕ β))), ∀ q ∈ cutListSummandsG extract cs,
      ∀ Tv ∈ q.1, extract Tv ≠ none
  | [] => by
    intro q hq Tv hTv
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    exact absurd hTv (Multiset.notMem_zero Tv)
  | t :: ts => by
    intro q hq Tv hTv
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    rcases Multiset.mem_add.mp hTv with h | h
    · exact augActionG_crown_isSome extract t pr.1 ha Tv h
    · exact cutListSummandsG_crown_isSome extract ts pr.2 hq' Tv h
theorem augActionG_crown_isSome
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ a ∈ augActionG extract t,
      ∀ Tv ∈ a.1, extract Tv ≠ none
  | t => by
    intro a ha Tv hTv
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none => rw [hex] at h; exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        obtain rfl := Multiset.mem_singleton.mp hTv
        rw [hex]; exact Option.some_ne_none r
    · obtain ⟨pp, hpp, rfl⟩ := Multiset.mem_map.mp h
      exact cutSummandsG_crown_isSome extract t pp hpp Tv hTv
end

/-- The Δ^c policy extracts only `Sum.inl`-rooted (lexical) subtrees. -/
theorem extractC_ne_none_imp_inl (τ : RoseTree (α ⊕ β) → β) (t : RoseTree (α ⊕ β))
    (h : extractC τ t ≠ none) : ∃ a cs, t = RoseTree.node (Sum.inl a) cs := by
  cases t with
  | node x cs =>
    cases x with
    | inl a => exact ⟨a, cs, rfl⟩
    | inr b => rw [extractC_inr] at h; exact absurd rfl h

/-- Crown components of a Δ^c cut are lexical-rooted, hence have strictly
    more vertices than trace leaves. -/
theorem cutSummandsCN_crown_traceLeafCount_lt_numNodes (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, ∀ Tv ∈ p.1, Tv.traceLeafCount < Tv.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp Tv hTv
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  change Tv ∈ q.1.map UnorderedTree.mk at hTv
  obtain ⟨Tv₀, hTv₀, rfl⟩ := Multiset.mem_map.mp hTv
  have hne := ConnesKreimer.cutSummandsG_crown_isSome _ T₀ q hq Tv₀ hTv₀
  obtain ⟨a, cs, rfl⟩ := ConnesKreimer.extractC_ne_none_imp_inl (τ ∘ UnorderedTree.mk) Tv₀ hne
  rw [UnorderedTree.traceLeafCount_mk, UnorderedTree.numNodes_mk]
  exact RoseTree.traceLeafCount_lt_numNodes_of_inl a cs

/-- A Δ^c cut never touches the root, so the trunk keeps the tree's root label. -/
theorem cutSummandsCN_trunk_value (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, p.2.value = T.value := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  cases T₀ with
  | node a cs =>
    rw [ConnesKreimer.cutSummandsG_node] at hq
    obtain ⟨q', hq', rfl⟩ := Multiset.mem_map.mp hq
    show (UnorderedTree.mk (RoseTree.node a q'.2)).value =
      (UnorderedTree.mk (RoseTree.node a cs)).value
    rw [UnorderedTree.value_mk, UnorderedTree.value_mk, RoseTree.value_node,
        RoseTree.value_node]

/-- Under nonempty-replacement extraction, a cut with a nonempty crown leaves a trunk with at least
    two vertices, the root and a replacement. -/
private theorem two_le_numNodes_of_mem_cutSummandsG
    (extract : RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β))))
    (hne : ∀ t r, extract t = some r → r ≠ []) :
    ∀ (t : RoseTree (α ⊕ β)), ∀ p ∈ cutSummandsG extract t, p.1 ≠ 0 → 2 ≤ p.2.numNodes
  | .node a [], p, hp, h => by
    simp only [cutSummandsG_node, cutListSummandsG_nil, Multiset.map_singleton,
      Multiset.mem_singleton] at hp
    exact (h (congrArg Prod.fst hp)).elim
  | .node a (c :: cs), p, hp, _ => by
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil
      (cutListSummandsG_remainder_ne_nil extract hne c cs q hq)
    have := d.numNodes_pos
    simp only [hd, RoseTree.numNodes_node, List.map_cons, List.sum_cons]
    omega

/-- A Δ^c cut with a nonempty crown leaves a trunk with at least two vertices, the root and a
    trace. -/
theorem cutSummandsCN_two_le_trunk_numNodes (τ : UnorderedTree (α ⊕ β) → β)
    (T : UnorderedTree (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T, p.1 ≠ 0 → 2 ≤ p.2.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = UnorderedTree.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp h
  rw [cutSummandsCN_mk, ConnesKreimer.cutSummandsCP_def] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have hne : ∀ t r, extractC (τ ∘ UnorderedTree.mk) t = some r → r ≠ [] := fun t r hr ↦
    ne_nil_of_traceLeafCount_sum_one r (extractC_traceLeafCount_sum_one _ t r hr)
  show 2 ≤ (UnorderedTree.mk q.2).numNodes
  rw [UnorderedTree.numNodes_mk]
  exact two_le_numNodes_of_mem_cutSummandsG _ hne T₀ q hq fun h0 ↦ h (by simp [projSummand, h0])

/-- A nonempty crown of a Δ^c cut has fewer edges in total than the tree. -/
theorem cutSummandsCN_crown_numEdges_lt (τ : UnorderedTree (α ⊕ β) → β)
    {T : UnorderedTree (α ⊕ β)} {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)}
    (hp : p ∈ cutSummandsCN τ T) (h : p.1 ≠ 0) :
    (p.1.map UnorderedTree.numEdges).sum < T.numEdges := by
  have hw := cutSummandsCN_numEdges τ T p hp
  have := cutSummandsCN_two_le_trunk_numNodes τ T p hp h
  have := T.numEdges_add_one
  omega

end ConnesKreimer
