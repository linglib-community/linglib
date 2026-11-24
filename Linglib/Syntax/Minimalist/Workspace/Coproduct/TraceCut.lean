/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.CutReplace
public import Linglib.Core.Combinatorics.RootedTree.DoubleCut

/-!
# Cuts that leave traces

Marcolli, Chomsky and Berwick's coproduct `Δ^c` cuts accessible terms out of a syntactic object
and leaves a trace in place of each. On trees labelled `α ⊕ β`, the trace of a cut subtree `t` is
a leaf `inr (τ t)` whose label is computed by a trace encoder `τ`, and cuts at trace leaves are
forbidden, since a trace is not an accessible term. This is the admissible-cut enumeration
`rootCuts` at the extraction policy `leaveTrace τ`.

## Main definitions

* `ConnesKreimer.traceLeaf`: the trace leaf with a given label.
* `ConnesKreimer.leaveTrace`: the trace extraction policy.
* `ConnesKreimer.traceCuts`: the trace cuts on `UnorderedTree`.

## Main results

* `ConnesKreimer.traceCuts_filter_empty`: the empty cut is the unique cut with empty crown.
* `ConnesKreimer.traceCuts_filter_crown_eq_singleton`: a lexical subtree occurring once is
  extracted by one cut, whose trunk replaces it by its trace.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α β : Type*}

/-! ### `traceLeaf` — placeholder for a cut subtree -/

/-- The trace-marker placeholder leaf carrying the encoded label `b : β`. -/
def traceLeaf (b : β) : RoseTree (α ⊕ β) := .node (Sum.inr b) []

/-! ### Δ^c extraction policy -/

/-- The Δ^c extraction policy cuts a `Sum.inl`-rooted subtree `t` whole, leaving the trace leaf
    `traceLeaf (τ t)` in its slot, and never cuts a trace, which is not an accessible term
    ([marcolli-chomsky-berwick-2025], proof of Lemma 1.6.3, p. 65). Cutting traces would also
    break coassociativity, since iterated Δ^c would then leave traces of traces. -/
def leaveTrace (τ : RoseTree (α ⊕ β) → β) :
    RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))
  | t@(.node (Sum.inl _) _) => some [traceLeaf (τ t)]
  | .node (Sum.inr _) _ => none

@[simp] theorem leaveTrace_inl (τ : RoseTree (α ⊕ β) → β)
    (a : α) (cs : List (RoseTree (α ⊕ β))) :
    leaveTrace τ (RoseTree.node (Sum.inl a) cs) =
      some [traceLeaf (τ (RoseTree.node (Sum.inl a) cs))] := rfl

@[simp] theorem leaveTrace_inr (τ : RoseTree (α ⊕ β) → β)
    (b : β) (cs : List (RoseTree (α ⊕ β))) :
    leaveTrace τ (RoseTree.node (Sum.inr b) cs) = none := rfl

/-- The Δ^c policy is coherent when cutting inside a tree keeps the marker `τ` gives it: a trace
leaf has no cuts, and a trunk has the root label of the tree it was cut from. -/
theorem extractCoherent_leaveTrace {τ : RoseTree (α ⊕ β) → β}
    (hτ : ∀ t, ∀ p ∈ rootCuts (leaveTrace τ) t, τ p.2 = τ t) : ExtractCoherent (leaveTrace τ) where
  childrenCuts_of_eq_some := by
    rintro ⟨a | b, cs⟩ r h
    · obtain rfl : [traceLeaf _] = r := Option.some.inj h
      rw [childrenCuts_singleton, traceLeaf, childCuts_eq_none _ _ (leaveTrace_inr τ _ []),
        rootCuts_node, childrenCuts_nil]
      rfl
    · cases h
  extract_trunk := by
    rintro ⟨a | b, cs⟩ p hp
    · have := hτ _ p hp
      rw [rootCuts_node] at hp
      obtain ⟨q, -, rfl⟩ := Multiset.mem_map.1 hp
      rw [leaveTrace_inl, leaveTrace_inl, this]
    · rw [rootCuts_node] at hp
      obtain ⟨q, -, rfl⟩ := Multiset.mem_map.1 hp
      rfl

/-! ### Descent to `UnorderedTree` -/

/-- The Δ^c extract policy is `ExtractInvariant`, since it reads only the root label and `τ` of
    the unordered tree. -/
theorem leaveTrace_mkComp_invariant (τ : UnorderedTree (α ⊕ β) → β) :
    ExtractInvariant (leaveTrace (τ ∘ UnorderedTree.mk)) := by
  rintro ⟨a, cs⟩ ⟨b, ds⟩ hmk
  obtain rfl : a = b := (UnorderedTree.mk_eq_mk_iff.mp hmk).value_eq
  cases a with
  | inl a => simp [hmk]
  | inr b => rfl

/-- The Δ^c cuts on `UnorderedTree`: the cuts at the policy `leaveTrace`, which descend
    along `RoseTree.Perm` since the policy is invariant. -/
noncomputable def traceCuts (τ : UnorderedTree (α ⊕ β) → β) :
    UnorderedTree (α ⊕ β) → Multiset (Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)) :=
  Quotient.lift (fun T ↦ (rootCuts (leaveTrace (τ ∘ UnorderedTree.mk)) T).map projCut)
    fun _ _ h ↦ rootCuts_proj_perm (leaveTrace_mkComp_invariant τ) h

@[simp] theorem traceCuts_mk (τ : UnorderedTree (α ⊕ β) → β) (T : RoseTree (α ⊕ β)) :
    traceCuts τ (UnorderedTree.mk T) =
      (rootCuts (leaveTrace (τ ∘ UnorderedTree.mk)) T).map projCut := rfl

/-- The empty cut `(0, T)` is the unique cut of `traceCuts τ T` with empty crown. -/
theorem traceCuts_filter_empty
    (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    (traceCuts τ T).filter (fun p ↦ p.1.card = 0) =
      ({((0 : Multiset (UnorderedTree (α ⊕ β))), T)} : Multiset _) := by
  induction T using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, traceCuts_mk, Multiset.filter_map,
      Multiset.filter_congr (q := fun q : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) ↦
        q.1.card = 0) fun q _ ↦ by simp [projCut],
      rootCuts_filter_empty, Multiset.map_singleton]
    rfl

/-- The empty cut is a trace cut. -/
theorem zero_mem_traceCuts (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    ((0 : Multiset (UnorderedTree (α ⊕ β))), T) ∈ traceCuts τ T :=
  Multiset.mem_of_mem_filter (p := fun p ↦ Multiset.card p.1 = 0) <| by
    rw [traceCuts_filter_empty]
    exact Multiset.mem_singleton_self _

/-- Every crown component of a Δ^c cut of `T` is a subtree of `T`. -/
theorem traceCuts_mem_subtrees_of_mem_crown (τ : UnorderedTree (α ⊕ β) → β)
    {T : UnorderedTree (α ⊕ β)} {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)}
    (hp : p ∈ traceCuts τ T) {x : UnorderedTree (α ⊕ β)} (hx : x ∈ p.1) :
    x ∈ T.subtrees := by
  induction T using Quotient.inductionOn with
  | h t =>
    obtain ⟨a, cs⟩ := t
    rw [UnorderedTree.quot_mk_eq_mk, traceCuts_mk] at hp
    rw [UnorderedTree.quot_mk_eq_mk, subtrees_mk, unorderedSubtrees]
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact Multiset.mem_cons_of_mem (mk_mem_of_mem_crown_rootCuts _ _ q hq y hy)

/-- The trunk of a Δ^c cut of a tree licensed by `R` is licensed by `R`, when `R` reads only the
    number of children and licenses a trace leaf: a cut child leaves one trace leaf in its slot. -/
theorem _root_.RoseTree.Licensed.of_mem_rootCuts_leaveTrace {R : α ⊕ β → List (α ⊕ β) → Prop}
    (hR : ∀ a ks ls, ks.length = ls.length → R a ks → R a ls) (hleaf : ∀ b, R (Sum.inr b) [])
    (τ : RoseTree (α ⊕ β) → β) {t : RoseTree (α ⊕ β)} (ht : t.Licensed R)
    {p : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β)} (hp : p ∈ rootCuts (leaveTrace τ) t) :
    p.2.Licensed R := by
  refine ((rootCuts_induction (leaveTrace τ)
    (P := fun cs q ↦ (∀ c ∈ cs, c.Licensed R) →
      (∀ c ∈ q.2, c.Licensed R) ∧ q.2.length = cs.length) ?_ ?_ ?_ ?_ t p hp)
    fun c hc ↦ List.mem_singleton.1 hc ▸ ht).1 p.2 (List.mem_singleton_self _)
  · exact fun _ ↦ ⟨by simp, rfl⟩
  · rintro ⟨a | b, cs⟩ r hr -
    · obtain rfl : [traceLeaf _] = r := Option.some.inj hr
      refine ⟨fun c hc ↦ ?_, rfl⟩
      rw [List.mem_singleton.1 hc]
      exact licensed_node_iff.2 ⟨hleaf _, by simp⟩
    · cases hr
  · intro a cs q _ ih h
    have hn := h _ (List.mem_singleton_self _)
    obtain ⟨hq, hlen⟩ := ih fun c hc ↦ hn.of_mem hc
    refine ⟨fun c hc ↦ ?_, rfl⟩
    rw [List.mem_singleton.1 hc]
    exact licensed_node_iff.2 ⟨hR a _ _ (by simp [hlen]) hn.rel_root, hq⟩
  · intro t ts a b _ _ iha ihb h
    obtain ⟨ha, hla⟩ := iha fun c hc ↦ h c (List.mem_singleton.1 hc ▸ List.mem_cons_self)
    obtain ⟨hb, hlb⟩ := ihb fun c hc ↦ h c (List.mem_cons_of_mem _ hc)
    exact ⟨fun c hc ↦ (List.mem_append.1 hc).elim (ha c) (hb c), by simp [hla, hlb, add_comm]⟩

/-- The trunk of a Δ^c cut of an unordered tree licensed by `R` is licensed by `R`, when `R` reads
    only the number of children and licenses a trace leaf. -/
theorem _root_.UnorderedTree.Licensed.of_mem_traceCuts {R : α ⊕ β → Multiset (α ⊕ β) → Prop}
    (hR : ∀ a ks ls, Multiset.card ks = Multiset.card ls → R a ks → R a ls)
    (hleaf : ∀ b, R (Sum.inr b) 0) (τ : UnorderedTree (α ⊕ β) → β) {T : UnorderedTree (α ⊕ β)}
    (hT : T.Licensed R) {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)}
    (hp : p ∈ traceCuts τ T) : p.2.Licensed R := by
  induction T using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, traceCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact RoseTree.Licensed.of_mem_rootCuts_leaveTrace
      (R := fun a (ks : List (α ⊕ β)) ↦ R a (ks : Multiset (α ⊕ β)))
      (fun a ks ls h ↦ hR a _ _ (by simpa using h)) hleaf _ hT hq

/-- A lexical subtree `M` occurring exactly once below the root of `T` is extracted by exactly one
    Δ^c cut, whose trunk is `T` with `M` replaced by its trace. -/
theorem traceCuts_filter_crown_eq_singleton [DecidableEq α] [DecidableEq β]
    (τ : UnorderedTree (α ⊕ β) → β) {M T : UnorderedTree (α ⊕ β)} (hM : M.value.isLeft)
    (hcount : T.subtrees.count M = 1) (hTM : T ≠ M) :
    (traceCuts τ T).filter (fun p ↦ p.1 = {M})
      = {({M}, UnorderedTree.replace M (UnorderedTree.leaf (Sum.inr (τ M))) T)} := by
  induction T using Quotient.inductionOn with
  | h t =>
    obtain ⟨a, cs⟩ := t
    rw [UnorderedTree.quot_mk_eq_mk] at hcount hTM ⊢
    have hlist : (unorderedSubtreesList cs).count M = 1 := by
      rw [subtrees_mk, unorderedSubtrees, Multiset.count_cons, ite_eq_right (Ne.symm hTM),
        add_zero] at hcount
      exact hcount
    have hE : ∀ s, UnorderedTree.mk s = M → ∃ ρ,
        leaveTrace (τ ∘ UnorderedTree.mk) s = some [ρ] ∧
          UnorderedTree.mk ρ = UnorderedTree.leaf (Sum.inr (τ M)) := by
      rintro ⟨x, ds⟩ rfl
      obtain ⟨y, rfl⟩ := Sum.isLeft_iff.mp hM
      exact ⟨traceLeaf (τ (UnorderedTree.mk (.node (Sum.inl y) ds))), rfl, rfl⟩
    have key := map_trunk_filter_rootCuts (leaveTrace (τ ∘ UnorderedTree.mk)) hE
      (.node a cs) hlist hTM
    rw [traceCuts_mk, Multiset.filter_map, replace_mk,
      ← Multiset.map_singleton (fun t ↦ (({M} : Multiset (UnorderedTree (α ⊕ β))), t)), ← key,
      Multiset.map_map]
    exact Multiset.map_congr (Multiset.filter_congr fun _ _ ↦ Iff.rfl)
      fun q hq ↦ Prod.ext (Multiset.mem_filter.mp hq).2 rfl

end ConnesKreimer
