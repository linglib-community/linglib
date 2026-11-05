/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.CutReplace

/-!
# Cuts that leave traces

Marcolli, Chomsky and Berwick's coproduct `Δ^c` cuts accessible terms out of a syntactic object
and leaves a trace in place of each. On trees labelled `α ⊕ β`, the trace of a cut subtree `t` is
a leaf `inr (τ t)` whose label is computed by a trace encoder `τ`, and cuts at trace leaves are
forbidden, since a trace is not an accessible term. This is the admissible-cut enumeration
`cutSummandsG` at the extraction policy `extractC τ`.

## Main definitions

* `ConnesKreimer.traceLeaf`: the trace leaf with a given label.
* `ConnesKreimer.extractC`: the trace extraction policy.
* `ConnesKreimer.cutSummandsCN`: the trace cut summands on `UnorderedTree`.

## Main results

* `ConnesKreimer.cutSummandsCN_filter_empty`: the empty cut is the unique cut with empty crown.
* `ConnesKreimer.cutSummandsCN_filter_crown_eq_singleton`: a lexical subtree occurring once is
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
def extractC (τ : RoseTree (α ⊕ β) → β) :
    RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))
  | t@(.node (Sum.inl _) _) => some [traceLeaf (τ t)]
  | .node (Sum.inr _) _ => none

@[simp] theorem extractC_inl (τ : RoseTree (α ⊕ β) → β)
    (a : α) (cs : List (RoseTree (α ⊕ β))) :
    extractC τ (RoseTree.node (Sum.inl a) cs) =
      some [traceLeaf (τ (RoseTree.node (Sum.inl a) cs))] := rfl

@[simp] theorem extractC_inr (τ : RoseTree (α ⊕ β) → β)
    (b : β) (cs : List (RoseTree (α ⊕ β))) :
    extractC τ (RoseTree.node (Sum.inr b) cs) = none := rfl

/-! ### Descent to `UnorderedTree` -/

/-- The Δ^c extract policy is `ExtractInvariant`, since it reads only the root label and `τ` of
    the unordered tree. -/
theorem extractC_mkComp_invariant (τ : UnorderedTree (α ⊕ β) → β) :
    ExtractInvariant (extractC (τ ∘ UnorderedTree.mk)) := by
  rintro ⟨a, cs⟩ ⟨b, ds⟩ hmk
  obtain rfl : a = b := (UnorderedTree.mk_eq_mk_iff.mp hmk).value_eq
  cases a with
  | inl a => simp [hmk]
  | inr b => rfl

/-- The Δ^c cut summands on `UnorderedTree`: the cuts at the policy `extractC`, which descend along
    `RoseTree.Perm` since the policy is invariant. -/
noncomputable def cutSummandsCN (τ : UnorderedTree (α ⊕ β) → β) :
    UnorderedTree (α ⊕ β) → Multiset (Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)) :=
  Quotient.lift (fun T ↦ (cutSummandsG (extractC (τ ∘ UnorderedTree.mk)) T).map projSummand)
    fun _ _ h ↦ cutSummandsG_proj_perm (extractC_mkComp_invariant τ) h

@[simp] theorem cutSummandsCN_mk (τ : UnorderedTree (α ⊕ β) → β) (T : RoseTree (α ⊕ β)) :
    cutSummandsCN τ (UnorderedTree.mk T) =
      (cutSummandsG (extractC (τ ∘ UnorderedTree.mk)) T).map projSummand := rfl

/-- The empty cut `(0, T)` is the unique cut summand of `cutSummandsCN τ T` with empty crown. -/
theorem cutSummandsCN_filter_empty
    (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    (cutSummandsCN τ T).filter (fun p ↦ p.1.card = 0) =
      ({((0 : Multiset (UnorderedTree (α ⊕ β))), T)} : Multiset _) := by
  induction T using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk, Multiset.filter_map,
      Multiset.filter_congr (q := fun q : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) ↦
        q.1.card = 0) fun q _ ↦ by simp [projSummand],
      cutSummandsG_filter_empty, Multiset.map_singleton]
    rfl

/-- The empty cut is a trace cut. -/
theorem zero_mem_cutSummandsCN (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree (α ⊕ β)) :
    ((0 : Multiset (UnorderedTree (α ⊕ β))), T) ∈ cutSummandsCN τ T :=
  Multiset.mem_of_mem_filter (p := fun p ↦ Multiset.card p.1 = 0) <| by
    rw [cutSummandsCN_filter_empty]
    exact Multiset.mem_singleton_self _

/-- Every crown component of a Δ^c cut of `T` is a subtree of `T`. -/
theorem cutSummandsCN_mem_subtrees_of_mem_crown (τ : UnorderedTree (α ⊕ β) → β)
    {T : UnorderedTree (α ⊕ β)} {p : Multiset (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β)}
    (hp : p ∈ cutSummandsCN τ T) {x : UnorderedTree (α ⊕ β)} (hx : x ∈ p.1) :
    x ∈ T.subtrees := by
  induction T using Quotient.inductionOn with
  | h t =>
    obtain ⟨a, cs⟩ := t
    rw [UnorderedTree.quot_mk_eq_mk, cutSummandsCN_mk] at hp
    rw [UnorderedTree.quot_mk_eq_mk, subtrees_mk, unorderedSubtrees]
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact Multiset.mem_cons_of_mem (mk_mem_of_mem_crown_cutSummandsG _ _ q hq y hy)

/-- A lexical subtree `M` occurring exactly once below the root of `T` is extracted by exactly one
    Δ^c cut, whose trunk is `T` with `M` replaced by its trace. -/
theorem cutSummandsCN_filter_crown_eq_singleton [DecidableEq α] [DecidableEq β]
    (τ : UnorderedTree (α ⊕ β) → β) {M T : UnorderedTree (α ⊕ β)} (hM : M.value.isLeft)
    (hcount : T.subtrees.count M = 1) (hTM : T ≠ M) :
    (cutSummandsCN τ T).filter (fun p ↦ p.1 = {M})
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
        extractC (τ ∘ UnorderedTree.mk) s = some [ρ] ∧
          UnorderedTree.mk ρ = UnorderedTree.leaf (Sum.inr (τ M)) := by
      rintro ⟨x, ds⟩ rfl
      obtain ⟨y, rfl⟩ := Sum.isLeft_iff.mp hM
      exact ⟨traceLeaf (τ (UnorderedTree.mk (.node (Sum.inl y) ds))), rfl, rfl⟩
    have key := map_trunk_filter_cutSummandsG (extractC (τ ∘ UnorderedTree.mk)) hE
      (.node a cs) hlist hTM
    rw [cutSummandsCN_mk, Multiset.filter_map, replace_mk,
      ← Multiset.map_singleton (fun t ↦ (({M} : Multiset (UnorderedTree (α ⊕ β))), t)), ← key,
      Multiset.map_map]
    exact Multiset.map_congr (Multiset.filter_congr fun _ _ ↦ Iff.rfl)
      fun q hq ↦ Prod.ext (Multiset.mem_filter.mp hq).2 rfl

end ConnesKreimer
