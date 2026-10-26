/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Merge.Internal
public import Linglib.Syntax.Minimalist.Workspace.Merge.Sideward
public import Linglib.Syntax.Minimalist.Workspace.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Replace
public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Core.Combinatorics.RootedTree.Conservation

/-!
# Merge on the syntactic-object carrier

Merge on the carrier is the bare binary node `SyntacticObject.merge` with root label
`Vertex.bare`. External Merge of two objects is the algebraic Merge operator on the two-object
workspace, at the pruning cuts (`mergeOp_node`) and at the trace cuts (`mergeOpC_node`).

Internal Merge goes through the trace cuts. The trace of an extracted term is a label of the leaf it
contracts to ([marcolli-chomsky-berwick-2025] Definition 1.2.4), here compressed to a token by a
trace encoder: a moved object leaves the trace of its head under the encoder (`headTrace`), by
default the head by selection (`traceEncoder`). A uniquely accessible mover is extracted by exactly
one trace cut, whose trunk is the remainder `deleteAccessible mover current`
(`cutSummandsCN_filter_mover`), and Internal Merge is the composition `M_{T/β,β} ∘ M_{β,1}` of
[marcolli-chomsky-berwick-2025] Proposition 1.4.2 (`mergeOpC_im`).

The pruning cuts cannot carry Internal Merge on syntactic objects. A syntactic object is a full
binary tree, so it has an odd number of vertices (`numNodes_odd`); a pruning cut removing one
syntactic object conserves vertices, so it leaves an even number, and the remainder is never a
syntactic object (`not_isSyntacticObject_of_mem_cutSummandsN`): the mover's parent is left unary.

## Main definitions

* `Minimalist.SyntacticObject.traceEncoder`

## Main results

* `Minimalist.SyntacticObject.mergeOp_node`, `mergeOpC_node`: External Merge on the carrier.
* `Minimalist.SyntacticObject.cutSummandsCN_filter_mover`: the trace cut extracting a uniquely
  accessible mover leaves `deleteAccessible`.
* `Minimalist.SyntacticObject.mergeOpUnitC_current`, `mergeOpC_im`: Internal Merge on the carrier.
* `Minimalist.SyntacticObject.mergeOpC_node_residual`, `mergeOpC_im_residual`: both beside a
  spectator workspace.
* `Minimalist.SyntacticObject.mergeOpC_of'_merge`: on External Merge the Merge operator computes
  MERGE (`Workspace.merge`).
* `mergeOpC_im_of'_merge`, `mergeOpC_sideward2b_of'_merge`, `mergeOpC_sideward3b_of'_merge`: on
  Internal Merge and Sideward Merge of types 2(b) and 3(b) it computes MERGE leaving traces
  (`Workspace.mergeWith`).
* `Minimalist.SyntacticObject.numNodes_odd`: a syntactic object has an odd number of vertices.
* `Minimalist.SyntacticObject.not_isSyntacticObject_of_mem_cutSummandsN`: no pruning cut removing
  one syntactic object from another leaves a syntactic object.

## TODO

* Sideward Merge of type 3(a), two terms of one member, needs the uniqueness of the cut whose
  crown is both terms. Where one target contains the other, as in Countercyclic Merge, no
  admissible cut has the pair as its crown, so the operator should vanish there.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open RoseTree UnorderedTree ConnesKreimer

/-- External Merge on the carrier is the algebraic Merge with the bare root label on the
    two-object workspace. -/
theorem mergeOp_node (S S' : SyntacticObject) :
    Merge.mergeOp (R := ℤ) Vertex.bare S.val S'.val
        (of' ({S.val, S'.val} : Forest (UnorderedTree Vertex)))
      = of' (R := ℤ) ({(merge S S').val} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOp_pair, merge_val]

/-- External Merge on the carrier is the trace-cut Merge with the bare root label on the
    two-object workspace, for any trace encoder. -/
theorem mergeOpC_node (τ : UnorderedTree Vertex → Option LexicalItem.Token)
    (S S' : SyntacticObject) :
    Merge.mergeOpC (R := ℤ) τ Vertex.bare S.val S'.val
        (of' ({S.val, S'.val} : Forest (UnorderedTree Vertex)))
      = of' (R := ℤ) ({(merge S S').val} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpC_pair, merge_val]

/-! ### Internal Merge through the trace cuts -/

/-- The trace encoder of derivations sends a tree to its head by selection. -/
def traceEncoder (t : UnorderedTree Vertex) : Option LexicalItem.Token := (selCheckN t).head

variable {mover current : SyntacticObject}

/-- A uniquely accessible mover that is not a trace is extracted by exactly one trace cut, whose
    trunk is the remainder `deleteAccessible mover current`. -/
theorem cutSummandsCN_filter_mover (hm : mover.val.value.isLeft)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    (cutSummandsCN traceEncoder current.val).filter (fun p ↦ p.1 = {mover.val})
      = {({mover.val}, (deleteAccessible mover current).val)} := by
  rw [deleteAccessible_val, headTrace_val]
  refine cutSummandsCN_filter_crown_eq_singleton traceEncoder hm ?_
    (fun h' ↦ hne (Subtype.ext h'))
  rw [← map_val_terms, Multiset.count_map_eq_count' _ _ Subtype.val_injective, h]

/-- The unit stage `M_{β,1}` on the current object splits off a uniquely accessible mover beside
    the remainder. -/
theorem mergeOpUnitC_current (hm : mover.val.value.isLeft) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) :
    Merge.mergeOpUnitC (R := ℤ) traceEncoder mover.val
        (of' ({current.val} : Forest (UnorderedTree Vertex)))
      = of' ({mover.val, (deleteAccessible mover current).val} :
          Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpUnitC, Merge.mergeOpUnitG_apply_singleton_unique _ _ _
      (cutSummandsCN_filter_mover hm h hne) (fun h' ↦ hne (Subtype.ext h')),
    ← of'_singleton, ← of'_add]
  rfl

/-- Internal Merge of a uniquely accessible mover is the composition `M_{T/β,β} ∘ M_{β,1}` of
    trace-cut Merges ([marcolli-chomsky-berwick-2025] Proposition 1.4.2). -/
theorem mergeOpC_im (hm : mover.val.value.isLeft) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover current).val
        mover.val (Merge.mergeOpUnitC traceEncoder mover.val
          (of' ({current.val} : Forest (UnorderedTree Vertex))))
      = of' (R := ℤ) ({(merge (deleteAccessible mover current) mover).val} :
          Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpC_im_composition traceEncoder Vertex.bare _ _ _ _
      (cutSummandsCN_filter_mover hm h hne) rfl (fun h' ↦ hne (Subtype.ext h')), merge_val]

/-! ### Merge beside a spectator workspace -/

private theorem disjoint_pair_subtrees {S S' U : SyntacticObject}
    (h : S ∉ U.terms ∧ S' ∉ U.terms) :
    Disjoint ({S.val, S'.val} : Forest (UnorderedTree Vertex)) U.val.subtrees := by
  rw [Multiset.disjoint_left]
  intro a ha
  rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> rw [val_mem_subtrees]
  exacts [h.1, h.2]

/-- External Merge on the carrier beside a spectator workspace none of whose components contains
    `S` or `S'`. -/
theorem mergeOpC_node_residual (τ : UnorderedTree Vertex → Option LexicalItem.Token)
    (S S' : SyntacticObject) {W : Workspace} (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.mergeOpC (R := ℤ) τ Vertex.bare S.val S'.val (of' (({S, S'} + W).map Subtype.val))
      = of' (({merge S S'} + W).map Subtype.val) := by
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_singleton, merge_val]
  refine Merge.mergeOpC_pair_residual τ Vertex.bare fun U hU ↦ ?_
  obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
  exact disjoint_pair_subtrees (hW U' hU')

/-- Internal Merge of a uniquely accessible mover beside a spectator workspace none of whose
    components contains the mover or the remainder. -/
theorem mergeOpC_im_residual (hm : mover.val.value.isLeft) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) {W : Workspace}
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover current).val
        mover.val (Merge.mergeOpUnitC traceEncoder mover.val
          (of' (({current} + W).map Subtype.val)))
      = of' (({merge (deleteAccessible mover current) mover} + W).map Subtype.val) := by
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_singleton, Multiset.map_singleton,
    merge_val]
  refine Merge.mergeOpG_im_composition_residual Vertex.bare _ _ _ _
    (cutSummandsCN_filter_mover hm h hne) rfl (fun h' ↦ hne (Subtype.ext h')) fun U hU ↦ ?_
  obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
  exact disjoint_pair_subtrees (hW U' hU')

/-! ### MERGE computed by the Merge operator -/

/-- External Merge: the Merge operator at the trace cuts computes MERGE on a workspace of which `S`
    and `S'` are members, when no other member contains them. -/
theorem mergeOpC_of'_merge (τ : UnorderedTree Vertex → Option LexicalItem.Token)
    {S S' : SyntacticObject} {W : Workspace} (hle : {S, S'} ≤ W)
    (hW : ∀ U ∈ W - {S, S'}, S ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.mergeOpC (R := ℤ) τ Vertex.bare S.val S'.val (of' (W.map Subtype.val))
      = of' ((W.merge S S').map Subtype.val) := by
  conv_lhs => rw [← add_tsub_cancel_of_le hle]
  rw [mergeOpC_node_residual τ S S' hW, Workspace.merge_def, add_comm]

/-- Internal Merge ([marcolli-chomsky-berwick-2025] Proposition 1.4.2): the Merge operator at the
    trace cuts computes MERGE of a uniquely accessible mover with the member containing it, leaving
    the trace of its head. -/
theorem mergeOpC_im_of'_merge (hm : mover.val.value.isLeft) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) {W : Workspace}
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover current).val
        mover.val (Merge.mergeOpUnitC traceEncoder mover.val
          (of' (({current} + W).map Subtype.val)))
      = of' ((({current} + W).mergeWith (·.headTrace) mover current).map Subtype.val) := by
  rw [mergeOpC_im_residual hm h hne hW, Workspace.mergeWith_internal
    (Multiset.count_pos.1 (by omega)) hne fun U hU ↦ (hW U hU).2, add_comm W, merge_comm]
  rfl

/-- Sideward Merge of type 2(b) ([marcolli-chomsky-berwick-2025] Lemma 1.4.4): merging a member `T`
    with the only occurrence of a term `S'` of another member `T'`, the Merge operator at the trace
    cuts computes MERGE leaving the trace of the head of `S'` in `T'`, when `S'` is no term of `T`.
    -/
theorem mergeOpC_sideward2b_of'_merge {T T' S' : SyntacticObject} {W : Workspace}
    (hS' : S'.val.value.isLeft) (hc : T'.terms.count S' = 1) (hne : T' ≠ S') (hT : T ∉ T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, T ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare T.val S'.val
        (of' (({T, T'} + W).map Subtype.val))
      = of' ((({T, T'} + W).mergeWith (·.headTrace) T S').map Subtype.val) := by
  have hout : ({T, T'} + W).mergeWith (·.headTrace) T S' =
      W + {merge T S'} + {deleteAccessible S' T'} := by
    rw [Workspace.mergeWith_sideward_member (Multiset.count_pos.1 (by omega)) hne hT hS'T hW,
      add_comm {_} W, add_right_comm]
    rfl
  have hval : T.val ∉ T'.val.subtrees := by rwa [val_mem_subtrees]
  have hne' : S'.val ≠ T'.val := fun h ↦ hne (Subtype.ext h).symm
  rw [hout, Merge.mergeOpC, Multiset.map_add, of'_add, mul_comm,
    Merge.mergeOpG_of'_mul _ fun U hU ↦ by
      obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
      exact disjoint_pair_subtrees (hW U' hU'),
    Multiset.map_add, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    ← Multiset.insert_eq_cons, Merge.mergeOpG_sideward_2b Vertex.bare hval hne',
    cutSummandsCN_filter_mover hS' hc hne]
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, of'_add,
    of'_singleton, merge_val]
  ring

/-- Sideward Merge of type 3(b) ([marcolli-chomsky-berwick-2025] Lemma 1.4.4): merging the only
    occurrences of a term `S` of a member `T` and a term `S'` of another member `T'`, the Merge
    operator at the trace cuts computes MERGE leaving the traces of their heads. -/
theorem mergeOpC_sideward3b_of'_merge {T T' S S' : SyntacticObject} {W : Workspace}
    (hS : S.val.value.isLeft) (hS' : S'.val.value.isLeft) (hcS : T.terms.count S = 1)
    (hcS' : T'.terms.count S' = 1) (hneS : T ≠ S) (hneS' : T' ≠ S') (hST' : S ∉ T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare S.val S'.val
        (of' (({T, T'} + W).map Subtype.val))
      = of' ((({T, T'} + W).mergeWith (·.headTrace) S S').map Subtype.val) := by
  have hout : ({T, T'} + W).mergeWith (·.headTrace) S S' =
      W + {merge S S'} + {deleteAccessible S T, deleteAccessible S' T'} := by
    rw [Workspace.mergeWith_sideward (Multiset.count_pos.1 (by omega))
      (Multiset.count_pos.1 (by omega)) hneS hneS' hST' hS'T hW, add_comm {_, _} W,
      add_right_comm]
    rfl
  have hvS : S.val ∉ T'.val.subtrees := by rwa [val_mem_subtrees]
  have hvS' : S'.val ∉ T.val.subtrees := by rwa [val_mem_subtrees]
  rw [hout, Merge.mergeOpC, Multiset.map_add, of'_add, mul_comm,
    Merge.mergeOpG_of'_mul _ fun U hU ↦ by
      obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
      exact disjoint_pair_subtrees (hW U' hU'),
    Multiset.map_add, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    ← Multiset.insert_eq_cons, Merge.mergeOpG_sideward_3b Vertex.bare
      (fun h ↦ hneS (Subtype.ext h).symm) (fun h ↦ hneS' (Subtype.ext h).symm) hvS hvS',
    cutSummandsCN_filter_mover hS hcS hneS, cutSummandsCN_filter_mover hS' hcS' hneS']
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, of'_add,
    of'_singleton, merge_val, Multiset.insert_eq_cons, Multiset.map_cons, of'_cons]
  ring

private def demoTok (i : ℕ) : LexicalItem.Token := ⟨.of .N [], i⟩

private def demoCurrent : SyntacticObject :=
  (LinearizedSyntacticObject.merge (.leaf (demoTok 0))
    (.leaf (demoTok 1))).toSyntacticObject

/-- Raising one daughter of a two-leaf object meets the hypotheses of `mergeOpC_im`. -/
example :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare
        (deleteAccessible (leaf (demoTok 0)) demoCurrent).val (leaf (demoTok 0)).val
        (Merge.mergeOpUnitC traceEncoder (leaf (demoTok 0)).val
          (of' ({demoCurrent.val} : Forest (UnorderedTree Vertex))))
      = of' (R := ℤ) ({(merge (deleteAccessible (leaf (demoTok 0)) demoCurrent)
          (leaf (demoTok 0))).val} : Forest (UnorderedTree Vertex)) :=
  mergeOpC_im (by decide) (by decide) (by decide)

/-! ### The pruning cuts on syntactic objects -/

private theorem odd_numNodes_of_isSyntacticObject {t : RoseTree Vertex}
    (h : IsSyntacticObject (UnorderedTree.mk t)) : Odd t.numNodes := by
  induction t with
  | node a cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · obtain rfl := List.length_eq_zero_iff.mp hlen
      simp
    · obtain ⟨l, r, rfl⟩ := List.length_eq_two.mp hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge l r).mp h
      obtain ⟨x, hx⟩ := ih l (by simp) hl
      obtain ⟨y, hy⟩ := ih r (by simp) hr
      simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      exact ⟨x + y + 1, by omega⟩

/-- A syntactic object, being a full binary tree, has an odd number of vertices. -/
theorem numNodes_odd (s : SyntacticObject) : Odd s.val.numNodes := by
  obtain ⟨t, ht⟩ := s
  induction t using Quotient.inductionOn with
  | h t => exact odd_numNodes_of_isSyntacticObject ht

/-- A pruning cut removing one syntactic object from another leaves no syntactic object, since
    the remainder has an even number of vertices. -/
theorem not_isSyntacticObject_of_mem_cutSummandsN {T mover : SyntacticObject}
    {p : Forest (UnorderedTree Vertex) × UnorderedTree Vertex} (hp : p ∈ cutSummandsN T.val)
    (hcrown : p.1 = {mover.val}) : ¬ IsSyntacticObject p.2 := fun h ↦ by
  have hw := cutSummandsN_numNodes T.val p hp
  rw [hcrown, Multiset.map_singleton, Multiset.sum_singleton] at hw
  obtain ⟨a, ha⟩ := numNodes_odd mover
  obtain ⟨b, hb⟩ := numNodes_odd ⟨p.2, h⟩
  obtain ⟨c, hc⟩ := numNodes_odd T
  simp only at hb
  omega

end Minimalist.SyntacticObject
