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
workspace, the book's operator at the deletion coproduct (`mergeOp_node`) and Merge at the trace
cuts (`traceMergeOp_node`).

Internal Merge goes through the trace cuts. The trace of an extracted term is a label of the leaf it
contracts to ([marcolli-chomsky-berwick-2025] Definition 1.2.4), here compressed to a token by a
trace encoder: a moved object leaves the trace of its head under the encoder (`headTrace`), by
default the head by selection (`traceEncoder`). A uniquely accessible mover is extracted by exactly
one trace cut, whose trunk is the remainder `deleteAccessible mover current`
(`traceCuts_filter_mover`), and Internal Merge is the composition `M_{T/β,β} ∘ M_{β,1}` of
[marcolli-chomsky-berwick-2025] Proposition 1.4.2 (`traceMergeOp_im`).

The admissible cuts cannot carry Internal Merge on syntactic objects. A syntactic object is a full
binary tree, so it has an odd number of vertices (`numNodes_odd`); an admissible cut removing one
syntactic object conserves vertices, so it leaves an even number, and the remainder is never a
syntactic object (`not_isSyntacticObject_of_mem_admissibleCuts`): the mover's parent is left unary.
The deletion contracts that vertex, so the remainder of a deletion extracting one syntactic object
is one (`isSyntacticObject_contractUnary_of_mem_admissibleCuts`), and the book's Merge carries
Internal Merge from a syntactic object to a syntactic object (`mergeOp_im`). A syntactic object is
its own remainder (`deletionQuotient_of_isSyntacticObject`), the bare label marking exactly its
vertices with children.

## Main definitions

* `Minimalist.SyntacticObject.traceEncoder`

## Main results

* `Minimalist.SyntacticObject.mergeOp_node`, `traceMergeOp_node`: External Merge on the carrier.
* `Minimalist.SyntacticObject.traceCuts_filter_mover`: the trace cut extracting a uniquely
  accessible mover leaves `deleteAccessible`.
* `Minimalist.SyntacticObject.traceMergeOpUnit_current`, `traceMergeOp_im`: Internal Merge on the
  carrier.
* `Minimalist.SyntacticObject.traceMergeOp_node_residual`, `traceMergeOp_im_residual`: both beside a
  spectator workspace.
* `Minimalist.SyntacticObject.traceMergeOp_of'_merge`: on External Merge the Merge operator computes
  MERGE (`Workspace.merge`).
* `traceMergeOp_im_of'_merge`, `traceMergeOp_sideward2b_of'_merge`,
  `traceMergeOp_sideward3b_of'_merge`: on Internal Merge and Sideward Merge of types 2(b) and 3(b)
  it computes MERGE leaving traces (`Workspace.mergeWith`).
* `Minimalist.SyntacticObject.numNodes_odd`: a syntactic object has an odd number of vertices.
* `Minimalist.SyntacticObject.not_isSyntacticObject_of_mem_admissibleCuts`: no admissible cut
  removing one syntactic object from another leaves a syntactic object.
* `Minimalist.SyntacticObject.isSyntacticObject_contractUnary_of_mem_admissibleCuts`,
  `Minimalist.SyntacticObject.mergeOp_im`: the remainder of a deletion removing at most one tree
  is a syntactic object, and Internal Merge at the deletion coproduct yields one.

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

/-- In a syntactic object the bare label marks exactly the vertices with children, and those
    have two. -/
theorem licensed_bare_of_isSyntacticObject {t : UnorderedTree Vertex} (h : IsSyntacticObject t) :
    t.Licensed fun a ks ↦ (a = Vertex.bare ↔ ks ≠ 0) ∧
      (Multiset.card ks = 0 ∨ Multiset.card ks = 2) :=
  UnorderedTree.Licensed.mono (R := Vertex.Licenses) (fun a ks h ↦ by
    match a, h with
    | .inl (some _), h | .inr _, h =>
      have hk : ks = 0 := h
      simp [hk]
    | .inl none, h =>
      have hk : Multiset.card ks = 2 := h
      refine ⟨⟨fun _ hz ↦ ?_, fun _ ↦ rfl⟩, .inr hk⟩
      simp [hz] at hk) h

/-- A syntactic object is its own remainder under deletion. -/
theorem deletionQuotient_of_isSyntacticObject {t : UnorderedTree Vertex}
    (h : IsSyntacticObject t) : deletionQuotient Vertex.bare t = some t :=
  deletionQuotient_eq_self _
    (ne_of_mem_leaves _ ((licensed_bare_of_isSyntacticObject h).mono fun _ _ h ↦ h.1))
    h.isFullBinary.numUnary_eq_zero

/-- External Merge on the carrier is the algebraic Merge with the bare root label on the
    two-object workspace. -/
theorem mergeOp_node (S S' : SyntacticObject) :
    Merge.mergeOp (R := ℤ) Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (of' ({S.toUnorderedTree, S'.toUnorderedTree} : Forest (UnorderedTree Vertex)))
      = of' (R := ℤ) ({(merge S S').toUnorderedTree} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOp_pair Vertex.bare
      (deletionQuotient_of_isSyntacticObject S.isSyntacticObject_toUnorderedTree)
      (deletionQuotient_of_isSyntacticObject S'.isSyntacticObject_toUnorderedTree),
    toUnorderedTree_merge]

/-- External Merge on the carrier is the trace-cut Merge with the bare root label on the
    two-object workspace, for any trace encoder. -/
theorem traceMergeOp_node (τ : UnorderedTree Vertex → Option LexicalItem.Token)
    (S S' : SyntacticObject) :
    Merge.traceMergeOp (R := ℤ) τ Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (of' ({S.toUnorderedTree, S'.toUnorderedTree} : Forest (UnorderedTree Vertex)))
      = of' (R := ℤ) ({(merge S S').toUnorderedTree} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.traceMergeOp_pair, toUnorderedTree_merge]

/-! ### Internal Merge through the trace cuts -/

/-- The trace encoder of derivations sends a tree to its head by selection. -/
def traceEncoder (t : UnorderedTree Vertex) : Option LexicalItem.Token := (selCheckN t).head

@[simp] theorem traceEncoder_toUnorderedTree (s : SyntacticObject) :
    traceEncoder s.toUnorderedTree = s.selHead := by
  rw [traceEncoder, selCheckN_toUnorderedTree]; rfl

variable {mover current : SyntacticObject}

/-- A uniquely accessible mover that is not a trace is extracted by exactly one trace cut, whose
    trunk is the remainder `deleteAccessible mover current`. -/
theorem traceCuts_filter_mover (hm : mover.toUnorderedTree.value.isLeft)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    (traceCuts traceEncoder current.toUnorderedTree).filter (fun p ↦ p.1 = {mover.toUnorderedTree})
      = {({mover.toUnorderedTree}, (deleteAccessible mover current).toUnorderedTree)} := by
  rw [toUnorderedTree_deleteAccessible, toUnorderedTree_headTrace,
    ← traceEncoder_toUnorderedTree]
  refine traceCuts_filter_crown_eq_singleton traceEncoder hm ?_
    (fun h' ↦ hne (toUnorderedTree_injective h'))
  rw [← map_toUnorderedTree_terms, Multiset.count_map_eq_count' _ _ toUnorderedTree_injective, h]

/-- The unit stage `M_{β,1}` on the current object splits off a uniquely accessible mover beside
    the remainder. -/
theorem traceMergeOpUnit_current (hm : mover.toUnorderedTree.value.isLeft) (h : current.terms.count
    mover = 1)
    (hne : current ≠ mover) :
    Merge.traceMergeOpUnit (R := ℤ) traceEncoder mover.toUnorderedTree
        (of' ({current.toUnorderedTree} : Forest (UnorderedTree Vertex)))
      = of' ({mover.toUnorderedTree, (deleteAccessible mover current).toUnorderedTree} :
          Forest (UnorderedTree Vertex)) := by
  rw [Merge.traceMergeOpUnit, Merge.mergeOpUnitOfCuts_apply_singleton_unique _ _ _
      (traceCuts_filter_mover hm h hne) (fun h' ↦ hne (toUnorderedTree_injective h')),
    ← of'_singleton, ← of'_add]
  rfl

/-- Internal Merge of a uniquely accessible mover is the composition `M_{T/β,β} ∘ M_{β,1}` of
    trace-cut Merges ([marcolli-chomsky-berwick-2025] Proposition 1.4.2). -/
theorem traceMergeOp_im (hm : mover.toUnorderedTree.value.isLeft) (h : current.terms.count mover =
    1)
    (hne : current ≠ mover) :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover
        current).toUnorderedTree
        mover.toUnorderedTree (Merge.traceMergeOpUnit traceEncoder mover.toUnorderedTree
          (of' ({current.toUnorderedTree} : Forest (UnorderedTree Vertex))))
      = of' (R := ℤ) ({(merge (deleteAccessible mover current) mover).toUnorderedTree} :
          Forest (UnorderedTree Vertex)) := by
  rw [Merge.traceMergeOp_im_composition traceEncoder Vertex.bare _ _ _ _
      (traceCuts_filter_mover hm h hne) rfl (fun h' ↦ hne (toUnorderedTree_injective
          h')), toUnorderedTree_merge]

/-! ### Merge beside a spectator workspace -/

private theorem disjoint_pair_subtrees {S S' U : SyntacticObject}
    (h : S ∉ U.terms ∧ S' ∉ U.terms) :
    Disjoint ({S.toUnorderedTree, S'.toUnorderedTree} : Forest (UnorderedTree
        Vertex)) U.toUnorderedTree.subtrees := by
  rw [Multiset.disjoint_left]
  intro a ha
  rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> rw [toUnorderedTree_mem_subtrees]
  exacts [h.1, h.2]

/-- External Merge on the carrier beside a spectator workspace none of whose components contains
    `S` or `S'`. -/
theorem traceMergeOp_node_residual (τ : UnorderedTree Vertex → Option LexicalItem.Token)
    (S S' : SyntacticObject) {W : Workspace} (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.traceMergeOp (R := ℤ) τ Vertex.bare S.toUnorderedTree S'.toUnorderedTree (of' (({S, S'} +
        W).map toUnorderedTree))
      = of' (({merge S S'} + W).map toUnorderedTree) := by
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_singleton, toUnorderedTree_merge]
  refine Merge.traceMergeOp_pair_residual τ Vertex.bare fun U hU ↦ ?_
  obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
  exact disjoint_pair_subtrees (hW U' hU')

/-- Internal Merge of a uniquely accessible mover beside a spectator workspace none of whose
    components contains the mover or the remainder. -/
theorem traceMergeOp_im_residual (hm : mover.toUnorderedTree.value.isLeft) (h : current.terms.count
    mover = 1)
    (hne : current ≠ mover) {W : Workspace}
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover
        current).toUnorderedTree
        mover.toUnorderedTree (Merge.traceMergeOpUnit traceEncoder mover.toUnorderedTree
          (of' (({current} + W).map toUnorderedTree)))
      = of' (({merge (deleteAccessible mover current) mover} + W).map toUnorderedTree) := by
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_singleton, Multiset.map_singleton,
    toUnorderedTree_merge]
  refine Merge.mergeOpOfCuts_im_composition_residual Vertex.bare _ _ _ _
    (traceCuts_filter_mover hm h hne) rfl (fun h' ↦ hne (toUnorderedTree_injective h')) fun U hU ↦
        ?_
  obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
  exact disjoint_pair_subtrees (hW U' hU')

/-! ### MERGE computed by the Merge operator -/

/-- External Merge: the Merge operator at the trace cuts computes MERGE on a workspace of which `S`
    and `S'` are members, when no other member contains them. -/
theorem traceMergeOp_of'_merge (τ : UnorderedTree Vertex → Option LexicalItem.Token)
    {S S' : SyntacticObject} {W : Workspace} (hle : {S, S'} ≤ W)
    (hW : ∀ U ∈ W - {S, S'}, S ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.traceMergeOp (R := ℤ) τ Vertex.bare S.toUnorderedTree S'.toUnorderedTree (of' (W.map
        toUnorderedTree))
      = of' ((W.merge S S').map toUnorderedTree) := by
  conv_lhs => rw [← add_tsub_cancel_of_le hle]
  rw [traceMergeOp_node_residual τ S S' hW, Workspace.merge_def, add_comm]

/-- Internal Merge ([marcolli-chomsky-berwick-2025] Proposition 1.4.2): the Merge operator at the
    trace cuts computes MERGE of a uniquely accessible mover with the member containing it, leaving
    the trace of its head. -/
theorem traceMergeOp_im_of'_merge (hm : mover.toUnorderedTree.value.isLeft) (h : current.terms.count
    mover = 1)
    (hne : current ≠ mover) {W : Workspace}
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare (deleteAccessible mover
        current).toUnorderedTree
        mover.toUnorderedTree (Merge.traceMergeOpUnit traceEncoder mover.toUnorderedTree
          (of' (({current} + W).map toUnorderedTree)))
      = of' ((({current} + W).mergeWith (·.headTrace) mover current).map toUnorderedTree) := by
  rw [traceMergeOp_im_residual hm h hne hW, Workspace.mergeWith_internal
    (Multiset.count_pos.1 (by omega)) hne fun U hU ↦ (hW U hU).2, add_comm W, merge_comm]
  rfl

/-- Sideward Merge of type 2(b) ([marcolli-chomsky-berwick-2025] Lemma 1.4.4): merging a member `T`
    with the only occurrence of a term `S'` of another member `T'`, the Merge operator at the trace
    cuts computes MERGE leaving the trace of the head of `S'` in `T'`, when `S'` is no term of `T`.
    -/
theorem traceMergeOp_sideward2b_of'_merge {T T' S' : SyntacticObject} {W : Workspace}
    (hS' : S'.toUnorderedTree.value.isLeft) (hc : T'.terms.count S' = 1) (hne : T' ≠ S') (hT : T ∉
        T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, T ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare T.toUnorderedTree S'.toUnorderedTree
        (of' (({T, T'} + W).map toUnorderedTree))
      = of' ((({T, T'} + W).mergeWith (·.headTrace) T S').map toUnorderedTree) := by
  have hout : ({T, T'} + W).mergeWith (·.headTrace) T S' =
      W + {merge T S'} + {deleteAccessible S' T'} := by
    rw [Workspace.mergeWith_sideward_member (Multiset.count_pos.1 (by omega)) hne hT hS'T hW,
      add_comm {_} W, add_right_comm]
    rfl
  have hval : T.toUnorderedTree ∉ T'.toUnorderedTree.subtrees := by
      rwa [toUnorderedTree_mem_subtrees]
  have hne' : S'.toUnorderedTree ≠ T'.toUnorderedTree := fun h ↦ hne (toUnorderedTree_injective
      h).symm
  rw [hout, Merge.traceMergeOp, Multiset.map_add, of'_add, mul_comm,
    Merge.mergeOpOfCuts_of'_mul _ fun U hU ↦ by
      obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
      exact disjoint_pair_subtrees (hW U' hU'),
    Multiset.map_add, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    ← Multiset.insert_eq_cons, Merge.mergeOpOfCuts_sideward_2b Vertex.bare hval hne',
    traceCuts_filter_mover hS' hc hne]
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, of'_add,
    of'_singleton, toUnorderedTree_merge]
  ring

/-- Sideward Merge of type 3(b) ([marcolli-chomsky-berwick-2025] Lemma 1.4.4): merging the only
    occurrences of a term `S` of a member `T` and a term `S'` of another member `T'`, the Merge
    operator at the trace cuts computes MERGE leaving the traces of their heads. -/
theorem traceMergeOp_sideward3b_of'_merge {T T' S S' : SyntacticObject} {W : Workspace}
    (hS : S.toUnorderedTree.value.isLeft) (hS' : S'.toUnorderedTree.value.isLeft) (hcS :
        T.terms.count S = 1)
    (hcS' : T'.terms.count S' = 1) (hneS : T ≠ S) (hneS' : T' ≠ S') (hST' : S ∉ T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (of' (({T, T'} + W).map toUnorderedTree))
      = of' ((({T, T'} + W).mergeWith (·.headTrace) S S').map toUnorderedTree) := by
  have hout : ({T, T'} + W).mergeWith (·.headTrace) S S' =
      W + {merge S S'} + {deleteAccessible S T, deleteAccessible S' T'} := by
    rw [Workspace.mergeWith_sideward (Multiset.count_pos.1 (by omega))
      (Multiset.count_pos.1 (by omega)) hneS hneS' hST' hS'T hW, add_comm {_, _} W,
      add_right_comm]
    rfl
  have hvS : S.toUnorderedTree ∉ T'.toUnorderedTree.subtrees := by
      rwa [toUnorderedTree_mem_subtrees]
  have hvS' : S'.toUnorderedTree ∉ T.toUnorderedTree.subtrees := by
      rwa [toUnorderedTree_mem_subtrees]
  rw [hout, Merge.traceMergeOp, Multiset.map_add, of'_add, mul_comm,
    Merge.mergeOpOfCuts_of'_mul _ fun U hU ↦ by
      obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
      exact disjoint_pair_subtrees (hW U' hU'),
    Multiset.map_add, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    ← Multiset.insert_eq_cons, Merge.mergeOpOfCuts_sideward_3b Vertex.bare
      (fun h ↦ hneS (toUnorderedTree_injective h).symm) (fun h ↦ hneS' (toUnorderedTree_injective
          h).symm) hvS hvS',
    traceCuts_filter_mover hS hcS hneS, traceCuts_filter_mover hS' hcS' hneS']
  simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, of'_add,
    of'_singleton, toUnorderedTree_merge, Multiset.insert_eq_cons, Multiset.map_cons, of'_cons]
  ring

private def demoTok (i : ℕ) : LexicalItem.Token := ⟨.of .N [], i⟩

private def demoCurrent : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf (demoTok 0))
    (.leaf (demoTok 1))).toSyntacticObject

/-- Raising one daughter of a two-leaf object meets the hypotheses of `traceMergeOp_im`. -/
example :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare
        (deleteAccessible (leaf (demoTok 0)) demoCurrent).toUnorderedTree (leaf (demoTok
            0)).toUnorderedTree
        (Merge.traceMergeOpUnit traceEncoder (leaf (demoTok 0)).toUnorderedTree
          (of' ({demoCurrent.toUnorderedTree} : Forest (UnorderedTree Vertex))))
      = of' (R := ℤ) ({(merge (deleteAccessible (leaf (demoTok 0)) demoCurrent)
          (leaf (demoTok 0))).toUnorderedTree} : Forest (UnorderedTree Vertex)) :=
  traceMergeOp_im (by decide) (by decide) (by decide)

/-! ### The admissible cuts on syntactic objects -/

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
theorem numNodes_odd (s : SyntacticObject) : Odd s.toUnorderedTree.numNodes := by
  have ht := s.isSyntacticObject_toUnorderedTree
  generalize s.toUnorderedTree = t at ht
  induction t using Quotient.inductionOn with
  | h t => exact odd_numNodes_of_isSyntacticObject ht

/-- An admissible cut removing one syntactic object from another leaves no syntactic object, since
    the remainder has an even number of vertices. -/
theorem not_isSyntacticObject_of_mem_admissibleCuts {T mover : SyntacticObject}
    {p : Forest (UnorderedTree Vertex) × UnorderedTree Vertex} (hp : p ∈ admissibleCuts
        T.toUnorderedTree)
    (hcrown : p.1 = {mover.toUnorderedTree}) : ¬ IsSyntacticObject p.2 := fun h ↦ by
  have hw := admissibleCuts_numNodes T.toUnorderedTree p hp
  rw [hcrown, Multiset.map_singleton, Multiset.sum_singleton] at hw
  obtain ⟨a, ha⟩ := numNodes_odd mover
  obtain ⟨b, hb⟩ := numNodes_odd (ofUnorderedTree p.2 h)
  obtain ⟨c, hc⟩ := numNodes_odd T
  rw [toUnorderedTree_ofUnorderedTree] at hb
  omega

/-- A tree whose bare vertices have one or two children and whose other vertices have none
    contracts to a syntactic object. -/
private theorem licensed_contractUnary {t : RoseTree Vertex}
    (ht : t.Licensed fun a ks ↦ Vertex.Licenses a (ks : Multiset Vertex) ∨
      (a = Vertex.bare ∧ ks.length = 1)) :
    t.contractUnary.Licensed fun a ks ↦ Vertex.Licenses a (ks : Multiset Vertex) := by
  induction t with
  | node a cs ih =>
    obtain ⟨hr, hcs⟩ := RoseTree.licensed_node_iff.mp ht
    rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
    · rw [RoseTree.contractUnary_leaf]
      exact RoseTree.licensed_node_iff.mpr ⟨hr.resolve_right fun h ↦ absurd h.2 (by simp),
        by simp⟩
    · rw [RoseTree.contractUnary_node_singleton]
      exact ih c (List.mem_singleton_self c) (hcs c (List.mem_singleton_self c))
    · rw [RoseTree.contractUnary_node_cons₂]
      refine RoseTree.licensed_node_iff.mpr ⟨?_, fun x hx ↦ ?_⟩
      · exact (Vertex.licenses_iff_of_card_eq (by simp)).1
          (hr.resolve_right fun h ↦ absurd h.2 (by simp))
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact ih y hy (hcs y hy)

/-- An admissible cut extracting at most one tree from a syntactic object leaves a tree whose bare
    vertices have one or two children and whose other vertices have none. -/
private theorem licensed_of_mem_rootCuts_leaveNothing {t : RoseTree Vertex}
    (ht : t.Licensed fun a ks ↦ Vertex.Licenses a (ks : Multiset Vertex))
    {p : Multiset (RoseTree Vertex) × RoseTree Vertex} (hp : p ∈ rootCuts leaveNothing t)
    (hcard : Multiset.card p.1 ≤ 1) :
    p.2.Licensed fun a ks ↦ Vertex.Licenses a (ks : Multiset Vertex) ∨
      (a = Vertex.bare ∧ ks.length = 1) := by
  have key := rootCuts_induction leaveNothing
    (P := fun cs q ↦ (∀ c ∈ cs, c.Licensed fun a ks ↦ Vertex.Licenses a (ks : Multiset Vertex)) →
      Multiset.card q.1 ≤ 1 →
        (∀ r ∈ q.2, r.Licensed fun a ks ↦ Vertex.Licenses a (ks : Multiset Vertex) ∨
          (a = Vertex.bare ∧ ks.length = 1)) ∧
        cs.length ≤ q.2.length + Multiset.card q.1 ∧ q.2.length ≤ cs.length)
    (fun _ _ ↦ ⟨by simp, by simp, by simp⟩)
    (fun _ _ h _ _ ↦ by cases h; exact ⟨by simp, by simp, by simp⟩)
    (fun a cs q _ hP hL hq ↦ by
      have hroot := (hL _ (List.mem_singleton_self _)).rel_root
      obtain ⟨h1, h2, h3⟩ := hP (fun c hc ↦ (hL _ (List.mem_singleton_self _)).of_mem hc) hq
      refine ⟨fun r hr ↦ ?_, by simp, by simp⟩
      rw [List.mem_singleton.mp hr]
      refine RoseTree.licensed_node_iff.mpr ⟨?_, h1⟩
      dsimp only at hq
      rcases a with (_ | x) | x
      · simp only [Vertex.Licenses, Multiset.coe_card, List.length_map] at hroot ⊢
        simp only [true_and]
        omega
      · simp only [Vertex.Licenses, Multiset.coe_eq_zero, List.map_eq_nil_iff] at hroot ⊢
        subst hroot
        exact .inl (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h3))
      · simp only [Vertex.Licenses, Multiset.coe_eq_zero, List.map_eq_nil_iff] at hroot ⊢
        subst hroot
        exact .inl (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h3)))
    (fun t ts a b _ _ ha hb hL hq ↦ by
      dsimp only at hq ⊢
      rw [Multiset.card_add] at hq
      obtain ⟨ha1, ha2, ha3⟩ := ha (fun c hc ↦ hL c (by simp_all)) (by omega)
      obtain ⟨hb1, hb2, hb3⟩ := hb (fun c hc ↦ hL c (List.mem_cons_of_mem _ hc)) (by omega)
      refine ⟨fun r hr ↦ (List.mem_append.mp hr).elim (ha1 r) (hb1 r), ?_, ?_⟩ <;>
        simp only [List.length_cons, List.length_nil, List.length_append,
          Multiset.card_add] at ha2 ha3 ⊢ <;> omega)
    t p hp
  exact (key (fun c hc ↦ List.mem_singleton.mp hc ▸ ht) hcard).1 _ (List.mem_singleton_self _)

/-- An admissible cut extracting at most one tree from a syntactic object leaves a syntactic
    object once the vertex the extraction leaves unary is contracted. -/
theorem isSyntacticObject_contractUnary_of_mem_admissibleCuts {T : SyntacticObject}
    {q : Forest (UnorderedTree Vertex) × UnorderedTree Vertex}
    (hq : q ∈ admissibleCuts T.toUnorderedTree) (hcard : Multiset.card q.1 ≤ 1) :
    IsSyntacticObject q.2.contractUnary := by
  have ht := T.isSyntacticObject_toUnorderedTree
  generalize T.toUnorderedTree = t at ht hq
  induction t using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, isSyntacticObject_mk] at ht
    rw [UnorderedTree.quot_mk_eq_mk, admissibleCuts_mk] at hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    simp only [projCut, Multiset.card_map] at hcard ⊢
    rw [UnorderedTree.contractUnary_mk, isSyntacticObject_mk]
    exact licensed_contractUnary (licensed_of_mem_rootCuts_leaveNothing ht hr hcard)

/-- Internal Merge at the deletion coproduct carries a syntactic object to a syntactic object:
    when one admissible cut extracts the mover, the remainder of its trunk is a syntactic object
    `Q`, and the composition `M_{Q,β} ∘ M_{β,1}` of Proposition 1.4.2 yields the one object
    `merge Q mover`. -/
theorem mergeOp_im {current mover : SyntacticObject}
    {p0 : Forest (UnorderedTree Vertex) × UnorderedTree Vertex}
    (h : (admissibleCuts current.toUnorderedTree).filter
        (fun p ↦ p.1 = {mover.toUnorderedTree}) = {p0})
    (hne : current ≠ mover) :
    ∃ Q : SyntacticObject, Q.toUnorderedTree = p0.2.contractUnary ∧
      Merge.mergeOp (R := ℤ) Vertex.bare Q.toUnorderedTree mover.toUnorderedTree
          (Merge.mergeOpUnit Vertex.bare mover.toUnorderedTree
            (of' ({current.toUnorderedTree} : Forest (UnorderedTree Vertex)))) =
        of' ({(merge Q mover).toUnorderedTree} : Forest (UnorderedTree Vertex)) := by
  obtain ⟨hp0, hcrown⟩ := Multiset.mem_filter.mp (h ▸ Multiset.mem_singleton_self p0)
  have hcard : Multiset.card p0.1 ≤ 1 := by rw [hcrown, Multiset.card_singleton]
  have hQ := isSyntacticObject_contractUnary_of_mem_admissibleCuts hp0 hcard
  have hrem : deletionQuotient Vertex.bare p0.2 = some p0.2.contractUnary := by
    rw [deletionQuotient, admissibleCuts_prune_eq_some _
      (licensed_bare_of_isSyntacticObject current.isSyntacticObject_toUnorderedTree) hp0 hcard,
      Option.map_some]
  refine ⟨ofUnorderedTree _ hQ, toUnorderedTree_ofUnorderedTree _ _, ?_⟩
  rw [toUnorderedTree_ofUnorderedTree, Merge.mergeOp_im_composition Vertex.bare
      mover.toUnorderedTree current.toUnorderedTree p0.2.contractUnary p0 h hrem
      (fun h' ↦ hne (toUnorderedTree_injective h'))
      (deletionQuotient_of_isSyntacticObject mover.isSyntacticObject_toUnorderedTree)
      (deletionQuotient_of_isSyntacticObject hQ),
    toUnorderedTree_merge, toUnorderedTree_ofUnorderedTree]

end Minimalist.SyntacticObject
