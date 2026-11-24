/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Merge.SyntacticObject

/-!
# The algebra of workspaces

The algebra `ConnesKreimer R SyntacticObject` has the workspaces as a basis and disjoint union as
product: it is the free commutative algebra on the syntactic objects, Marcolli, Chomsky and
Berwick's `V(𝔉_{SO₀})`. The tree of an object embeds it in the algebra of forests of labelled
unordered trees, where the coproducts are defined, by the injective algebra homomorphism
`Workspace.toTrees`.

A cut of a syntactic object that leaves a trace in place of each extracted term extracts
syntactic objects and leaves a syntactic object, so the trace cuts are an enumeration
`SyntacticObject.cuts` on the objects themselves, and Merge at the trace cuts is an operator
`Workspace.mergeOp S S'` on the algebra of workspaces: on a workspace `W` it is the sum, over the
cuts of `W` that extract `S` and `S'`, of the workspace with `{S, S'}` beside what the cut
leaves. The homomorphism `toTrees` intertwines it with `Merge.traceMergeOp`, and the forms of Merge
are stated on workspaces.

## Main definitions

* `Minimalist.Workspace.toTrees`: the algebra of workspaces in the algebra of forests of trees.
* `Minimalist.SyntacticObject.cuts`: the trace cuts of a syntactic object.
* `Minimalist.Workspace.mergeOp`, `Minimalist.Workspace.mergeOpUnit`: Merge `M_{S,S'}` and its
  unit stage `M_{S,1}` on the algebra of workspaces.

## Main results

* `Minimalist.IsSyntacticObject.of_mem_markerCuts`: a trace cut of a syntactic object leaves a
  syntactic object.
* `Minimalist.Workspace.toTrees_injective`
* `Minimalist.Workspace.toTrees_mergeOp`, `Minimalist.Workspace.toTrees_mergeOpUnit`: `toTrees`
  intertwines Merge on workspaces with Merge at the trace cuts.
* `Minimalist.Workspace.mergeOp_of'`: External Merge is MERGE.
* `Minimalist.Workspace.mergeOp_mergeOpUnit_of'_singleton`,
  `Minimalist.Workspace.mergeOp_mergeOpUnit_of'`: Internal Merge is the composition
  `M_{T/β,β} ∘ M_{β,1}`, and it is MERGE leaving the trace of the mover's head.
* `Minimalist.Workspace.mergeOp_of'_sideward_member`, `Minimalist.Workspace.mergeOp_of'_sideward`:
  Sideward Merge of types 2(b) and 3(b).

## Implementation notes

The operators are defined on the basis of workspaces by the formula that
`Merge.mergeOpOfCuts_apply_of'` proves of the operator on trees, over the cuts of syntactic
objects, and not as the restriction of the operator on trees to the range of `toTrees`: a
restriction needs the range to be stable before the operator can be named, while the formula
makes stability the theorem `toTrees_mergeOp`. Merge at the deletion coproduct also preserves
workspaces, and Merge at the admissible cuts does not, a remainder there having a unary vertex.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree ConnesKreimer SyntacticObject

/-- A trace cut of a syntactic object leaves a syntactic object. -/
theorem IsSyntacticObject.of_mem_markerCuts
    (τ : UnorderedTree Vertex → Option LexicalItem.Token) {T : UnorderedTree Vertex}
    (hT : IsSyntacticObject T) {p : Forest (UnorderedTree Vertex) × UnorderedTree Vertex}
    (hp : p ∈ markerCuts τ T) : IsSyntacticObject p.2 :=
  UnorderedTree.Licensed.of_mem_markerCuts (R := Vertex.Licenses)
    (fun _ _ _ h ↦ (Vertex.licenses_iff_of_card_eq h).1)
    (fun b ↦ show Vertex.Licenses (Sum.inr b) 0 from rfl) τ hT hp

namespace SyntacticObject

/-- The trace cuts of a syntactic object, as pairs of the workspace of extracted terms and the
object that remains, with the trace of the head of each extracted term in its place. -/
noncomputable def cuts (S : SyntacticObject) : Multiset (Workspace × SyntacticObject) :=
  (markerCuts traceEncoder S.toUnorderedTree).attach.map fun p ↦
    (p.1.1.attach.map fun t ↦ ofUnorderedTree t.1 (isSyntacticObject_of_mem_subtrees S t.1
        (markerCuts_mem_subtrees_of_mem_crown traceEncoder p.2 t.2)),
      ofUnorderedTree p.1.2
        (.of_mem_markerCuts traceEncoder S.isSyntacticObject_toUnorderedTree p.2))

theorem map_cuts (S : SyntacticObject) :
    S.cuts.map (Prod.map (Multiset.map toUnorderedTree) toUnorderedTree) =
      markerCuts traceEncoder S.toUnorderedTree := by
  rw [cuts, Multiset.map_map]
  refine (Multiset.map_congr rfl fun p _ ↦ ?_).trans (Multiset.attach_map_val _)
  refine Prod.ext ?_ (toUnorderedTree_ofUnorderedTree _ _)
  simp only [Function.comp_apply, Prod.map_fst, Multiset.map_map, toUnorderedTree_ofUnorderedTree]
  exact Multiset.attach_map_val _

end SyntacticObject

namespace Workspace

variable {R : Type*} [CommSemiring R]

/-- The algebra of workspaces in the algebra of forests of labelled unordered trees, each
syntactic object going to its tree. -/
noncomputable def toTrees :
    ConnesKreimer R SyntacticObject →ₐ[R] ConnesKreimer R (UnorderedTree Vertex) :=
  rename toUnorderedTree

@[simp] theorem toTrees_of' (W : Workspace) :
    toTrees (R := R) (of' W) = of' (W.map toUnorderedTree) :=
  rename_of' _ _

@[simp] theorem toTrees_ofTree (S : SyntacticObject) :
    toTrees (R := R) (ofTree S) = ofTree S.toUnorderedTree :=
  rename_ofTree _ _

theorem toTrees_injective :
    Function.Injective (toTrees : ConnesKreimer R SyntacticObject → _) :=
  rename_injective toUnorderedTree_injective

/-- Merge `M_{S,S'}` on the algebra of workspaces: on a workspace `W`, the sum over the cuts of
`W` that extract `S` and `S'` of the workspace with `{S, S'}` beside what the cut leaves. -/
noncomputable def mergeOp (S S' : SyntacticObject) :
    ConnesKreimer R SyntacticObject →ₗ[R] ConnesKreimer R SyntacticObject :=
  linearLift fun W ↦ (((forestCuts SyntacticObject.cuts W).filter (·.1 = {S, S'})).map
    fun p ↦ of' ({SyntacticObject.merge S S'} + p.2)).sum

/-- The unit stage `M_{S,1}` on the algebra of workspaces: on a workspace `W`, the sum over the
cuts of `W` that extract `S` of the workspace with `S` beside what the cut leaves. -/
noncomputable def mergeOpUnit (S : SyntacticObject) :
    ConnesKreimer R SyntacticObject →ₗ[R] ConnesKreimer R SyntacticObject :=
  linearLift fun W ↦ (((forestCuts SyntacticObject.cuts W).filter (·.1 = {S})).map
    fun p ↦ of' ({S} + p.2)).sum

private theorem forestCuts_map_toUnorderedTree (W : Workspace) :
    forestCuts (markerCuts traceEncoder) (W.map toUnorderedTree) =
      (forestCuts SyntacticObject.cuts W).map
        (Prod.map (Multiset.map toUnorderedTree) (Multiset.map toUnorderedTree)) :=
  forestCuts_map (fun S ↦ (map_cuts S).symm) W

private theorem map_toUnorderedTree_eq_iff {V W : Workspace} :
    V.map toUnorderedTree = W.map toUnorderedTree ↔ V = W :=
  (Multiset.map_injective toUnorderedTree_injective).eq_iff

theorem toTrees_mergeOp_of' (S S' : SyntacticObject) (W : Workspace) :
    toTrees (mergeOp (R := R) S S' (of' W)) =
      Merge.traceMergeOp traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (of' (W.map toUnorderedTree)) := by
  have hpair : ({S.toUnorderedTree, S'.toUnorderedTree} : Multiset (UnorderedTree Vertex)) =
      Multiset.map toUnorderedTree {S, S'} := rfl
  rw [Merge.traceMergeOp, Merge.mergeOpOfCuts_apply_of', forestCuts_map_toUnorderedTree,
    Multiset.filter_map, Multiset.map_map, mergeOp, linearLift_of', map_multiset_sum,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, hpair, map_toUnorderedTree_eq_iff,
    toTrees_of', Multiset.map_singleton, toUnorderedTree_merge, of'_add, map_mul]

theorem toTrees_mergeOpUnit_of' (S : SyntacticObject) (W : Workspace) :
    toTrees (mergeOpUnit (R := R) S (of' W)) =
      Merge.traceMergeOpUnit traceEncoder S.toUnorderedTree (of' (W.map toUnorderedTree)) := by
  have hone : ({S.toUnorderedTree} : Multiset (UnorderedTree Vertex)) =
      Multiset.map toUnorderedTree {S} := rfl
  rw [Merge.traceMergeOpUnit, Merge.mergeOpUnitOfCuts_apply_of', forestCuts_map_toUnorderedTree,
    Multiset.filter_map, Multiset.map_map, mergeOpUnit, linearLift_of', map_multiset_sum,
    Multiset.map_map]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, hone, map_toUnorderedTree_eq_iff,
    toTrees_of', ← Multiset.map_add]

/-- `toTrees` intertwines Merge on workspaces with Merge at the trace cuts. -/
theorem toTrees_mergeOp (S S' : SyntacticObject) (x : ConnesKreimer R SyntacticObject) :
    toTrees (mergeOp S S' x) =
      Merge.traceMergeOp traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (toTrees x) :=
  LinearMap.congr_fun (lhom_ext' (f := toTrees.toLinearMap ∘ₗ mergeOp S S')
    (g := Merge.traceMergeOp traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree ∘ₗ
      toTrees.toLinearMap) fun W ↦ by
    simpa using toTrees_mergeOp_of' (R := R) S S' W) x

/-- `toTrees` intertwines the unit stage on workspaces with the unit stage at the trace cuts. -/
theorem toTrees_mergeOpUnit (S : SyntacticObject) (x : ConnesKreimer R SyntacticObject) :
    toTrees (mergeOpUnit S x) = Merge.traceMergeOpUnit traceEncoder S.toUnorderedTree (toTrees x) :=
  LinearMap.congr_fun (lhom_ext' (f := toTrees.toLinearMap ∘ₗ mergeOpUnit S)
    (g := Merge.traceMergeOpUnit traceEncoder S.toUnorderedTree ∘ₗ toTrees.toLinearMap) fun W ↦ by
    simpa using toTrees_mergeOpUnit_of' (R := R) S W) x

/-! ### The forms of Merge -/

variable {S S' T T' mover current : SyntacticObject} {W : Workspace}

/-- External Merge: Merge of two members of a workspace that no other member contains is MERGE. -/
theorem mergeOp_of' (hle : {S, S'} ≤ W) (hW : ∀ U ∈ W - {S, S'}, S ∉ U.terms ∧ S' ∉ U.terms) :
    mergeOp (R := ℤ) S S' (of' W) = of' (W.merge S S') :=
  toTrees_injective <| by
    rw [toTrees_mergeOp_of', traceMergeOp_of'_merge traceEncoder hle hW, toTrees_of']

/-- External Merge of two objects beside spectators that contain neither. -/
theorem mergeOp_of'_add (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    mergeOp (R := ℤ) S S' (of' ({S, S'} + W)) = of' ({SyntacticObject.merge S S'} + W) :=
  toTrees_injective <| by
    rw [toTrees_mergeOp_of', traceMergeOp_node_residual traceEncoder S S' hW, toTrees_of']

/-- The unit stage beside spectators that do not contain the mover splits a uniquely accessible
mover off the object containing it. -/
theorem mergeOpUnit_of'_add (hm : ¬ mover.IsTrace) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) (hW : ∀ U ∈ W, mover ∉ U.terms) :
    mergeOpUnit (R := ℤ) mover (of' ({current} + W)) =
      of' ({mover, deleteAccessible mover current} + W) :=
  toTrees_injective <| by
    rw [toTrees_mergeOpUnit_of', toTrees_of', Multiset.map_add, Multiset.map_add,
      Multiset.map_singleton, Merge.traceMergeOpUnit,
      Merge.mergeOpUnitOfCuts_apply_singleton_unique_residual _ _ _
        (markerCuts_filter_mover hm h hne) (fun h' ↦ hne (toUnorderedTree_injective h'))
        fun U hU ↦ ?_]
    · rfl
    · obtain ⟨U', hU', rfl⟩ := Multiset.mem_map.mp hU
      rw [toUnorderedTree_mem_subtrees]
      exact hW U' hU'

/-- Internal Merge of a uniquely accessible mover beside spectators that contain neither the mover
nor what it leaves. -/
theorem mergeOp_mergeOpUnit_of'_add (hm : ¬ mover.IsTrace) (h : current.terms.count mover = 1)
    (hne : current ≠ mover)
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    mergeOp (R := ℤ) (deleteAccessible mover current) mover
        (mergeOpUnit mover (of' ({current} + W))) =
      of' ({SyntacticObject.merge (deleteAccessible mover current) mover} + W) :=
  toTrees_injective <| by
    rw [toTrees_mergeOp, toTrees_mergeOpUnit_of', traceMergeOp_im_residual hm h hne hW,
      toTrees_of']

/-- The unit stage on a single object splits off a uniquely accessible mover beside what it
leaves. -/
theorem mergeOpUnit_of'_singleton (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    mergeOpUnit (R := ℤ) mover (of' {current}) = of' {mover, deleteAccessible mover current} :=
  toTrees_injective <| by
    rw [toTrees_mergeOpUnit_of', toTrees_of', Multiset.map_singleton,
      traceMergeOpUnit_current hm h hne]
    rfl

/-- Internal Merge of a uniquely accessible mover in a single object is the composition
`M_{T/β,β} ∘ M_{β,1}`. -/
theorem mergeOp_mergeOpUnit_of'_singleton (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    mergeOp (R := ℤ) (deleteAccessible mover current) mover (mergeOpUnit mover (of' {current})) =
      of' {SyntacticObject.merge (deleteAccessible mover current) mover} :=
  toTrees_injective <| by
    rw [toTrees_mergeOp, toTrees_mergeOpUnit_of', toTrees_of', Multiset.map_singleton,
      Multiset.map_singleton, traceMergeOp_im hm h hne]

/-- Internal Merge: the unit stage followed by Merge of a uniquely accessible mover with what it
leaves is MERGE of the mover with the member containing it, leaving the trace of its head. -/
theorem mergeOp_mergeOpUnit_of' (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1) (hne : current ≠ mover)
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    mergeOp (R := ℤ) (deleteAccessible mover current) mover
        (mergeOpUnit mover (of' ({current} + W))) =
      of' (({current} + W).mergeWith (·.headTrace) mover current) :=
  toTrees_injective <| by
    rw [toTrees_mergeOp, toTrees_mergeOpUnit_of', traceMergeOp_im_of'_merge hm h hne hW,
      toTrees_of']

/-- Sideward Merge of type 2(b): Merge of a member `T` with the only occurrence of a term `S'` of
another member `T'` is MERGE leaving the trace of the head of `S'` in `T'`. -/
theorem mergeOp_of'_sideward_member (hS' : ¬ S'.IsTrace)
    (hc : T'.terms.count S' = 1) (hne : T' ≠ S') (hT : T ∉ T'.terms) (hS'T : S' ∉ T.terms)
    (hW : ∀ U ∈ W, T ∉ U.terms ∧ S' ∉ U.terms) :
    mergeOp (R := ℤ) T S' (of' ({T, T'} + W)) =
      of' (({T, T'} + W).mergeWith (·.headTrace) T S') :=
  toTrees_injective <| by
    rw [toTrees_mergeOp_of', traceMergeOp_sideward2b_of'_merge hS' hc hne hT hS'T hW, toTrees_of']

/-- Sideward Merge of type 3(b): Merge of the only occurrences of a term `S` of a member `T` and a
term `S'` of another member `T'` is MERGE leaving the traces of their heads. -/
theorem mergeOp_of'_sideward (hS : ¬ S.IsTrace)
    (hS' : ¬ S'.IsTrace) (hcS : T.terms.count S = 1)
    (hcS' : T'.terms.count S' = 1) (hneS : T ≠ S) (hneS' : T' ≠ S') (hST' : S ∉ T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    mergeOp (R := ℤ) S S' (of' ({T, T'} + W)) =
      of' (({T, T'} + W).mergeWith (·.headTrace) S S') :=
  toTrees_injective <| by
    rw [toTrees_mergeOp_of',
      traceMergeOp_sideward3b_of'_merge hS hS' hcS hcS' hneS hneS' hST' hS'T hW, toTrees_of']

end Workspace

end Minimalist
