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

The remainder of a deletion of a syntactic object is a syntactic object, so the deletion
coproduct `Δ^d` is a coproduct `Workspace.deletionComul` on the algebra of workspaces, and the
Merge of their Definition 1.3.4 is an operator `Workspace.mergeOp S S'` on it: multiplication by
`{S, S'}` after contraction of `Δ^d` with the workspace of `S` and `S'`.

A cut of a syntactic object that leaves a trace in place of each extracted term also extracts
syntactic objects and leaves a syntactic object, so the trace cuts are an enumeration
`SyntacticObject.cuts` on the objects themselves, and Merge at the trace cuts is an operator
`Workspace.traceMergeOp S S'`: on a workspace `W` it is the sum, over the cuts of `W` that extract
`S` and `S'`, of the workspace with `{S, S'}` beside what the cut leaves. The homomorphism
`toTrees` intertwines each operator with its counterpart on trees, and the forms of Merge are
stated on workspaces.

## Main definitions

* `Minimalist.Workspace.toTrees`: the algebra of workspaces in the algebra of forests of trees.
* `Minimalist.SyntacticObject.deletionCuts`, `Minimalist.Workspace.deletionComul`: the deletion
  cuts of a syntactic object and the deletion coproduct on workspaces.
* `Minimalist.Workspace.mergeOp`, `Minimalist.Workspace.mergeOpUnit`: Merge at the deletion
  coproduct and its unit stage, on the algebra of workspaces.
* `Minimalist.SyntacticObject.cuts`: the trace cuts of a syntactic object.
* `Minimalist.Workspace.traceMergeOp`, `Minimalist.Workspace.traceMergeOpUnit`: Merge at the
  trace cuts and its unit stage, on the algebra of workspaces.

## Main results

* `Minimalist.IsSyntacticObject.of_mem_markerCuts`: a trace cut of a syntactic object leaves a
  syntactic object.
* `Minimalist.Workspace.toTrees_injective`
* `Minimalist.Workspace.map_toTrees_comp_deletionComul`: `toTrees` intertwines the deletion
  coproducts.
* `Minimalist.Workspace.toTrees_mergeOp`, `Minimalist.Workspace.toTrees_mergeOpUnit`: `toTrees`
  intertwines Merge on workspaces with Merge at the deletion coproduct.
* `Minimalist.Workspace.mergeOp_of'_pair`, `Minimalist.Workspace.mergeOp_mergeOpUnit_of'_singleton`:
  External and Internal Merge at the deletion coproduct.
* `Minimalist.Workspace.toTrees_traceMergeOp`, `Minimalist.Workspace.toTrees_traceMergeOpUnit`:
  `toTrees` intertwines Merge on workspaces with Merge at the trace cuts.
* `Minimalist.Workspace.traceMergeOp_of'`: External Merge is MERGE.
* `Minimalist.Workspace.traceMergeOp_traceMergeOpUnit_of'_singleton`,
  `Minimalist.Workspace.traceMergeOp_traceMergeOpUnit_of'`: Internal Merge is the composition
  `M_{T/β,β} ∘ M_{β,1}`, and it is MERGE leaving the trace of the mover's head.
* `Minimalist.Workspace.traceMergeOp_of'_sideward_member`,
  `Minimalist.Workspace.traceMergeOp_of'_sideward`: Sideward Merge of types 2(b) and 3(b).

## Implementation notes

Merge at the deletion coproduct is defined from a coproduct on the algebra of workspaces, and
`toTrees` intertwines it with the operator on trees because it intertwines the coproducts and
contraction is natural.

The operators at the trace cuts are defined on the basis of workspaces by the formula that
`Merge.mergeOpOfCuts_apply_of'` proves of the operator on trees, over the cuts of syntactic
objects, and not as the restriction of the operator on trees to the range of `toTrees`: a
restriction needs the range to be stable before the operator can be named, while the formula
makes stability the theorem `toTrees_traceMergeOp`.

Marcolli, Chomsky and Berwick define Merge at the deletion coproduct, which leaves no trace, and
obtain it from the coproduct with traces by a projection of the right channel
(`Merge.mergeOp_eq_comp_traceMergeOp`, on trees without traces). Merge at the admissible cuts does
not preserve workspaces, a remainder there having a unary vertex.

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

/-- The deletion cuts of a syntactic object, as pairs of the workspace of extracted terms and the
remainder of the deletion, absent when the cut leaves nothing. -/
noncomputable def deletionCuts (S : SyntacticObject) :
    Multiset (Workspace × Option SyntacticObject) :=
  (admissibleCuts S.toUnorderedTree).attach.map fun p ↦
    (p.1.1.attach.map fun t ↦ ofUnorderedTree t.1 (isSyntacticObject_of_mem_subtrees S t.1
        (exists_mem_crown_admissibleCuts_iff.mp ⟨_, p.2, t.2⟩).1),
      (deletionQuotient Vertex.bare p.1.2).pmap ofUnorderedTree
        fun _ hr ↦ isSyntacticObject_of_deletionQuotient p.2 hr)

theorem map_deletionCuts (S : SyntacticObject) :
    S.deletionCuts.map (Prod.map (Multiset.map toUnorderedTree) (Option.map toUnorderedTree)) =
      ConnesKreimer.deletionCuts Vertex.bare S.toUnorderedTree := by
  rw [deletionCuts, Multiset.map_map, ConnesKreimer.deletionCuts]
  refine (Multiset.map_congr rfl fun p _ ↦ ?_).trans
    (Multiset.attach_map_val' _ fun q : Multiset (UnorderedTree Vertex) × UnorderedTree Vertex ↦
      (q.1, deletionQuotient Vertex.bare q.2))
  refine Prod.ext ?_ ?_
  · simp only [Function.comp_apply, Prod.map_fst, Multiset.map_map,
      toUnorderedTree_ofUnorderedTree]
    exact Multiset.attach_map_val _
  · simp only [Function.comp_apply, Prod.map_snd, Option.map_pmap,
      toUnorderedTree_ofUnorderedTree]
    rw [Option.pmap_eq_map, Option.map_id']

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

/-- Merge at the trace cuts on the algebra of workspaces: on a workspace `W`, the sum over the
cuts of `W` that extract `S` and `S'` of the workspace with `{S, S'}` beside what the cut leaves,
a trace in place of each extracted term. -/
noncomputable def traceMergeOp (S S' : SyntacticObject) :
    ConnesKreimer R SyntacticObject →ₗ[R] ConnesKreimer R SyntacticObject :=
  linearLift fun W ↦ (((forestCuts SyntacticObject.cuts W).filter (·.1 = {S, S'})).map
    fun p ↦ of' ({SyntacticObject.merge S S'} + p.2)).sum

/-- The unit stage at the trace cuts on the algebra of workspaces: on a workspace `W`, the sum
over the cuts of `W` that extract `S` of the workspace with `S` beside what the cut leaves. -/
noncomputable def traceMergeOpUnit (S : SyntacticObject) :
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

theorem toTrees_traceMergeOp_of' (S S' : SyntacticObject) (W : Workspace) :
    toTrees (traceMergeOp (R := R) S S' (of' W)) =
      Merge.traceMergeOp traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (of' (W.map toUnorderedTree)) := by
  have hpair : ({S.toUnorderedTree, S'.toUnorderedTree} : Multiset (UnorderedTree Vertex)) =
      Multiset.map toUnorderedTree {S, S'} := rfl
  rw [Merge.traceMergeOp, Merge.mergeOpOfCuts_apply_of', forestCuts_map_toUnorderedTree,
    Multiset.filter_map, Multiset.map_map, traceMergeOp, linearLift_of', map_multiset_sum,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, hpair, map_toUnorderedTree_eq_iff,
    toTrees_of', Multiset.map_singleton, toUnorderedTree_merge, of'_add, map_mul]

theorem toTrees_traceMergeOpUnit_of' (S : SyntacticObject) (W : Workspace) :
    toTrees (traceMergeOpUnit (R := R) S (of' W)) =
      Merge.traceMergeOpUnit traceEncoder S.toUnorderedTree (of' (W.map toUnorderedTree)) := by
  have hone : ({S.toUnorderedTree} : Multiset (UnorderedTree Vertex)) =
      Multiset.map toUnorderedTree {S} := rfl
  rw [Merge.traceMergeOpUnit, Merge.mergeOpUnitOfCuts_apply_of', forestCuts_map_toUnorderedTree,
    Multiset.filter_map, Multiset.map_map, traceMergeOpUnit, linearLift_of', map_multiset_sum,
    Multiset.map_map]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, hone, map_toUnorderedTree_eq_iff,
    toTrees_of', ← Multiset.map_add]

/-- `toTrees` intertwines Merge on workspaces with Merge at the trace cuts. -/
theorem toTrees_traceMergeOp (S S' : SyntacticObject) (x : ConnesKreimer R SyntacticObject) :
    toTrees (traceMergeOp S S' x) =
      Merge.traceMergeOp traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree
        (toTrees x) :=
  LinearMap.congr_fun (lhom_ext' (f := toTrees.toLinearMap ∘ₗ traceMergeOp S S')
    (g := Merge.traceMergeOp traceEncoder Vertex.bare S.toUnorderedTree S'.toUnorderedTree ∘ₗ
      toTrees.toLinearMap) fun W ↦ by
    simpa using toTrees_traceMergeOp_of' (R := R) S S' W) x

/-- `toTrees` intertwines the unit stage on workspaces with the unit stage at the trace cuts. -/
theorem toTrees_traceMergeOpUnit (S : SyntacticObject) (x : ConnesKreimer R SyntacticObject) :
    toTrees (traceMergeOpUnit S x) =
      Merge.traceMergeOpUnit traceEncoder S.toUnorderedTree (toTrees x) :=
  LinearMap.congr_fun (lhom_ext' (f := toTrees.toLinearMap ∘ₗ traceMergeOpUnit S)
    (g := Merge.traceMergeOpUnit traceEncoder S.toUnorderedTree ∘ₗ toTrees.toLinearMap) fun W ↦ by
    simpa using toTrees_traceMergeOpUnit_of' (R := R) S W) x

/-! ### Merge at the deletion coproduct

The remainder of a deletion of a syntactic object is a syntactic object, so the deletion coproduct
`Δ^d` is a coproduct on the algebra of workspaces, and the Merge of
[marcolli-chomsky-berwick-2025] Definition 1.3.4 is an operator on it. -/

open scoped TensorProduct in
/-- The deletion coproduct `Δ^d` on the algebra of workspaces. -/
noncomputable def deletionComul : ConnesKreimer R SyntacticObject →ₐ[R]
    ConnesKreimer R SyntacticObject ⊗[R] ConnesKreimer R SyntacticObject :=
  aeval fun S ↦ ofTree S ⊗ₜ[R] 1 +
    (S.deletionCuts.map fun p ↦ of' (R := R) p.1 ⊗ₜ[R] p.2.elim 1 ofTree).sum

/-- `toTrees` intertwines the deletion coproduct on workspaces with the deletion coproduct on
trees. -/
theorem map_toTrees_comp_deletionComul :
    (Algebra.TensorProduct.map toTrees toTrees).comp (deletionComul (R := R)) =
      (deletionComulAlgHom (R := R) Vertex.bare).comp toTrees := by
  ext S
  simp only [AlgHom.comp_apply, deletionComul, aeval_ofTree, toTrees_ofTree,
    deletionComulAlgHom_apply_ofTree, ← map_deletionCuts, map_add, map_multiset_sum,
    Multiset.map_map, Algebra.TensorProduct.map_tmul, map_one]
  refine congrArg _ (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_))
  rcases p with ⟨W, _ | Q⟩ <;> simp

/-- The Merge operator `M_{S,S'}` of [marcolli-chomsky-berwick-2025] Definition 1.3.4 on the
algebra of workspaces: multiplication by `{S, S'}` after contraction of the deletion coproduct
with the workspace of `S` and `S'`. -/
noncomputable def mergeOp (S S' : SyntacticObject) :
    ConnesKreimer R SyntacticObject →ₗ[R] ConnesKreimer R SyntacticObject :=
  LinearMap.mulLeft R (ofTree (SyntacticObject.merge S S')) ∘ₗ
    contractAlong (deletionComul (R := R)).toLinearMap (lcoeff R ({S, S'} : Workspace))

/-- The unit stage `M_{S,1}` at the deletion coproduct on the algebra of workspaces. -/
noncomputable def mergeOpUnit (S : SyntacticObject) :
    ConnesKreimer R SyntacticObject →ₗ[R] ConnesKreimer R SyntacticObject :=
  LinearMap.mulLeft R (ofTree S) ∘ₗ
    contractAlong (deletionComul (R := R)).toLinearMap (lcoeff R ({S} : Workspace))

open scoped TensorProduct in
/-- `toTrees` carries the contraction of `Δ^d` with a workspace to the contraction with its
trees. -/
private theorem toTrees_comp_contractAlong_deletionComul (W : Workspace) :
    toTrees.toLinearMap ∘ₗ contractAlong (deletionComul (R := R)).toLinearMap (lcoeff R W) =
      contractAlong (deletionComulAlgHom (R := R) Vertex.bare).toLinearMap
        (lcoeff R (W.map toUnorderedTree)) ∘ₗ toTrees.toLinearMap := by
  have h : TensorProduct.map (toTrees (R := R)).toLinearMap toTrees.toLinearMap ∘ₗ
      (deletionComul (R := R)).toLinearMap =
      (deletionComulAlgHom (R := R) Vertex.bare).toLinearMap ∘ₗ toTrees.toLinearMap :=
    congrArg AlgHom.toLinearMap (map_toTrees_comp_deletionComul (R := R))
  calc _ = toTrees.toLinearMap ∘ₗ contractAlong (deletionComul (R := R)).toLinearMap
          (lcoeff R (W.map toUnorderedTree) ∘ₗ toTrees.toLinearMap) := by
        rw [toTrees, lcoeff_map_comp_rename toUnorderedTree_injective]
    _ = contractAlong (TensorProduct.map (toTrees (R := R)).toLinearMap toTrees.toLinearMap ∘ₗ
          (deletionComul (R := R)).toLinearMap) (lcoeff R (W.map toUnorderedTree)) :=
        (contractAlong_map_comp _ _ _ _).symm
    _ = _ := by rw [h]; rfl

/-- `toTrees` intertwines Merge on workspaces with Merge at the deletion coproduct on trees. -/
theorem toTrees_mergeOp (S S' : SyntacticObject) (x : ConnesKreimer R SyntacticObject) :
    toTrees (mergeOp S S' x) =
      Merge.mergeOp Vertex.bare S.toUnorderedTree S'.toUnorderedTree (toTrees x) := by
  have h := LinearMap.congr_fun (toTrees_comp_contractAlong_deletionComul (R := R) {S, S'}) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h
  rw [mergeOp, LinearMap.comp_apply, LinearMap.mulLeft_apply, map_mul, toTrees_ofTree,
    toUnorderedTree_merge, h, Merge.mergeOp, Merge.mergeAlong_pair_apply]
  rfl

/-- `toTrees` intertwines the unit stage on workspaces with the unit stage at the deletion
coproduct on trees. -/
theorem toTrees_mergeOpUnit (S : SyntacticObject) (x : ConnesKreimer R SyntacticObject) :
    toTrees (mergeOpUnit S x) = Merge.mergeOpUnit Vertex.bare S.toUnorderedTree (toTrees x) := by
  have h := LinearMap.congr_fun (toTrees_comp_contractAlong_deletionComul (R := R) {S}) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h
  rw [mergeOpUnit, LinearMap.comp_apply, LinearMap.mulLeft_apply, map_mul, toTrees_ofTree, h]
  rfl

/-- External Merge at the deletion coproduct: Merge of the two members of a workspace is their
merge. -/
theorem mergeOp_of'_pair (S S' : SyntacticObject) :
    mergeOp (R := ℤ) S S' (of' {S, S'}) = of' {SyntacticObject.merge S S'} :=
  toTrees_injective <| by
    rw [toTrees_mergeOp, toTrees_of', toTrees_of']
    exact mergeOp_node S S'

/-- Internal Merge at the deletion coproduct: when one deletion extracts the mover, the unit
stage followed by Merge with the remainder `Q` yields the one object `{Q, mover}`. -/
theorem mergeOp_mergeOpUnit_of'_singleton {current mover : SyntacticObject}
    {p0 : Multiset (UnorderedTree Vertex) × UnorderedTree Vertex}
    (h : (admissibleCuts current.toUnorderedTree).filter
        (fun p ↦ p.1 = {mover.toUnorderedTree}) = {p0})
    (hne : current ≠ mover) :
    ∃ Q : SyntacticObject, Q.toUnorderedTree = p0.2.contractUnary ∧
      mergeOp (R := ℤ) Q mover (mergeOpUnit mover (of' {current})) =
        of' {SyntacticObject.merge Q mover} := by
  obtain ⟨Q, hQ, hm⟩ := mergeOp_im h hne
  refine ⟨Q, hQ, toTrees_injective ?_⟩
  rw [toTrees_mergeOp, toTrees_mergeOpUnit, toTrees_of', toTrees_of']
  exact hm

/-! ### The forms of Merge -/

variable {S S' T T' mover current : SyntacticObject} {W : Workspace}

/-- External Merge: Merge of two members of a workspace that no other member contains is MERGE. -/
theorem traceMergeOp_of' (hle : {S, S'} ≤ W) (hW : ∀ U ∈ W - {S, S'}, S ∉ U.terms ∧ S' ∉ U.terms) :
    traceMergeOp (R := ℤ) S S' (of' W) = of' (W.merge S S') :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp_of', traceMergeOp_of'_merge traceEncoder hle hW, toTrees_of']

/-- External Merge of two objects beside spectators that contain neither. -/
theorem traceMergeOp_of'_add (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    traceMergeOp (R := ℤ) S S' (of' ({S, S'} + W)) = of' ({SyntacticObject.merge S S'} + W) :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp_of', traceMergeOp_node_residual traceEncoder S S' hW, toTrees_of']

/-- The unit stage beside spectators that do not contain the mover splits a uniquely accessible
mover off the object containing it. -/
theorem traceMergeOpUnit_of'_add (hm : ¬ mover.IsTrace) (h : current.terms.count mover = 1)
    (hne : current ≠ mover) (hW : ∀ U ∈ W, mover ∉ U.terms) :
    traceMergeOpUnit (R := ℤ) mover (of' ({current} + W)) =
      of' ({mover, deleteAccessible mover current} + W) :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOpUnit_of', toTrees_of', Multiset.map_add, Multiset.map_add,
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
theorem traceMergeOp_traceMergeOpUnit_of'_add (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1)
    (hne : current ≠ mover)
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    traceMergeOp (R := ℤ) (deleteAccessible mover current) mover
        (traceMergeOpUnit mover (of' ({current} + W))) =
      of' ({SyntacticObject.merge (deleteAccessible mover current) mover} + W) :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp, toTrees_traceMergeOpUnit_of', traceMergeOp_im_residual hm h hne hW,
      toTrees_of']

/-- The unit stage on a single object splits off a uniquely accessible mover beside what it
leaves. -/
theorem traceMergeOpUnit_of'_singleton (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    traceMergeOpUnit (R := ℤ) mover (of' {current}) = of' {mover, deleteAccessible mover current} :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOpUnit_of', toTrees_of', Multiset.map_singleton,
      traceMergeOpUnit_current hm h hne]
    rfl

/-- Internal Merge of a uniquely accessible mover in a single object is the composition
`M_{T/β,β} ∘ M_{β,1}`. -/
theorem traceMergeOp_traceMergeOpUnit_of'_singleton (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    traceMergeOp (R := ℤ) (deleteAccessible mover current) mover
        (traceMergeOpUnit mover (of' {current})) =
      of' {SyntacticObject.merge (deleteAccessible mover current) mover} :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp, toTrees_traceMergeOpUnit_of', toTrees_of', Multiset.map_singleton,
      Multiset.map_singleton, traceMergeOp_im hm h hne]

/-- Internal Merge: the unit stage followed by Merge of a uniquely accessible mover with what it
leaves is MERGE of the mover with the member containing it, leaving the trace of its head. -/
theorem traceMergeOp_traceMergeOpUnit_of' (hm : ¬ mover.IsTrace)
    (h : current.terms.count mover = 1) (hne : current ≠ mover)
    (hW : ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms) :
    traceMergeOp (R := ℤ) (deleteAccessible mover current) mover
        (traceMergeOpUnit mover (of' ({current} + W))) =
      of' (({current} + W).mergeWith (·.headTrace) mover current) :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp, toTrees_traceMergeOpUnit_of', traceMergeOp_im_of'_merge hm h hne hW,
      toTrees_of']

/-- Sideward Merge of type 2(b): Merge of a member `T` with the only occurrence of a term `S'` of
another member `T'` is MERGE leaving the trace of the head of `S'` in `T'`. -/
theorem traceMergeOp_of'_sideward_member (hS' : ¬ S'.IsTrace)
    (hc : T'.terms.count S' = 1) (hne : T' ≠ S') (hT : T ∉ T'.terms) (hS'T : S' ∉ T.terms)
    (hW : ∀ U ∈ W, T ∉ U.terms ∧ S' ∉ U.terms) :
    traceMergeOp (R := ℤ) T S' (of' ({T, T'} + W)) =
      of' (({T, T'} + W).mergeWith (·.headTrace) T S') :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp_of', traceMergeOp_sideward2b_of'_merge hS' hc hne hT hS'T hW,
      toTrees_of']

/-- Sideward Merge of type 3(b): Merge of the only occurrences of a term `S` of a member `T` and a
term `S'` of another member `T'` is MERGE leaving the traces of their heads. -/
theorem traceMergeOp_of'_sideward (hS : ¬ S.IsTrace)
    (hS' : ¬ S'.IsTrace) (hcS : T.terms.count S = 1)
    (hcS' : T'.terms.count S' = 1) (hneS : T ≠ S) (hneS' : T' ≠ S') (hST' : S ∉ T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    traceMergeOp (R := ℤ) S S' (of' ({T, T'} + W)) =
      of' (({T, T'} + W).mergeWith (·.headTrace) S S') :=
  toTrees_injective <| by
    rw [toTrees_traceMergeOp_of',
      traceMergeOp_sideward3b_of'_merge hS hS' hcS hcS' hneS hneS' hST' hS'T hW, toTrees_of']

end Workspace

end Minimalist
