module

public import Linglib.Syntax.Minimalist.Workspace.Merge.Basic
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceConservation
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Core.Combinatorics.RootedTree.Crown
public import Linglib.Core.Algebra.RootedTree.HopfAlgebra

/-!
# External Merge

External Merge (Lemma 1.4.1 of Marcolli, Chomsky and Berwick) is Merge of two components `S, S'`
of a workspace. It replaces them by `node lbl {S, S'}` and leaves the rest unchanged. For a
two-object workspace this holds over every cut enumeration admitting Merge (`mergeOpOfCuts_pair`),
in particular at the admissible and trace cuts. With a residual workspace `F̂` it holds when no
component of `F̂` has `S` or `S'` as a subtree (`mergeOpOfCuts_pair_residual`), since such a
workspace passes through Merge unchanged (`mergeOpOfCuts_of'_mul`). The book's Merge, at the
deletion coproduct, reaches these through the projection of the remainder
(`mergeOp_eq_deletionProj_comp`), so its forms hold of objects that are their own remainders, as
syntactic objects are.

The proof of `mergeOpOfCuts_pair` expands the coproduct of `{S, S'}` into four cross-terms of the
primitive terms and the cut sums of `S` and `S'`. Only the primitive term survives: a cut of `S'`
alone would need crown `{S'}`, and cuts of both would need crowns reassembling `{S, S'}`, and
both are ruled out by the edge bound of `IsMergeCuts`.

## Main results

* `Minimalist.Merge.mergeOpOfCuts_pair`, `mergeOp_pair`, `traceMergeOp_pair`: External Merge on a
  two-object workspace.
* `Minimalist.Merge.mergeOpOfCuts_of'_mul`: Merge commutes with a spectator workspace.
* `Minimalist.Merge.mergeOpOfCuts_pair_residual`, `mergeOp_pair_residual`,
  `traceMergeOp_pair_residual`: External Merge with a residual workspace.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

private theorem sum_map_ite_eq_zero {ι M : Type*} [AddCommMonoid M] {s : Multiset ι}
    {P : ι → Prop} [DecidablePred P] {f : ι → M} (h : ∀ i ∈ s, ¬ P i) :
    (s.map fun i ↦ if P i then f i else 0).sum = 0 :=
  Multiset.sum_eq_zero fun _ hx ↦ by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact ite_eq_right (h i hi)

section DecidableEq

variable [DecidableEq (UnorderedTree α)]

instance : IsMergeCuts (admissibleCuts (α := α)) where
  crown_numEdges_lt := admissibleCuts_crown_numEdges_lt
  mem_subtrees_of_mem_crown hp hx := (exists_mem_crown_admissibleCuts_iff.mp ⟨_, hp, hx⟩).1
  filter_empty := admissibleCuts_filter_empty

instance {β : Type*} (τ : UnorderedTree (α ⊕ β) → β) : IsMergeCuts (traceCuts τ) where
  crown_numEdges_lt := traceCuts_crown_numEdges_lt τ
  mem_subtrees_of_mem_crown hp hx := traceCuts_mem_subtrees_of_mem_crown τ hp hx
  filter_empty := traceCuts_filter_empty τ

/-- External Merge of a two-object workspace, over a cut enumeration admitting Merge. -/
theorem mergeOpOfCuts_pair
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) (S S' : UnorderedTree α) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  have key (F F' : Forest (UnorderedTree α)) (t t' : ConnesKreimer R (UnorderedTree α)) :
      mergePost (R := R) lbl S S' ((of' F ⊗ₜ[R] t) * (of' F' ⊗ₜ[R] t'))
        = if F + F' = {S, S'} then of' {UnorderedTree.node lbl {S, S'}} * (t * t') else 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, mergePost_basis_tensor]
  have hpair : ({S} : Forest (UnorderedTree α)) + {S'} = {S, S'} := rfl
  have hS (p) (hp : p ∈ cuts S) : ¬ p.1 + {S'} = {S, S'} := fun h ↦
    IsMergeCuts.crown_ne_singleton hp (Multiset.add_left_inj.mp (h.trans hpair.symm))
  have hS' (p) (hp : p ∈ cuts S') : ¬ {S} + p.1 = {S, S'} := fun h ↦
    IsMergeCuts.crown_ne_singleton hp (Multiset.add_right_inj.mp (h.trans hpair.symm))
  have hSS' (p) (hp : p ∈ cuts S) (p') (hp' : p' ∈ cuts S') : ¬ p.1 + p'.1 = {S, S'} := by
    intro h
    have hsum := congrArg (fun F ↦ (F.map numEdges).sum) h
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    rcases eq_or_ne p.1 0 with h1 | h1
    · have h2 : p'.1 ≠ 0 := fun h2 ↦ by simp [h1, h2] at h
      have := IsMergeCuts.crown_numEdges_lt hp' h2
      simp only [h1, Multiset.map_zero, Multiset.sum_zero] at hsum
      omega
    · have := IsMergeCuts.crown_numEdges_lt hp h1
      rcases eq_or_ne p'.1 0 with h2 | h2
      · simp only [h2, Multiset.map_zero, Multiset.sum_zero] at hsum
        omega
      · have := IsMergeCuts.crown_numEdges_lt hp' h2
        omega
  rw [mergeOpOfCuts, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulOfCuts_apply_of',
    show ({S, S'} : Forest (UnorderedTree α)) = S ::ₘ S' ::ₘ 0 from rfl, comulForestOfCuts_cons,
    comulForestOfCuts_cons, comulForestOfCuts_zero, mul_one, comulTreeOfCuts, comulTreeOfCuts]
  simp only [ofTree, add_mul, mul_add, ← Multiset.sum_map_mul_left,
    ← Multiset.sum_map_mul_right, map_add, map_multiset_sum, Multiset.map_map,
    Function.comp_def, key, ite_eq_left hpair, mul_one]
  rw [sum_map_ite_eq_zero hS, add_zero, Multiset.sum_eq_zero, add_zero]
  · rfl
  intro x hx
  obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hx
  rw [ite_eq_right (hS' p' hp'), zero_add, sum_map_ite_eq_zero fun p hp ↦ hSS' p hp p' hp']

/-- External Merge of a two-object workspace, for objects that are their own remainders
([marcolli-chomsky-berwick-2025] Lemma 1.4.1). -/
theorem mergeOp_pair [DecidableEq α] (lbl : α) {S S' : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) (hS' : deletionQuotient lbl S' = some S') :
    mergeOp (R := R) lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  rw [mergeOp_eq_deletionProj_comp lbl hS hS', LinearMap.comp_apply, mergeOpOfCuts_pair,
    AlgHom.toLinearMap_apply, of'_singleton, deletionProj_ofTree,
    deletionQuotient_node_pair lbl hS hS', Option.elim_some]

/-- Merge commutes with a spectator component having neither `S` nor `S'` as a subtree
([marcolli-chomsky-berwick-2025] Lemma 1.4.1). -/
theorem mergeOpOfCuts_ofTree_mul
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) {S S' T : UnorderedTree α}
    (hT_S : S ∉ T.subtrees) (hT_S' : S' ∉ T.subtrees)
    (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (ofTree T * w) =
      ofTree T * mergeOpOfCuts (R := R) cuts lbl S S' w := by
  rw [mergeOpOfCuts, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, map_mul, comulOfCuts_apply_ofTree, comulTreeOfCuts, add_mul, map_add,
    ← of'_singleton]
  -- The primitive term vanishes, since `{T}` does not fit inside `{S, S'}`.
  rw [mergePost_left_mul_eq_zero_of_not_le _ _ _ _ _ ?prim, zero_add]
  case prim =>
    intro h_le
    have hT_mem : T ∈ ({S, S'} : Forest (UnorderedTree α)) :=
      Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
    rcases hT_mem with rfl | rfl
    exacts [hT_S T.self_mem_subtrees, hT_S' T.self_mem_subtrees]
  -- Split off the empty cut `(0, T)`; the nonempty cuts vanish.
  rw [← Multiset.sum_map_mul_right,
    ← Multiset.filter_add_not (fun pf => pf.1.card = 0) (cuts T),
    Multiset.map_add, Multiset.sum_add, map_add, IsMergeCuts.filter_empty,
    Multiset.map_singleton, Multiset.sum_singleton, _root_.map_multiset_sum,
    Multiset.sum_eq_zero, add_zero]
  · -- The empty cut passes `T` to the right channel.
    rw [of'_zero,
      mul_comm ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree T) _,
      mergePost_right_one_tmul, mul_comm]
    rfl
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.map_map _ _ _ ▸ hx)
    obtain ⟨hp, hcard⟩ := Multiset.mem_filter.mp hp
    refine mergePost_left_mul_eq_zero_of_not_le _ _ _ _ _ (fun h_le ↦ hcard ?_) _
    rw [Multiset.card_eq_zero]
    refine Multiset.eq_zero_of_forall_notMem fun x hx_mem => ?_
    have hx_in : x ∈ ({S, S'} : Forest (UnorderedTree α)) := Multiset.subset_of_le h_le hx_mem
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx_in
    rcases hx_in with rfl | rfl
    exacts [hT_S (IsMergeCuts.mem_subtrees_of_mem_crown hp hx_mem),
      hT_S' (IsMergeCuts.mem_subtrees_of_mem_crown hp hx_mem)]

/-- Merge commutes with a spectator workspace `F` none of whose components has `S` or `S'` as a
    subtree. -/
theorem mergeOpOfCuts_of'_mul
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) {S S' : UnorderedTree α} {F : Forest (UnorderedTree α)}
    (hF : ∀ T ∈ F, Disjoint ({S, S'} : Forest (UnorderedTree α)) T.subtrees)
    (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' F * w) =
      of' F * mergeOpOfCuts (R := R) cuts lbl S S' w := by
  induction F using Multiset.induction generalizing w with
  | empty => rw [of'_zero, one_mul, one_mul]
  | cons T F ih =>
    have hT := hF T (Multiset.mem_cons_self _ _)
    rw [of'_cons, mul_assoc,
      mergeOpOfCuts_ofTree_mul lbl (Multiset.disjoint_left.mp hT (by simp))
        (Multiset.disjoint_left.mp hT (by simp)),
      ih (fun U hU ↦ hF U (Multiset.mem_cons_of_mem hU)), mul_assoc]

/-- Merge commutes with a spectator component that has neither `S` nor `S'` as a subtree, all
    three their own remainders. -/
theorem mergeOp_ofTree_mul [DecidableEq α] (lbl : α) {S S' T : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) (hS' : deletionQuotient lbl S' = some S')
    (hT : deletionQuotient lbl T = some T) (hT_S : S ∉ T.subtrees)
    (hT_S' : S' ∉ T.subtrees) (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOp (R := R) lbl S S' (ofTree T * w) = ofTree T * mergeOp (R := R) lbl S S' w := by
  simp only [mergeOp_eq_deletionProj_comp lbl hS hS', LinearMap.comp_apply,
    mergeOpOfCuts_ofTree_mul lbl hT_S hT_S', AlgHom.toLinearMap_apply, map_mul,
    deletionProj_ofTree, hT, Option.elim_some]

/-- External Merge of `S` and `S'` beside a workspace `F̂` none of whose components contains them
leaves `F̂` unchanged ([marcolli-chomsky-berwick-2025] Lemma 1.4.1). -/
theorem mergeOpOfCuts_pair_residual
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) {S S' : UnorderedTree α} {Fhat : Forest (UnorderedTree α)}
    (hF : ∀ T ∈ Fhat, Disjoint ({S, S'} : Forest (UnorderedTree α)) T.subtrees) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' (({S, S'} : Forest (UnorderedTree α)) + Fhat))
      = of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat) := by
  rw [add_comm, of'_add, mergeOpOfCuts_of'_mul lbl hF, mergeOpOfCuts_pair, ← of'_add, add_comm]

/-- External Merge with a residual workspace, all of whose objects are their own remainders. -/
theorem mergeOp_pair_residual [DecidableEq α] (lbl : α) {S S' : UnorderedTree α}
    {Fhat : Forest (UnorderedTree α)} (hS : deletionQuotient lbl S = some S)
    (hS' : deletionQuotient lbl S' = some S')
    (hF : ∀ T ∈ Fhat, Disjoint ({S, S'} : Forest (UnorderedTree α)) T.subtrees)
    (hFu : ∀ T ∈ Fhat, deletionQuotient lbl T = some T) :
    mergeOp (R := R) lbl S S' (of' (({S, S'} : Forest (UnorderedTree α)) + Fhat))
      = of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + Fhat) := by
  rw [mergeOp_eq_deletionProj_comp lbl hS hS', LinearMap.comp_apply,
    mergeOpOfCuts_pair_residual lbl hF, AlgHom.toLinearMap_apply]
  refine deletionProj_of' lbl fun T hT ↦ ?_
  rcases Multiset.mem_add.mp hT with h | h
  · rw [Multiset.mem_singleton.mp h]
    exact deletionQuotient_node_pair lbl hS hS'
  · exact hFu T h

end DecidableEq

/-! ### External Merge at the trace cuts -/

/-- External Merge of a two-object workspace at the trace cuts. -/
theorem traceMergeOp_pair {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : UnorderedTree (α ⊕ β)) :
    traceMergeOp (R := R) τ lbl S S' (of' ({S, S'} : Forest (UnorderedTree (α ⊕ β))))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree (α ⊕ β))) :=
  mergeOpOfCuts_pair lbl S S'

/-- External Merge at the trace cuts with a residual workspace. -/
theorem traceMergeOp_pair_residual {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) {S S' : UnorderedTree (α ⊕ β)}
    {Fhat : Forest (UnorderedTree (α ⊕ β))}
    (hF : ∀ T ∈ Fhat, Disjoint ({S, S'} : Forest (UnorderedTree (α ⊕ β))) T.subtrees) :
    traceMergeOp (R := R) τ lbl S S' (of' (({S, S'} : Forest (UnorderedTree (α ⊕ β))) + Fhat))
      = of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree (α ⊕ β))) + Fhat) :=
  mergeOpOfCuts_pair_residual lbl hF

end Minimalist.Merge
