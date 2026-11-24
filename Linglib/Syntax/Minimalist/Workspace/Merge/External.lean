module

public import Linglib.Core.Algebra.RootedTree.DualPrimitive
public import Linglib.Syntax.Minimalist.Workspace.Merge.Basic
public import Linglib.Core.Combinatorics.RootedTree.MarkerCutConservation
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

Merge is multiplication by the grafted pair after contraction of the coproduct with the forest
`{S, S'}` (`mergeOpOfCuts_eq_mul_contractForest`), and contractions obey a product rule
(`ConnesKreimer.contractForest_mul`). Each result here evaluates that rule on a product of trees,
from the contractions of a single tree.

## Main results

* `Minimalist.Merge.mergeOpOfCuts_pair`, `mergeOp_pair`, `traceMergeOp_pair`: External Merge on a
  two-object workspace.
* `Minimalist.Merge.mergeOpOfCuts_mul_of_contractForest_eq_zero`, `mergeOpOfCuts_of'_mul`: Merge
  commutes with a spectator.
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

section DecidableEq

variable [DecidableEq (UnorderedTree α)]

instance : IsMergeCuts (admissibleCuts (α := α)) where
  crown_numEdges_lt := admissibleCuts_crown_numEdges_lt
  mem_subtrees_of_mem_crown hp hx := (exists_mem_crown_admissibleCuts_iff.mp ⟨_, hp, hx⟩).1

instance {β : Type*} (τ : UnorderedTree (α ⊕ β) → β) : IsMergeCuts (markerCuts τ) where
  crown_numEdges_lt := markerCuts_crown_numEdges_lt τ
  mem_subtrees_of_mem_crown hp hx := markerCuts_mem_subtrees_of_mem_crown τ hp hx

/-! ### Contraction of a tree

Over a cut enumeration admitting Merge, the contraction of a tree `T` with a forest `A` is `1` at
`A = {T}`, and vanishes when `A` has a member that no crown of `T` can have. -/

section Contract

variable {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
  {A : Forest (UnorderedTree α)} {T : UnorderedTree α}

/-- Contraction of `T` with a forest other than `{T}` that is the crown of no cut of `T`
    vanishes. -/
theorem contractForest_ofTree_eq_zero (hA : A ≠ {T}) (h : ∀ p ∈ cuts T, p.1 ≠ A) :
    contractForest (R := R) cuts A (ofTree T) = 0 := by
  rw [contractForest_ofTree_of_ne hA, Multiset.filter_eq_nil.mpr h, Multiset.map_zero,
    Multiset.sum_zero]

variable [IsMergeCuts cuts]

/-- Contraction of a tree with itself is `1`. -/
theorem contractForest_ofTree_self (T : UnorderedTree α) :
    contractForest (R := R) cuts {T} (ofTree T) = 1 := by
  rw [contractForest_ofTree, ite_eq_left rfl,
    Multiset.filter_eq_nil.mpr fun p hp ↦ IsMergeCuts.crown_ne_singleton hp, Multiset.map_zero,
    Multiset.sum_zero, add_zero]

/-- Contraction of `T` with a forest that has `T` beside other members vanishes. -/
theorem contractForest_ofTree_of_mem (hT : T ∈ A) (hA : A ≠ {T}) :
    contractForest (R := R) cuts A (ofTree T) = 0 :=
  contractForest_ofTree_eq_zero hA fun _ hp h ↦ IsMergeCuts.notMem_crown hp (h ▸ hT)

/-- Contraction of `T` with a nonempty forest other than `{T}` that has at least as many edges
    as `T` vanishes. -/
theorem contractForest_ofTree_of_numEdges_le (h0 : A ≠ 0) (hA : A ≠ {T})
    (h : T.numEdges ≤ (A.map numEdges).sum) : contractForest (R := R) cuts A (ofTree T) = 0 :=
  contractForest_ofTree_eq_zero hA fun _ hp hpA ↦
    (IsMergeCuts.crown_numEdges_lt hp (hpA ▸ h0)).not_ge (hpA ▸ h)

/-- Contraction with a forest vanishes on a tree that does not contain one of its members. -/
theorem contractForest_ofTree_of_notMem {t : UnorderedTree α} (ht : t ∈ A)
    (hT : t ∉ T.subtrees) : contractForest (R := R) cuts A (ofTree T) = 0 :=
  contractForest_ofTree_eq_zero
    (fun h ↦ hT (Multiset.mem_singleton.1 (h ▸ ht) ▸ T.self_mem_subtrees))
    fun _ hp h ↦ hT (IsMergeCuts.mem_subtrees_of_mem_crown hp (h ▸ ht))

end Contract

/-! ### External Merge of a pair -/

/-- External Merge of a two-object workspace, over a cut enumeration admitting Merge. In the
    product rule for the contraction of `S * S'` with `{S, S'}`, only the term contracting each
    object with itself survives: every other split gives one of the two a forest with at least
    as many edges as it has. -/
theorem mergeOpOfCuts_pair
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) (S S' : UnorderedTree α) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  have hpair : ({S} : Forest (UnorderedTree α)) + {S'} = {S, S'} := rfl
  rw [mergeOpOfCuts_eq_mul_contractForest, ← hpair, of'_add, of'_singleton, of'_singleton,
    contractForest_mul, Finset.sum_eq_single (({S} : Forest (UnorderedTree α)), {S'})]
  · rw [contractForest_ofTree_self, contractForest_ofTree_self, mul_one, mul_one, of'_singleton]
  · rintro ⟨A, B⟩ hp hne
    have hAB : A + B = {S} + {S'} := Multiset.mem_antidiagonal.1 (Multiset.mem_toFinset.1 hp)
    have hsum := congrArg (fun F ↦ (F.map numEdges).sum) hAB
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton] at hsum
    have hA : A ≠ {S} := by
      rintro rfl; exact hne (Prod.ext rfl (Multiset.add_right_inj.mp hAB))
    have hB : B ≠ {S'} := by
      rintro rfl; exact hne (Prod.ext (Multiset.add_left_inj.mp hAB) rfl)
    rcases eq_or_ne A 0 with rfl | hA0
    · rw [contractForest_ofTree_of_numEdges_le (T := S') (by rintro rfl; simp at hAB) hB
        (by simp at hsum; omega), mul_zero]
    rcases eq_or_ne B 0 with rfl | hB0
    · rw [contractForest_ofTree_of_numEdges_le hA0 hA (by simp at hsum; omega), zero_mul]
    rcases le_or_gt S.numEdges (A.map numEdges).sum with h | h
    · rw [contractForest_ofTree_of_numEdges_le hA0 hA h, zero_mul]
    · rw [contractForest_ofTree_of_numEdges_le (T := S') hB0 hB (by omega), mul_zero]
  · exact fun h ↦ absurd (by simp) h

/-- External Merge of a two-object workspace, for objects that are their own remainders
([marcolli-chomsky-berwick-2025] Lemma 1.4.1). -/
theorem mergeOp_pair [DecidableEq α] (lbl : α) {S S' : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) (hS' : deletionQuotient lbl S' = some S') :
    mergeOp (R := R) lbl S S' (of' ({S, S'} : Forest (UnorderedTree α)))
      = of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  rw [mergeOp_eq_deletionProj_comp lbl hS hS', LinearMap.comp_apply, mergeOpOfCuts_pair,
    AlgHom.toLinearMap_apply, of'_singleton, deletionProj_ofTree,
    deletionQuotient_node_pair lbl hS hS', Option.elim_some]

/-! ### Spectators -/

/-- Merge commutes with a spectator `x` whose contractions with the nonempty parts of `{S, S'}`
    vanish: in the product rule for the contraction of `x * w`, only the term that leaves `x`
    whole survives. -/
theorem mergeOpOfCuts_mul_of_contractForest_eq_zero
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) {S S' : UnorderedTree α} {x : ConnesKreimer R (UnorderedTree α)}
    (hx : ∀ A : Forest (UnorderedTree α), A ≠ 0 → A ≤ {S, S'} → contractForest cuts A x = 0)
    (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (x * w) = x * mergeOpOfCuts (R := R) cuts lbl S S' w := by
  rw [mergeOpOfCuts_eq_mul_contractForest, mergeOpOfCuts_eq_mul_contractForest, contractForest_mul,
    Finset.sum_eq_single ((0 : Forest (UnorderedTree α)), ({S, S'} : Forest (UnorderedTree α)))]
  · rw [contractForest_zero, mul_left_comm]
  · rintro ⟨A, B⟩ hp hne
    have hAB : A + B = {S, S'} := Multiset.mem_antidiagonal.1 (Multiset.mem_toFinset.1 hp)
    rw [hx A (fun h ↦ hne (by subst h; simpa using hAB)) (hAB ▸ Multiset.le_add_right A B),
      zero_mul]
  · exact fun h ↦ absurd (by simp) h

/-- Merge commutes with a spectator component having neither `S` nor `S'` as a subtree
([marcolli-chomsky-berwick-2025] Lemma 1.4.1). -/
theorem mergeOpOfCuts_ofTree_mul
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] (lbl : α) {S S' T : UnorderedTree α}
    (hT_S : S ∉ T.subtrees) (hT_S' : S' ∉ T.subtrees)
    (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (ofTree T * w) =
      ofTree T * mergeOpOfCuts (R := R) cuts lbl S S' w := by
  refine mergeOpOfCuts_mul_of_contractForest_eq_zero lbl (fun A hA hle ↦ ?_) w
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hA
  refine contractForest_ofTree_of_notMem ht ?_
  rcases (by simpa using Multiset.subset_of_le hle ht : t = S ∨ t = S') with rfl | rfl <;>
    assumption

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
