/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.AdmissibleCut
public import Linglib.Core.Algebra.RootedTree.DualPrimitive
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Data.UnorderedTree.Leaves
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.Deletion
public import Linglib.Core.Combinatorics.RootedTree.MarkerCut
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The Merge operator on workspaces

The Merge operator of Marcolli, Chomsky and Berwick (their Definition 1.3.4) acts on the workspace
algebra `ConnesKreimer R (UnorderedTree α)`. For a pair `S, S'` of accessible terms,

  M_{S,S'} = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ,

where `Δ` is a coproduct extracting accessible terms, `δ_{S,S'}` keeps the terms whose left
channel is the forest `{S, S'}` (Definition 1.3.1), `B` grafts that forest under a new root
(Definition 1.3.2), and `⊔` multiplies the two channels back into one workspace. Only `Δ` depends
on how accessible terms are cut out, so the operator is defined over an arbitrary cut enumeration
`cuts` (`mergeOpOfCuts`). The book's `Δ` is the deletion coproduct `Δ^d`, and `mergeOp` is Merge at
that coproduct; `traceMergeOp` is Merge at the trace cuts. In the unit stage `M_{β,1}` of Internal
Merge (Proposition 1.4.2) the grafting is the identity, `B` leaving a single tree as it is
(`mergeOpUnitOfCuts`).

On a workspace `F`, Merge grafts `{S, S'}` beside the trunk of each forest cut of `F` whose crown
is `{S, S'}`, summed over all such cuts (`mergeOpOfCuts_apply_of'`, the book's (1.3.11)). Each form
of Merge in their §1.4 is this sum on a particular workspace.

External, Internal and Sideward Merge are in `Merge/External.lean`, `Merge/Internal.lean` and
`Merge/Sideward.lean`; the Minimal-Search weighting is in `Merge/MinimalSearch.lean`.

## Main definitions

* `Minimalist.Merge.matchForest`, `graft`: the matching projection `γ` and the grafting `B`.
* `Minimalist.Merge.mergeAlong`: Merge at a forest along a coproduct.
* `Minimalist.Merge.mergeOpOfCuts`, `mergeOp`, `traceMergeOp`: Merge over a cut enumeration, at the
  deletion coproduct, and at the trace cuts.
* `Minimalist.Merge.mergeOpUnitOfCuts`, `mergeOpUnit`, `traceMergeOpUnit`: the unit stage `M_{β,1}`.
* `Minimalist.Merge.IsMergeCuts`: cut enumerations whose nonempty crowns have fewer edges than
  their tree.

## Main results

* `Minimalist.Merge.mergeAlong_eq_mul'_comp`: Merge along a coproduct is the chain
  `⊔ ∘ (B ⊗ id) ∘ δ ∘ Δ`.
* `Minimalist.Merge.graft_ofTree_mul_ofTree`: the Merge of two trees is the grafting of their
  product.
* `Minimalist.Merge.mergeOpOfCuts_eq_mul_contractForest`: Merge is multiplication by the grafted
  pair after contraction of the coproduct with `{S, S'}`.
* `Minimalist.Merge.mergeOpOfCuts_apply_of'`, `mergeOpOfCuts_apply_of'_eq_sum`: Merge on a workspace
  is a sum over its forest cuts, or over a choice of cut for each of its trees.
* `Minimalist.Merge.mergeOpOfCuts_comm`: Merge does not depend on the order of the pair.
* `Minimalist.Merge.mergeOp_eq_mergeAlong_comulAlgHom`, `mergeOp_eq_comp_markerComulAlgHom`: Merge
  at `Δ^d` through the Connes–Kreimer coproduct and through the trace coproduct, the two
  expressions of the book's (1.3.10).
* `Minimalist.Merge.mergeOp_eq_deletionProj_comp`, `mergeOpUnit_eq_deletionProj_comp`: on
  objects that are their own remainders, Merge at the deletion coproduct is Merge at the
  admissible cuts followed by the projection `Π_{d,ρ}`.
* `Minimalist.Merge.eraseTraces_comp_traceMergeOp`, `mergeOp_eq_comp_traceMergeOp`,
  `mergeOpUnit_eq_comp_traceMergeOpUnit`: on trees without traces, erasing the traces of Merge at
  the trace cuts gives Merge at the admissible cuts, and projecting too gives Merge at the
  deletion coproduct.

## Implementation notes

The chain `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ` sends a term `a ⊗ b` of the coproduct to the coefficient
of `{S, S'}` in `a` times the product of the grafted pair with `b`. `mergeAlong` is defined in that
form, as multiplication by the grafting of the forest after contraction of the coproduct with the
coefficient functional of the forest, and `mergeAlong_eq_mul'_comp` recovers the chain. In this
form an algebra map commutes with Merge when it sends the grafted tree to the grafted tree, and
the product rule for contractions (`ConnesKreimer.contractForest_mul`) applies to Merge.

The grafting `B` leaves a single tree as it is, so the unit stage `M_{β,1}` is Merge at the forest
`{β}` (`mergeAlong_singleton`). `mergeOpUnitOfCuts` and `mergeOpUnit` are stated without the
label, which they do not use.

Definition 1.3.4 fixes the deletion coproduct `Δ^d`, which reduces the remainder of a cut to a
binary tree, and `mergeOp` is Merge at that coproduct. The Connes–Kreimer coproduct `Δ^ρ` keeps the
remainder as it is. The two extract the same accessible terms, but `⊔` multiplies the remainder
into the result, so Merge at the admissible cuts (`mergeOpOfCuts admissibleCuts`) is not the book's
operator: its Internal Merge leaves a unary vertex, which no syntactic object has. The book writes
(1.3.7) through `Δ^ρ` only with the right channel projected
(`mergeOp_eq_mergeAlong_comulAlgHom`).

`mergeOp lbl` uses the label `lbl` twice: Merge gives it to the new root, and the deletion takes it
to mark the vertices with children, removing those a cut leaves childless. The deletion coproduct
is not `comulOfCuts` of a cut enumeration, since a remainder may be empty, so `mergeOp` is defined
from `deletionComulAlgHom`. On trees that are their own remainders, as syntactic objects are, it is
Merge at the admissible cuts followed by the projection (`mergeOp_eq_deletionProj_comp`).

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### Cut enumerations that admit Merge -/

/-- A cut enumeration admits Merge when it is counital and its crowns are subtrees with fewer
    edges in total than their tree. The edge bound makes External Merge of a pair exact
    (`mergeOpOfCuts_pair`); the other two let a spectator component pass through
    (`mergeOpOfCuts_ofTree_mul`). -/
class IsMergeCuts
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)) : Prop
    extends IsCounitalCuts cuts where
  crown_numEdges_lt {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α} :
    p ∈ cuts T → p.1 ≠ 0 → (p.1.map numEdges).sum < T.numEdges
  mem_subtrees_of_mem_crown {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α}
    {x : UnorderedTree α} : p ∈ cuts T → x ∈ p.1 → x ∈ T.subtrees

namespace IsMergeCuts

variable {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
  [IsMergeCuts cuts] {T : UnorderedTree α}

/-- No cut of an enumeration admitting Merge has its own tree in the crown. -/
theorem notMem_crown {p : Forest (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cuts T) :
    T ∉ p.1 := fun h ↦
  (crown_numEdges_lt hp (by rintro h0; simp [h0] at h)).not_ge
    (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ h))

/-- No cut of an enumeration admitting Merge extracts the whole tree. -/
theorem crown_ne_singleton {p : Forest (UnorderedTree α) × UnorderedTree α} (hp : p ∈ cuts T) :
    p.1 ≠ {T} := fun h ↦ notMem_crown hp (h ▸ Multiset.mem_singleton_self T)

/-- Every crown member of a cut in `treeCuts cuts T`, the whole tree included, is a subtree of
    `T`. -/
theorem mem_subtrees_of_mem_treeCuts {a : Forest (UnorderedTree α) × Forest (UnorderedTree α)}
    (ha : a ∈ treeCuts cuts T) {x : UnorderedTree α} (hx : x ∈ a.1) : x ∈ T.subtrees := by
  rcases Multiset.mem_cons.mp ha with rfl | ha
  · rw [Multiset.mem_singleton.mp hx]; exact T.self_mem_subtrees
  · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ha
    exact mem_subtrees_of_mem_crown hp hx

end IsMergeCuts

/-! ### Matching and grafting -/

/-- The matching projection `γ_F` of [marcolli-chomsky-berwick-2025] Definition 1.3.1 keeps the
    coefficient of the basis element `F` and sends every other basis element to zero. The book's
    `γ_{S,S'}` is `matchForest {S, S'}`, and `δ_{S,S'}` is `γ_{S,S'} ⊗ id`. -/
noncomputable def matchForest (F : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  (lcoeff R F).smulRight (of' F)

theorem matchForest_of' [DecidableEq (UnorderedTree α)] (F G : Forest (UnorderedTree α)) :
    matchForest (R := R) F (of' G) = if G = F then of' G else 0 := by
  rw [matchForest, LinearMap.smulRight_apply, lcoeff_apply, coeff_of']
  split_ifs with h
  · rw [one_smul, h]
  · rw [zero_smul]

/-- The grafting operator `B` of [marcolli-chomsky-berwick-2025] Definition 1.3.2 puts the trees
    of a forest under a new root labelled `lbl`, and leaves a single tree as it is. -/
noncomputable def graft (lbl : α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  linearLift fun F ↦ if F.card ≤ 1 then of' F else bPlus lbl (of' F)

theorem graft_of' (lbl : α) (F : Forest (UnorderedTree α)) :
    graft (R := R) lbl (of' F) = if F.card ≤ 1 then of' F else ofTree (.node lbl F) := by
  rw [graft, linearLift_of', bPlus_of']

@[simp] theorem graft_one (lbl : α) :
    graft (R := R) lbl (1 : ConnesKreimer R (UnorderedTree α)) = 1 := by
  rw [← of'_zero, graft_of']; simp

@[simp] theorem graft_ofTree (lbl : α) (T : UnorderedTree α) :
    graft (R := R) lbl (ofTree T) = ofTree T := by
  rw [← of'_singleton, graft_of']; simp

@[simp] theorem graft_of'_pair (lbl : α) (S S' : UnorderedTree α) :
    graft (R := R) lbl (of' {S, S'}) = ofTree (.node lbl {S, S'}) := by
  rw [graft_of']; simp

/-- The Merge of two trees is the grafting of their product
    ([marcolli-chomsky-berwick-2025] Lemma 1.3.3). -/
theorem graft_ofTree_mul_ofTree (lbl : α) (S S' : UnorderedTree α) :
    graft (R := R) lbl (ofTree S * ofTree S') = ofTree (.node lbl {S, S'}) := by
  rw [← of'_singleton, ← of'_singleton, ← of'_add]
  exact graft_of'_pair lbl S S'

/-! ### Merge along a coproduct

For a forest `F`, the chain `⊔ ∘ (B ⊗ id) ∘ (γ_F ⊗ id) ∘ Δ` contracts the left channel of `Δ` with
the coefficient of `F` and multiplies what is left of the right channel by the grafting of `F`.
At `F = {S, S'}` it is `M_{S,S'}`, and at `F = {β}`, where the grafting is `β`, it is the unit
stage `M_{β,1}` of Internal Merge (Proposition 1.4.2), which occurs only composed with
`M_{T/β,β}` ([marcolli-chomsky-berwick-2025] Remark 1.4.3). -/

/-- Merge at the forest `F` along a coproduct `Δ`: multiplication by the grafting of `F` after
    contraction of `Δ` with the coefficient of `F`. -/
noncomputable def mergeAlong
    (Δ : ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (lbl : α) (F : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mulLeft R (graft lbl (of' F)) ∘ₗ contractAlong Δ (lcoeff R F)

section MergeAlong

variable (Δ : ConnesKreimer R (UnorderedTree α) →ₗ[R]
  ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) (lbl : α)

theorem mergeAlong_apply (F : Forest (UnorderedTree α)) (x : ConnesKreimer R (UnorderedTree α)) :
    mergeAlong Δ lbl F x = graft lbl (of' F) * contractAlong Δ (lcoeff R F) x := rfl

/-- Merge along `Δ` is the chain `⊔ ∘ (B ⊗ id) ∘ δ ∘ Δ` of
    [marcolli-chomsky-berwick-2025] (1.3.7). -/
theorem mergeAlong_eq_mul'_comp (F : Forest (UnorderedTree α)) :
    mergeAlong Δ lbl F = LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
      TensorProduct.map (graft lbl) LinearMap.id ∘ₗ
      TensorProduct.map (matchForest F) LinearMap.id ∘ₗ Δ := by
  have h : LinearMap.mulLeft R (graft (R := R) lbl (of' F)) ∘ₗ
      (TensorProduct.lid R _).toLinearMap ∘ₗ (lcoeff R F).rTensor _ =
      LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
        TensorProduct.map (graft lbl) LinearMap.id ∘ₗ
        TensorProduct.map (matchForest F) LinearMap.id :=
    TensorProduct.ext' fun a b ↦ by simp [matchForest]
  exact congrArg (fun g ↦ g ∘ₗ Δ) h

theorem mergeAlong_pair_apply (S S' : UnorderedTree α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    mergeAlong Δ lbl {S, S'} x =
      ofTree (.node lbl {S, S'}) * contractAlong Δ (lcoeff R {S, S'}) x := by
  rw [mergeAlong_apply, graft_of'_pair]

/-- At a single tree `β`, Merge is multiplication by `β` after contraction with `{β}`, whatever
    the label. -/
theorem mergeAlong_singleton (β : UnorderedTree α) :
    mergeAlong Δ lbl {β} = LinearMap.mulLeft R (ofTree β) ∘ₗ
      contractAlong Δ (lcoeff R ({β} : Forest (UnorderedTree α))) := by
  rw [mergeAlong, of'_singleton, graft_ofTree]

end MergeAlong

/-! ### Merge over a cut enumeration -/

/-- Merge `M_{S,S'}` over a cut enumeration `cuts`, whose coproduct is `comulOfCuts cuts`. -/
noncomputable def mergeOpOfCuts (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α))
    (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergeAlong (comulOfCuts cuts).toLinearMap lbl {S, S'}

/-- The unit stage `M_{β,1}` over a cut enumeration `cuts`. -/
noncomputable def mergeOpUnitOfCuts (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mulLeft R (ofTree β) ∘ₗ contractForest cuts {β}

/-- The Merge operator `M_{S,S'}` of [marcolli-chomsky-berwick-2025] Definition 1.3.4, Merge at
    the deletion coproduct `Δ^d`. The label `lbl` is that of the vertices with children: Merge
    gives it to the new root, and the deletion removes the vertices so labelled that are left
    without a child. -/
noncomputable def mergeOp [DecidableEq α] (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergeAlong (deletionComulAlgHom lbl).toLinearMap lbl {S, S'}

/-- The unit stage `M_{β,1}` at the deletion coproduct, the operator of Definition 1.3.4 that
    Proposition 1.4.2 composes with External Merge. -/
noncomputable def mergeOpUnit [DecidableEq α] (lbl : α) (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mulLeft R (ofTree β) ∘ₗ
    contractAlong (deletionComulAlgHom lbl).toLinearMap
      (lcoeff R ({β} : Forest (UnorderedTree α)))

section Cuts

variable (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))

/-- Merge `M_{S,S'}` over a cut enumeration is multiplication by the grafted pair after
    contraction of the coproduct with the forest `{S, S'}`. -/
theorem mergeOpOfCuts_eq_mul_contractForest (lbl : α) (S S' : UnorderedTree α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' x =
      ofTree (UnorderedTree.node lbl {S, S'}) * contractForest cuts {S, S'} x :=
  mergeAlong_pair_apply _ lbl S S' x

/-- The unit stage `M_{β,1}` over a cut enumeration is multiplication by `β` after contraction of
    the coproduct with the forest `{β}`. -/
theorem mergeOpUnitOfCuts_eq_mul_contractForest (β : UnorderedTree α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    mergeOpUnitOfCuts (R := R) cuts β x = ofTree β * contractForest cuts {β} x :=
  rfl

/-- The unit stage is Merge at the forest `{β}`. -/
theorem mergeAlong_comulOfCuts_singleton (lbl : α) (β : UnorderedTree α) :
    mergeAlong (comulOfCuts (R := R) cuts).toLinearMap lbl {β} = mergeOpUnitOfCuts cuts β :=
  mergeAlong_singleton _ lbl β

/-- Merge does not depend on the order of the pair. -/
theorem mergeOpOfCuts_comm (lbl : α) (S S' : UnorderedTree α) :
    mergeOpOfCuts (R := R) cuts lbl S S' = mergeOpOfCuts cuts lbl S' S := by
  simp only [mergeOpOfCuts, Multiset.pair_comm S S']

/-- The unit stage vanishes on the empty workspace, which has no `β` to extract. -/
theorem mergeOpUnitOfCuts_one (β : UnorderedTree α) :
    mergeOpUnitOfCuts (R := R) cuts β 1 = 0 := by
  classical
  have h : (1 : ConnesKreimer R (UnorderedTree α)).coeff {β} = 0 := by
    rw [← of'_zero, coeff_of', ite_eq_right (Multiset.singleton_ne_zero β).symm]
  simp [mergeOpUnitOfCuts_eq_mul_contractForest, contractForest, contractAlong_apply,
    Algebra.TensorProduct.one_def, h]

variable [DecidableEq (UnorderedTree α)]

/-- Merge on a workspace `F` grafts `{S, S'}` beside the trunk of each forest cut of `F` with crown
    `{S, S'}` ([marcolli-chomsky-berwick-2025] (1.3.11)). -/
theorem mergeOpOfCuts_apply_of' (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' F) = of' {UnorderedTree.node lbl {S, S'}} *
      (((forestCuts cuts F).filter (·.1 = {S, S'})).map fun p ↦ of' (R := R) p.2).sum := by
  rw [mergeOpOfCuts_eq_mul_contractForest, contractForest_of', of'_singleton]

/-- Merge on a workspace `F` is a sum of workspaces, one for each choice of a cut of each tree of
    `F` whose crowns together are `{S, S'}`. -/
theorem mergeOpOfCuts_apply_of'_eq_sum (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' F) =
      (((forestCutChoices cuts F).filter (·.crown = {S, S'})).map
        fun s ↦ of' ({UnorderedTree.node lbl {S, S'}} + s.trunk)).sum := by
  rw [mergeOpOfCuts_apply_of', forestCuts_eq_map_forestCutChoices, Multiset.filter_map,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  simp only [Function.comp_def, of'_add]

/-- The unit stage on a workspace `F` puts `β` beside the trunk of each forest cut of `F` with
    crown `{β}`. -/
theorem mergeOpUnitOfCuts_apply_of' (β : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    mergeOpUnitOfCuts (R := R) cuts β (of' F) =
      (((forestCuts cuts F).filter (·.1 = {β})).map fun p ↦ of' ({β} + p.2)).sum := by
  rw [mergeOpUnitOfCuts_eq_mul_contractForest, contractForest_of', ← of'_singleton,
    ← Multiset.sum_map_mul_left]
  simp only [of'_add]

/-- The unit stage on a workspace `F` is a sum of workspaces, one for each choice of a cut of each
    tree of `F` whose crowns together are `{β}`. -/
theorem mergeOpUnitOfCuts_apply_of'_eq_sum (β : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    mergeOpUnitOfCuts (R := R) cuts β (of' F) =
      (((forestCutChoices cuts F).filter (·.crown = {β})).map
        fun s ↦ of' ({β} + s.trunk)).sum := by
  rw [mergeOpUnitOfCuts_apply_of', forestCuts_eq_map_forestCutChoices, Multiset.filter_map,
    Multiset.map_map]
  rfl

end Cuts

/-! ### Deletion and admissible cuts

Merge at the deletion coproduct reaches the Connes–Kreimer coproduct through the projection
`Π_{d,ρ}` of the right channel, `deletionProj`. Contraction is natural in the right channel, and
the projection is an algebra map, so it commutes with Merge once it fixes the grafted tree. -/

section Contraction

variable [DecidableEq α]

/-- Merge at `Δ^d` is Merge along `(id ⊗ Π_{d,ρ}) ∘ Δ^ρ`, the Connes–Kreimer coproduct with its
    remainder projected ([marcolli-chomsky-berwick-2025] (1.3.10)). -/
theorem mergeOp_eq_mergeAlong_comulAlgHom (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' = mergeAlong
      (TensorProduct.map LinearMap.id (deletionProj (R := R) lbl).toLinearMap ∘ₗ
        (comulAlgHom (R := R) (α := α)).toLinearMap) lbl {S, S'} := rfl

/-- On trees that are their own remainders, Merge at the deletion coproduct is Merge at the
    admissible cuts followed by the projection `Π_{d,ρ}` of the workspace. -/
theorem mergeOp_eq_deletionProj_comp (lbl : α) {S S' : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) (hS' : deletionQuotient lbl S' = some S') :
    mergeOp (R := R) lbl S S' = (deletionProj (R := R) lbl).toLinearMap ∘ₗ
      mergeOpOfCuts (R := R) admissibleCuts lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  rw [mergeOp_eq_mergeAlong_comulAlgHom, mergeAlong_pair_apply, contractAlong_map_comp,
    LinearMap.comp_id, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, mergeOpOfCuts_eq_mul_contractForest, map_mul, deletionProj_ofTree,
    deletionQuotient_node_pair lbl hS hS', Option.elim_some]
  rfl

/-- On a tree that is its own remainder, the unit stage at the deletion coproduct is the unit
    stage at the admissible cuts followed by the projection `Π_{d,ρ}` of the workspace. -/
theorem mergeOpUnit_eq_deletionProj_comp (lbl : α) {β : UnorderedTree α}
    (hβ : deletionQuotient lbl β = some β) :
    mergeOpUnit (R := R) lbl β = (deletionProj (R := R) lbl).toLinearMap ∘ₗ
      mergeOpUnitOfCuts (R := R) admissibleCuts β := by
  refine LinearMap.ext fun x ↦ ?_
  show ofTree β * contractAlong (TensorProduct.map LinearMap.id
      (deletionProj (R := R) lbl).toLinearMap ∘ₗ (comulAlgHom (R := R) (α := α)).toLinearMap)
      (lcoeff R {β}) x = _
  rw [contractAlong_map_comp, LinearMap.comp_id, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, mergeOpUnitOfCuts_eq_mul_contractForest,
    map_mul, deletionProj_ofTree, hβ, Option.elim_some]
  rfl

end Contraction

/-! ### Merge at the trace cuts -/

/-- The trace Merge operator is Merge at the trace cuts `markerCuts τ`, whose trunks carry a
    trace leaf at each cut site. -/
noncomputable def traceMergeOp {β : Type*}
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpOfCuts (R := R) (markerCuts τ) lbl S S'

/-- The unit stage `M_{S,1}` at the trace cuts `markerCuts τ`. -/
noncomputable def traceMergeOpUnit {β : Type*}
    (τ : UnorderedTree (α ⊕ β) → β) (S : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpUnitOfCuts (R := R) (markerCuts τ) S

/-! ### Erasing the traces of Merge

The embedding of the trees without traces is a section of the erasure `eraseTraces`, and the
coefficient of an embedded forest in an embedded element is the coefficient of the forest in the
element. So erasure carries the contraction of the trace coproduct with an embedded forest to the
contraction of the Connes–Kreimer coproduct with the forest, and the relations between the
coproducts pass to Merge. -/

section Erasure

variable {β : Type*} (τ : UnorderedTree (α ⊕ β) → β)

/-- The embedding of the trees without traces into the trees with traces. -/
local notation "ι" => rename (R := R) (UnorderedTree.map (Sum.inl : α → α ⊕ β))

/-- The projection `Π_{d,c}`: erase the traces, then project by `Π_{d,ρ}`. -/
local notation "Π_dc[" l "]" => AlgHom.comp (deletionProj (R := R) (α := α) l)
  (eraseTraces (R := R) (α := α) (β := β))

omit τ in
private theorem eraseTraces_ofTree_map_inl (T : UnorderedTree α) :
    eraseTraces (R := R) (β := β) (ofTree (T.map Sum.inl)) = ofTree T := by
  simp

/-- Erasure carries the contraction of `Δ^c` with an embedded forest, on embedded elements, to
    the contraction of `Δ^ρ` with the forest. -/
private theorem eraseTraces_comp_contractForest_markerCuts (F : Forest (UnorderedTree α)) :
    eraseTraces.toLinearMap ∘ₗ
        contractForest (R := R) (markerCuts τ) (F.map (UnorderedTree.map Sum.inl)) ∘ₗ
        (ι).toLinearMap =
      contractForest admissibleCuts F := by
  have h : TensorProduct.map LinearMap.id (eraseTraces (R := R) (α := α) (β := β)).toLinearMap ∘ₗ
      (markerComulAlgHom τ).toLinearMap ∘ₗ (ι).toLinearMap =
      TensorProduct.map (ι).toLinearMap LinearMap.id ∘ₗ
        (comulAlgHom (R := R) (α := α)).toLinearMap :=
    congrArg AlgHom.toLinearMap (eraseTraces_markerComulAlgHom (R := R) τ)
  calc _ = contractAlong (TensorProduct.map LinearMap.id
          (eraseTraces (R := R) (α := α) (β := β)).toLinearMap ∘ₗ
          (markerComulAlgHom τ).toLinearMap ∘ₗ (ι).toLinearMap)
          (lcoeff R (F.map (UnorderedTree.map Sum.inl))) :=
        (contractAlong_map_comp _ LinearMap.id _ _).symm
    _ = contractAlong (comulAlgHom (R := R) (α := α)).toLinearMap
          (lcoeff R (F.map (UnorderedTree.map Sum.inl)) ∘ₗ (ι).toLinearMap) := by
        rw [h]; exact contractAlong_map_comp _ _ LinearMap.id _
    _ = _ := by
        rw [lcoeff_map_comp_rename (UnorderedTree.map_injective Sum.inl_injective)]; rfl

/-- Erasing the traces of Merge at the trace cuts gives Merge at the admissible cuts, on trees
    without traces. -/
theorem eraseTraces_comp_traceMergeOp (lbl : α) (S S' : UnorderedTree α) :
    eraseTraces.toLinearMap ∘ₗ
        traceMergeOp (R := R) τ (Sum.inl lbl) (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ (ι).toLinearMap =
      mergeOpOfCuts admissibleCuts lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  have hpair : ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β))) =
      ({S, S'} : Forest (UnorderedTree α)).map (UnorderedTree.map Sum.inl) := by simp
  have h := LinearMap.congr_fun (eraseTraces_comp_contractForest_markerCuts (R := R) τ {S, S'}) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at h
  simp only [LinearMap.comp_apply, traceMergeOp, mergeOpOfCuts_eq_mul_contractForest, hpair,
    AlgHom.toLinearMap_apply, map_mul]
  exact congrArg₂ (· * ·) (by rw [← UnorderedTree.map_node, eraseTraces_ofTree_map_inl]) h

/-- Erasing the traces of the unit stage at the trace cuts gives the unit stage at the admissible
    cuts, on trees without traces. -/
theorem eraseTraces_comp_traceMergeOpUnit (S : UnorderedTree α) :
    eraseTraces.toLinearMap ∘ₗ traceMergeOpUnit (R := R) τ (S.map Sum.inl) ∘ₗ (ι).toLinearMap =
      mergeOpUnitOfCuts admissibleCuts S := by
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (eraseTraces_comp_contractForest_markerCuts (R := R) τ {S}) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Multiset.map_singleton] at h
  simp only [LinearMap.comp_apply, traceMergeOpUnit, mergeOpUnitOfCuts_eq_mul_contractForest,
    AlgHom.toLinearMap_apply, map_mul]
  exact congrArg₂ (· * ·) (eraseTraces_ofTree_map_inl S) h

variable [DecidableEq α]

/-- Merge at `Δ^d` through the trace coproduct, the second expression of
    [marcolli-chomsky-berwick-2025] (1.3.10): the contraction of `(id ⊗ Π_{d,c}) ∘ Δ^c` on the
    embedded tree with the embedded pair, multiplied by the pair grafted among the trees without
    traces. -/
theorem mergeOp_eq_comp_markerComulAlgHom (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' =
      LinearMap.mulLeft R (ofTree (UnorderedTree.node lbl {S, S'})) ∘ₗ
      contractAlong (TensorProduct.map LinearMap.id (Π_dc[lbl]).toLinearMap ∘ₗ
          (markerComulAlgHom τ).toLinearMap ∘ₗ (ι).toLinearMap)
        (lcoeff R ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β)))) := by
  have h : TensorProduct.map LinearMap.id (Π_dc[lbl]).toLinearMap ∘ₗ
      (markerComulAlgHom τ).toLinearMap ∘ₗ (ι).toLinearMap =
      TensorProduct.map (ι).toLinearMap LinearMap.id ∘ₗ
        (deletionComulAlgHom (R := R) (α := α) lbl).toLinearMap :=
    congrArg AlgHom.toLinearMap (deletionProj_eraseTraces_markerComulAlgHom (R := R) lbl τ)
  have hpair : ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β))) =
      ({S, S'} : Forest (UnorderedTree α)).map (UnorderedTree.map Sum.inl) := by simp
  refine LinearMap.ext fun x ↦ ?_
  rw [h, hpair, contractAlong_map_comp,
    lcoeff_map_comp_rename (UnorderedTree.map_injective Sum.inl_injective), LinearMap.id_comp,
    LinearMap.comp_apply, LinearMap.mulLeft_apply]
  exact mergeAlong_pair_apply _ lbl S S' x

/-- On trees that are their own remainders, Merge at the deletion coproduct is the projection
    `Π_{d,c}` of Merge at the trace cuts. -/
theorem mergeOp_eq_comp_traceMergeOp (lbl : α) {S S' : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) (hS' : deletionQuotient lbl S' = some S') :
    mergeOp (R := R) lbl S S' = (Π_dc[lbl]).toLinearMap ∘ₗ
      traceMergeOp τ (Sum.inl lbl : α ⊕ β) (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ (ι).toLinearMap := by
  rw [mergeOp_eq_deletionProj_comp lbl hS hS', ← eraseTraces_comp_traceMergeOp τ]
  rfl

/-- On a tree that is its own remainder, the unit stage at the deletion coproduct is the
    projection `Π_{d,c}` of the unit stage at the trace cuts: the remainder `T/d T_v` that the book
    sends to Externalization is `Π_{d,c}` of the remainder `T/c T_v` that it sends to semantic
    interpretation ([marcolli-chomsky-berwick-2025] p. 82). -/
theorem mergeOpUnit_eq_comp_traceMergeOpUnit (lbl : α) {S : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) :
    mergeOpUnit (R := R) lbl S =
      (Π_dc[lbl]).toLinearMap ∘ₗ traceMergeOpUnit τ (S.map Sum.inl) ∘ₗ (ι).toLinearMap := by
  rw [mergeOpUnit_eq_deletionProj_comp lbl hS, ← eraseTraces_comp_traceMergeOpUnit τ]
  rfl

end Erasure

end Minimalist.Merge
