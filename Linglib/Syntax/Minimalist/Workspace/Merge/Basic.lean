module

public import Linglib.Core.Algebra.RootedTree.Coproduct.AdmissibleCut
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
that coproduct; `traceMergeOp` is Merge at the trace cuts. The unit stage `M_{β,1}` of Internal
Merge (Proposition 1.4.2) has no grafting step (`mergeOpUnitOfCuts`).

On a workspace `F`, Merge grafts `{S, S'}` beside the trunk of each forest cut of `F` whose crown
is `{S, S'}`, summed over all such cuts (`mergeOpOfCuts_apply_of'`, the book's (1.3.11)). Each form
of Merge in their §1.4 is this sum on a particular workspace.

External, Internal and Sideward Merge are in `Merge/External.lean`, `Merge/Internal.lean` and
`Merge/Sideward.lean`; the Minimal-Search weighting is in `Merge/MinimalSearch.lean`.

## Main definitions

* `Minimalist.Merge.mergeOpOfCuts`, `mergeOp`, `traceMergeOp`: Merge over a cut enumeration, at the
  deletion coproduct, and at the trace cuts.
* `Minimalist.Merge.mergeOpUnitOfCuts`, `mergeOpUnit`, `traceMergeOpUnit`: the unit stage `M_{β,1}`.
* `Minimalist.Merge.IsMergeCuts`: cut enumerations whose nonempty crowns have fewer edges than
  their tree.

## Main results

* `Minimalist.Merge.mergeOpOfCuts_apply_of'`, `mergeOpOfCuts_apply_of'_eq_sum`: Merge on a workspace
  is a sum over its forest cuts, or over a choice of cut for each of its trees.
* `Minimalist.Merge.mergeOpOfCuts_comm`: Merge does not depend on the order of the pair.
* `Minimalist.Merge.mergeOp_eq_comp_comulAlgHom`, `mergeOp_eq_comp_markerComulAlgHom`: Merge at
  `Δ^d` through the Connes–Kreimer coproduct and through the trace coproduct, the two expressions
  of the book's (1.3.10).
* `Minimalist.Merge.mergeOp_eq_deletionProj_comp`, `mergeOpUnit_eq_deletionProj_comp`: on
  objects that are their own remainders, Merge at the deletion coproduct is Merge at the
  admissible cuts followed by the projection `Π_{d,ρ}`.
* `Minimalist.Merge.eraseTraces_comp_traceMergeOp`, `mergeOp_eq_comp_traceMergeOp`,
  `mergeOpUnit_eq_comp_traceMergeOpUnit`: on trees without traces, erasing the traces of Merge at
  the trace cuts gives Merge at the admissible cuts, and projecting too gives Merge at the
  deletion coproduct.

## Implementation notes

Definition 1.3.4 fixes the deletion coproduct `Δ^d`, which reduces the remainder of a cut to a
binary tree, and `mergeOp` is Merge at that coproduct. The Connes–Kreimer coproduct `Δ^ρ` keeps the
remainder as it is. The two extract the same accessible terms, but `⊔` multiplies the remainder
into the result, so Merge at the admissible cuts (`mergeOpOfCuts admissibleCuts`) is not the book's
operator: its Internal Merge leaves a unary vertex, which no syntactic object has. The book writes
(1.3.7) through `Δ^ρ` only with the right channel projected after the matching
(`mergeOp_eq_comp_comulAlgHom`).

The chain `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}` after the coproduct is defined as one map, `mergePost`:
contraction of the left channel with the coefficient functional of the forest `{S, S'}`, then
multiplication by the tree `node lbl {S, S'}`. The matching `γ_{S,S'}` and the grafting `B` are
not separate declarations. An algebra map then commutes with the chain when it sends the grafted
tree to the grafted tree, and the product rule for contractions (`contractForest_mul`) applies to
Merge (`mergeOpOfCuts_eq_mul_contractForest` in `Merge/External.lean`).

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

/-- A cut enumeration admits Merge when its crowns are subtrees with fewer edges in total than
    their tree, and its only empty cut is the tree itself. The edge bound makes External Merge of
    a pair exact (`mergeOpOfCuts_pair`); the other two let a spectator component pass through
    (`mergeOpOfCuts_ofTree_mul`). -/
class IsMergeCuts
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)) : Prop where
  crown_numEdges_lt {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α} :
    p ∈ cuts T → p.1 ≠ 0 → (p.1.map numEdges).sum < T.numEdges
  mem_subtrees_of_mem_crown {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α}
    {x : UnorderedTree α} : p ∈ cuts T → x ∈ p.1 → x ∈ T.subtrees
  filter_empty (T : UnorderedTree α) : (cuts T).filter (fun p ↦ p.1.card = 0) = {(0, T)}

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

/-! ### Contraction of the left channel

Contraction of the left channel with a functional `f`, the map `z ↦ lid ((f ⊗ id) z)`, is natural
in both channels. -/

section Channels

variable {A A' B C : Type*} [CommSemiring A] [Algebra R A] [CommSemiring A'] [Algebra R A']
  [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- Contraction of the left channel after a pair of algebra maps is the right map after
    contraction with the functional pulled back along the left map. -/
private theorem lid_rTensor_map (f : A →ₗ[R] R) (g : A' →ₐ[R] A) (φ : B →ₐ[R] C)
    (z : A' ⊗[R] B) :
    TensorProduct.lid R C (f.rTensor C (Algebra.TensorProduct.map g φ z)) =
      φ (TensorProduct.lid R B ((f ∘ₗ g.toLinearMap).rTensor B z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

end Channels

/-! ### The chain after the coproduct

After the coproduct, Merge applies `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}`. The matching
`δ_{S,S'} = γ_{S,S'} ⊗ id` (Definition 1.3.1) keeps the terms whose left channel is the forest
`{S, S'}`, the grafting `B` (Definition 1.3.2) sends that forest to the tree `node lbl {S, S'}`,
and `⊔` multiplies the channels. So the chain contracts the left channel with the coefficient of
`{S, S'}` and multiplies what is left of the right channel by the grafted tree. -/

/-- The post-coproduct chain `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}`, shared by every coproduct: contraction of
    the left channel with the coefficient of `{S, S'}`, then multiplication by the tree
    `node lbl {S, S'}`. -/
noncomputable def mergePost (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mulLeft R (ofTree (UnorderedTree.node lbl {S, S'})) ∘ₗ
    (TensorProduct.lid R _).toLinearMap ∘ₗ
      (lcoeff R ({S, S'} : Forest (UnorderedTree α))).rTensor _

/-! ### The unit stage `M_{β,1}`

The first stage of Internal Merge (Proposition 1.4.2) moves an accessible term `β` to the left
channel and leaves `T/β` on the right. Its grafting step is the identity, since
`B(β ⊔ 1) = M(β, 1) = β`. It is not a Merge in its own right: it occurs only composed with
`M_{T/β,β}` ([marcolli-chomsky-berwick-2025] Remark 1.4.3). -/

/-- The post-coproduct chain `⊔ ∘ δ_{β,1}` of the unit stage: contraction of the left channel
    with the coefficient of `{β}`, then multiplication by `β`. -/
noncomputable def mergePostUnit (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mulLeft R (ofTree β) ∘ₗ (TensorProduct.lid R _).toLinearMap ∘ₗ
    (lcoeff R ({β} : Forest (UnorderedTree α))).rTensor _

section DecidableEq

variable [DecidableEq (UnorderedTree α)]

/-- On a basis tensor `of' F ⊗ r`, the post-coproduct chain grafts `F` if it is `{S, S'}` and
    vanishes otherwise. -/
theorem mergePost_basis_tensor (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (r : ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S' (of' F ⊗ₜ[R] r)
      = if F = ({S, S'} : Forest (UnorderedTree α))
          then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) * r
          else 0 := by
  simp [mergePost, coeff_of', of'_singleton]

theorem mergePostUnit_basis_tensor (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (r : ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) (α := α) β (of' F ⊗ₜ[R] r)
      = if F = ({β} : Forest (UnorderedTree α))
          then of' ({β} : Forest (UnorderedTree α)) * r
          else 0 := by
  simp [mergePostUnit, coeff_of', of'_singleton]

/-! ### Merge over a cut enumeration -/

/-- Merge `M_{S,S'}` over a cut enumeration `cuts`, whose coproduct is `comulOfCuts cuts`. -/
noncomputable def mergeOpOfCuts (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α))
    (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ (comulOfCuts cuts).toLinearMap

/-- The unit stage `M_{β,1}` over a cut enumeration `cuts`. -/
noncomputable def mergeOpUnitOfCuts (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePostUnit (R := R) (α := α) β ∘ₗ (comulOfCuts cuts).toLinearMap

/-- The Merge operator `M_{S,S'}` of [marcolli-chomsky-berwick-2025] Definition 1.3.4, Merge at
    the deletion coproduct `Δ^d`. The label `lbl` is that of the vertices with children: Merge
    gives it to the new root, and the deletion removes the vertices so labelled that are left
    without a child. -/
noncomputable def mergeOp [DecidableEq α] (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ (deletionComulAlgHom lbl).toLinearMap

/-- The unit stage `M_{β,1}` at the deletion coproduct, the operator of Definition 1.3.4 that
    Proposition 1.4.2 composes with External Merge. -/
noncomputable def mergeOpUnit [DecidableEq α] (lbl : α) (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePostUnit (R := R) (α := α) β ∘ₗ (deletionComulAlgHom lbl).toLinearMap

/-- Merge on a workspace `F` grafts `{S, S'}` beside the trunk of each forest cut of `F` with crown
    `{S, S'}` ([marcolli-chomsky-berwick-2025] (1.3.11)). -/
theorem mergeOpOfCuts_apply_of' (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' F) = of' {UnorderedTree.node lbl {S, S'}} *
      (((forestCuts cuts F).filter (·.1 = {S, S'})).map fun p ↦ of' (R := R) p.2).sum := by
  rw [mergeOpOfCuts, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulOfCuts_apply_of',
    comulForestOfCuts_eq_sum, map_multiset_sum, Multiset.map_map, Multiset.sum_map_filter,
    ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  rw [Function.comp_apply, cutTensor, mergePost_basis_tensor, mul_ite, mul_zero]

/-- Merge on a workspace `F` is a sum of workspaces, one for each choice of a cut of each tree of
    `F` whose crowns together are `{S, S'}`. -/
theorem mergeOpOfCuts_apply_of'_eq_sum (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    mergeOpOfCuts (R := R) cuts lbl S S' (of' F) =
      (((forestCutChoices cuts F).filter (·.crown = {S, S'})).map
        fun s ↦ of' ({UnorderedTree.node lbl {S, S'}} + s.trunk)).sum := by
  rw [mergeOpOfCuts_apply_of', forestCuts_eq_map_forestCutChoices, Multiset.filter_map,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  simp only [Function.comp_def, of'_add]

/-- The unit stage on a workspace `F` is a sum of workspaces, one for each choice of a cut of each
    tree of `F` whose crowns together are `{β}`. -/
theorem mergeOpUnitOfCuts_apply_of'_eq_sum (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    mergeOpUnitOfCuts (R := R) cuts β (of' F) =
      (((forestCutChoices cuts F).filter (·.crown = {β})).map
        fun s ↦ of' ({β} + s.trunk)).sum := by
  rw [mergeOpUnitOfCuts, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulOfCuts_apply_of',
    comulForestOfCuts_eq_sum, forestCuts_eq_map_forestCutChoices, Multiset.map_map,
    map_multiset_sum, Multiset.map_map, Multiset.sum_map_filter]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ ↦ ?_)
  simp only [Function.comp_apply, cutTensor, mergePostUnit_basis_tensor]
  split_ifs
  · rw [← of'_add]
  · simp

/-- The unit stage on a workspace `F` puts `β` beside the trunk of each forest cut of `F` with
    crown `{β}`. -/
theorem mergeOpUnitOfCuts_apply_of' (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    mergeOpUnitOfCuts (R := R) cuts β (of' F) =
      (((forestCuts cuts F).filter (·.1 = {β})).map fun p ↦ of' ({β} + p.2)).sum := by
  rw [mergeOpUnitOfCuts_apply_of'_eq_sum, forestCuts_eq_map_forestCutChoices, Multiset.filter_map,
    Multiset.map_map]
  rfl

omit [DecidableEq (UnorderedTree α)] in
/-- Merge does not depend on the order of the pair. -/
theorem mergeOpOfCuts_comm (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α) :
    mergeOpOfCuts (R := R) cuts lbl S S' = mergeOpOfCuts cuts lbl S' S := by
  simp only [mergeOpOfCuts, mergePost,
    Multiset.pair_comm S S']

/-- The unit stage vanishes on the empty workspace, which has no `β` to extract. -/
theorem mergeOpUnitOfCuts_one (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    mergeOpUnitOfCuts (R := R) cuts β 1 = 0 := by
  rw [mergeOpUnitOfCuts, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
    Algebra.TensorProduct.one_def, ← of'_zero, mergePostUnit_basis_tensor,
    ite_eq_right (Multiset.singleton_ne_zero β).symm]


/-! ### Deletion and admissible cuts

Merge at the deletion coproduct reaches the Connes–Kreimer coproduct through the projection
`Π_{d,ρ}` of the right channel, `deletionProj`. The projection is an algebra map, so it commutes
with the chain after the coproduct once it fixes the tree that the chain multiplies by. -/

section Contraction

variable [DecidableEq α]

omit [DecidableEq (UnorderedTree α)] in
/-- Merge at `Δ^d` is `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ (id ⊗ Π_{d,ρ}) ∘ Δ^ρ`, the Connes–Kreimer
    coproduct with its remainder projected ([marcolli-chomsky-berwick-2025] (1.3.10)). The
    matching and the projection act on different channels, so their order does not matter. -/
theorem mergeOp_eq_comp_comulAlgHom (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' = mergePost lbl S S' ∘ₗ
      (Algebra.TensorProduct.map (.id R _) (deletionProj (R := R) lbl)).toLinearMap ∘ₗ
      (comulAlgHom (R := R) (α := α)).toLinearMap := rfl

omit [DecidableEq (UnorderedTree α)] in
/-- On trees that are their own remainders, Merge at the deletion coproduct is Merge at the
    admissible cuts followed by the projection `Π_{d,ρ}` of the workspace. -/
theorem mergeOp_eq_deletionProj_comp (lbl : α) {S S' : UnorderedTree α}
    (hS : deletionQuotient lbl S = some S) (hS' : deletionQuotient lbl S' = some S') :
    mergeOp (R := R) lbl S S' = (deletionProj (R := R) lbl).toLinearMap ∘ₗ
      mergeOpOfCuts (R := R) admissibleCuts lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOp_eq_comp_comulAlgHom, mergeOpOfCuts, mergePost, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply, lid_rTensor_map,
    map_mul, deletionProj_ofTree, deletionQuotient_node_pair lbl hS hS', Option.elim_some]
  rfl

omit [DecidableEq (UnorderedTree α)] in
/-- On a tree that is its own remainder, the unit stage at the deletion coproduct is the unit
    stage at the admissible cuts followed by the projection `Π_{d,ρ}` of the workspace. -/
theorem mergeOpUnit_eq_deletionProj_comp (lbl : α) {β : UnorderedTree α}
    (hβ : deletionQuotient lbl β = some β) :
    mergeOpUnit (R := R) lbl β = (deletionProj (R := R) lbl).toLinearMap ∘ₗ
      mergeOpUnitOfCuts (R := R) admissibleCuts β := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOpUnit, mergeOpUnitOfCuts, mergePostUnit, deletionComulAlgHom,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, LinearEquiv.coe_coe,
    LinearMap.mulLeft_apply, lid_rTensor_map, map_mul, deletionProj_ofTree, hβ, Option.elim_some]
  rfl

end Contraction

end DecidableEq

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
element. So erasure carries the chain of Merge at an embedded pair to the chain at the pair, and
the relations between the coproducts pass to Merge. -/

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

/-- Erasure carries the contraction of `Δ^c` with an embedded forest, on an embedded element, to
    the contraction of `Δ^ρ` with the forest. -/
private theorem eraseTraces_lid_rTensor_markerComulAlgHom (F : Forest (UnorderedTree α))
    (x : ConnesKreimer R (UnorderedTree α)) :
    eraseTraces (R := R) (TensorProduct.lid R _
        ((lcoeff R (F.map (UnorderedTree.map Sum.inl))).rTensor _ (markerComulAlgHom τ (ι x)))) =
      TensorProduct.lid R _ ((lcoeff R F).rTensor _ (comulAlgHom x)) := by
  have h := DFunLike.congr_fun (eraseTraces_markerComulAlgHom (R := R) τ) x
  simp only [AlgHom.comp_apply] at h
  calc _ = TensorProduct.lid R _ ((lcoeff R (F.map (UnorderedTree.map Sum.inl))).rTensor _
          (Algebra.TensorProduct.map (.id R _) eraseTraces (markerComulAlgHom τ (ι x)))) :=
        (lid_rTensor_map _ (.id R _) eraseTraces _).symm
    _ = _ := by
      rw [h, lid_rTensor_map,
        lcoeff_map_comp_rename (UnorderedTree.map_injective Sum.inl_injective)]
      rfl

/-- Erasing the traces of Merge at the trace cuts gives Merge at the admissible cuts, on trees
    without traces. -/
theorem eraseTraces_comp_traceMergeOp (lbl : α) (S S' : UnorderedTree α) :
    eraseTraces.toLinearMap ∘ₗ
        traceMergeOp (R := R) τ (Sum.inl lbl) (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ (ι).toLinearMap =
      mergeOpOfCuts admissibleCuts lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  have hpair : ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β))) =
      ({S, S'} : Forest (UnorderedTree α)).map (UnorderedTree.map Sum.inl) := by simp
  have h := eraseTraces_lid_rTensor_markerComulAlgHom (R := R) τ {S, S'} x
  simp only [LinearMap.comp_apply, traceMergeOp, mergeOpOfCuts, mergePost, hpair,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply, map_mul]
  exact congrArg₂ (· * ·) (by rw [← UnorderedTree.map_node, eraseTraces_ofTree_map_inl]) h

/-- Erasing the traces of the unit stage at the trace cuts gives the unit stage at the admissible
    cuts, on trees without traces. -/
theorem eraseTraces_comp_traceMergeOpUnit (S : UnorderedTree α) :
    eraseTraces.toLinearMap ∘ₗ traceMergeOpUnit (R := R) τ (S.map Sum.inl) ∘ₗ (ι).toLinearMap =
      mergeOpUnitOfCuts admissibleCuts S := by
  refine LinearMap.ext fun x ↦ ?_
  have h := eraseTraces_lid_rTensor_markerComulAlgHom (R := R) τ {S} x
  rw [Multiset.map_singleton] at h
  simp only [LinearMap.comp_apply, traceMergeOpUnit, mergeOpUnitOfCuts, mergePostUnit,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply, map_mul]
  exact congrArg₂ (· * ·) (eraseTraces_ofTree_map_inl S) h

variable [DecidableEq α]

/-- Merge at `Δ^d` through the trace coproduct, the second expression of
    [marcolli-chomsky-berwick-2025] (1.3.10): `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ (id ⊗ Π_{d,c}) ∘ Δ^c`. The
    chain runs on the embedded tree: the left channel is matched against the embedded pair, and
    the pair is grafted among the trees without traces. -/
theorem mergeOp_eq_comp_markerComulAlgHom (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' =
      LinearMap.mulLeft R (ofTree (UnorderedTree.node lbl {S, S'})) ∘ₗ
      (TensorProduct.lid R _).toLinearMap ∘ₗ
      (lcoeff R ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β)))).rTensor _ ∘ₗ
      (Algebra.TensorProduct.map (.id R _) Π_dc[lbl]).toLinearMap ∘ₗ
      (markerComulAlgHom τ).toLinearMap ∘ₗ (ι).toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  have h := DFunLike.congr_fun (deletionProj_eraseTraces_markerComulAlgHom (R := R) lbl τ) x
  simp only [AlgHom.comp_apply] at h
  have hpair : ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β))) =
      ({S, S'} : Forest (UnorderedTree α)).map (UnorderedTree.map Sum.inl) := by simp
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, h, hpair,
    lid_rTensor_map, lcoeff_map_comp_rename (UnorderedTree.map_injective Sum.inl_injective)]
  rfl

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
