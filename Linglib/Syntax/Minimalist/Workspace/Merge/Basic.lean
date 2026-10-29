module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Data.UnorderedTree.Count
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.Deletion
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceCut
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
`cuts` (`mergeOpG`). The book's `Δ` is the deletion coproduct `Δ^d`, and `mergeOp` is Merge at the
deletion cuts; `mergeOpC` is Merge at the trace cuts. The unit stage `M_{β,1}` of Internal Merge
(Proposition 1.4.2) has no grafting step (`mergeOpUnitG`).

On a workspace `F`, Merge grafts `{S, S'}` beside the trunk of each forest cut of `F` whose crown
is `{S, S'}`, summed over all such cuts (`mergeOpG_apply_of'`, the book's (1.3.11)). Each form of
Merge in their §1.4 is this sum on a particular workspace.

External, Internal and Sideward Merge are in `Merge/External.lean`, `Merge/Internal.lean` and
`Merge/Sideward.lean`; the Minimal-Search weighting is in `Merge/MinimalSearch.lean`.

## Main definitions

* `Minimalist.Merge.mergeOpG`, `mergeOp`, `mergeOpC`: Merge over a cut enumeration, at the
  deletion cuts, and at the trace cuts.
* `Minimalist.Merge.mergeOpUnitG`, `mergeOpUnit`, `mergeOpUnitC`: the unit stage `M_{β,1}`.
* `Minimalist.Merge.IsMergeCuts`: cut enumerations whose nonempty crowns have fewer edges than
  their tree.

## Main results

* `Minimalist.Merge.mergeOpG_apply_of'`, `mergeOpG_apply_of'_eq_sum`: Merge on a workspace is a sum
  over its forest cuts, or over a choice of cut for each of its trees.
* `Minimalist.Merge.mergeOpG_comm`: Merge does not depend on the order of the pair.
* `Minimalist.Merge.mergeOp_eq_comp_comulAlgHomN`: Merge at `Δ^d` through the pruning coproduct,
  the book's (1.3.10).
* `Minimalist.Merge.mergeOp_eq_rename_contractUnary_comp`,
  `mergeOpUnit_eq_rename_contractUnary_comp`: on objects without unary vertices, Merge at the
  deletion cuts is Merge at the pruning cuts followed by contracting unary vertices.

## Implementation notes

Definition 1.3.4 fixes the deletion coproduct `Δ^d`, which contracts the unary vertex a cut leaves,
and `mergeOp` is Merge at the deletion cuts. The pruning coproduct `Δ^ρ` keeps that vertex. The two
extract the same accessible terms, but `⊔` multiplies the remainder into the result, so Merge at
the pruning cuts (`mergeOpG cutSummandsN`) is not the book's operator: its Internal Merge leaves a
unary vertex, which no syntactic object has. The book writes (1.3.7) through `Δ^ρ` only with the
right channel contracted after the matching (`mergeOp_eq_comp_comulAlgHomN`).

The deletion cuts do not admit Merge in the sense of `IsMergeCuts`: on a tree with a unary vertex
the trunk of the empty cut is the contracted tree, not the tree. The book's objects are binary
trees, which have none, and on them `mergeOp` is Merge at the pruning cuts followed by the
contraction (`mergeOp_eq_rename_contractUnary_comp`).

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
    a pair exact (`mergeOpG_pair`); the other two let a spectator component pass through
    (`mergeOpG_ofTree_mul`). -/
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

/-- Every crown member of a cut in `treeCutsG cuts T`, the whole tree included, is a subtree of
    `T`. -/
theorem mem_subtrees_of_mem_treeCutsG {a : Forest (UnorderedTree α) × Forest (UnorderedTree α)}
    (ha : a ∈ treeCutsG cuts T) {x : UnorderedTree α} (hx : x ∈ a.1) : x ∈ T.subtrees := by
  rcases Multiset.mem_cons.mp ha with rfl | ha
  · rw [Multiset.mem_singleton.mp hx]; exact T.self_mem_subtrees
  · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ha
    exact mem_subtrees_of_mem_crown hp hx

end IsMergeCuts

/-! ### Products in the two channels -/

private theorem of'_mul_single (F G : Forest (UnorderedTree α)) (r : R) :
    of' (R := R) F * single G r = single (F + G) r := by
  rw [← smul_of', mul_smul_comm, ← of'_add, smul_of']

/-- A chain `⊔ ∘ (f ⊗ id)` kills every term whose left channel is a product with `x` that `f`
    kills. -/
private theorem mul'_map_tmul_mul_eq_zero
    (f : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α))
    {x : ConnesKreimer R (UnorderedTree α)} (hf : ∀ a, f (x * a) = 0)
    (b : ConnesKreimer R (UnorderedTree α))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    (LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ TensorProduct.map f LinearMap.id)
      ((x ⊗ₜ[R] b) * z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul a b' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, TensorProduct.map_tmul, hf,
      TensorProduct.zero_tmul, map_zero]
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, add_zero]

/-- A chain `⊔ ∘ (f ⊗ id)` commutes with right multiplication by a right-channel factor `1 ⊗ y`. -/
private theorem mul'_map_mul_one_tmul
    (f : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (y : ConnesKreimer R (UnorderedTree α)) :
    (LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ TensorProduct.map f LinearMap.id)
        (z * ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] y))
      = (LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
          TensorProduct.map f LinearMap.id) z * y := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, LinearMap.comp_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.id_apply,
      LinearMap.mul'_apply, LinearMap.mul'_apply, mul_assoc]
  | add z₁ z₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]

section DecidableEq

variable [DecidableEq (UnorderedTree α)]

/-! ### The matching projections -/

/-- The projection onto the basis element `F₀` keeps its coefficient and sends every other basis
    element to zero. -/
noncomputable def forestProj (F₀ : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  ConnesKreimer.linearLift (fun F => if F = F₀ then of' F else 0)

theorem forestProj_apply_of' (F₀ F : Forest (UnorderedTree α)) :
    forestProj (R := R) F₀ (of' F) = if F = F₀ then of' F else 0 := by
  rw [forestProj, ConnesKreimer.linearLift_of']

/-- The projection onto `F₀` kills every product with a forest that does not fit inside `F₀`. -/
theorem forestProj_mul_eq_zero_of_not_le {F₀ F : Forest (UnorderedTree α)} (hF : ¬ F ≤ F₀)
    (a : ConnesKreimer R (UnorderedTree α)) : forestProj F₀ (of' F * a) = 0 := by
  induction a using ConnesKreimer.induction_linear with
  | zero => rw [mul_zero, map_zero]
  | add g h hg hh => rw [mul_add, map_add, hg, hh, add_zero]
  | single G r =>
    have hne : F + G ≠ F₀ := fun heq => hF (heq ▸ Multiset.le_add_right F G)
    rw [of'_mul_single, forestProj]
    simp only [ConnesKreimer.linearLift_single]
    rw [ite_eq_right hne, smul_zero]

/-- The matching projection `γ_{S,S'}` ([marcolli-chomsky-berwick-2025] Definition 1.3.1) is the
    projection onto `{S, S'}`. -/
noncomputable def gammaMatch (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  forestProj {S, S'}

theorem gammaMatch_apply_singleton (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    gammaMatch (R := R) S S' (of' F) =
      if F = ({S, S'} : Forest (UnorderedTree α)) then of' F else 0 :=
  forestProj_apply_of' _ F

/-- The matching operator `δ_{S,S'} = γ_{S,S'} ⊗ id` acts on the left channel of a coproduct. -/
noncomputable def deltaMatch (S S' : UnorderedTree α) :
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  TensorProduct.map (gammaMatch (R := R) S S') LinearMap.id

/-! ### Grafting -/

/-- The grafting operator `B` at the pair `S, S'` sends the basis element `{S, S'}` to the tree
    `node lbl {S, S'}` and every other basis element to zero. Merge applies it only after
    `δ_{S,S'}`, so this restriction of [marcolli-chomsky-berwick-2025]'s `B` suffices. -/
noncomputable def graftBinaryAt (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  ConnesKreimer.linearLift
    (fun F => if F = ({S, S'} : Forest (UnorderedTree α))
      then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) else 0)

theorem graftBinaryAt_apply_singleton (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    graftBinaryAt (R := R) lbl S S' (of' F) =
      if F = ({S, S'} : Forest (UnorderedTree α))
        then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α))
        else 0 := by
  rw [graftBinaryAt, ConnesKreimer.linearLift_of']

/-! ### The Merge operator -/

/-- The post-coproduct chain `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}`, shared by every cut enumeration. -/
noncomputable def mergePost (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mul' R (ConnesKreimer R (UnorderedTree α))
    ∘ₗ TensorProduct.map (graftBinaryAt (R := R) lbl S S') LinearMap.id
    ∘ₗ deltaMatch (R := R) S S'

/-- On a basis tensor `of' F ⊗ r`, the post-coproduct chain grafts `F` if it is `{S, S'}` and
    vanishes otherwise. -/
theorem mergePost_basis_tensor (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (r : ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S' (of' F ⊗ₜ[R] r)
      = if F = ({S, S'} : Forest (UnorderedTree α))
          then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) * r
          else 0 := by
  unfold mergePost deltaMatch
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, gammaMatch_apply_singleton]
  by_cases hF : F = ({S, S'} : Forest (UnorderedTree α))
  · subst hF
    rw [ite_eq_left rfl, TensorProduct.map_tmul, LinearMap.id_apply,
        graftBinaryAt_apply_singleton, ite_eq_left rfl, ite_eq_left rfl]
    exact LinearMap.mul'_apply
  · rw [ite_eq_right hF, TensorProduct.zero_tmul, ite_eq_right hF]
    simp only [map_zero]

/-- `γ_{S,S'}` kills every product with a forest `F` that does not fit inside `{S, S'}`. -/
theorem gammaMatch_mul_eq_zero_of_not_le (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α))
    (hF : ¬ F ≤ ({S, S'} : Forest (UnorderedTree α)))
    (a : ConnesKreimer R (UnorderedTree α)) :
    gammaMatch (R := R) S S' (of' F * a) = 0 :=
  forestProj_mul_eq_zero_of_not_le hF a

/-- `γ_{S,S'}` kills every product with a tree other than `S` and `S'`. -/
theorem gammaMatch_singleton_mul_eq_zero (S S' T : UnorderedTree α)
    (hT_ne_S : T ≠ S) (hT_ne_S' : T ≠ S') (a : ConnesKreimer R (UnorderedTree α)) :
    gammaMatch (R := R) S S' (of' ({T} : Forest (UnorderedTree α)) * a) = 0 := by
  apply gammaMatch_mul_eq_zero_of_not_le
  intro h_le
  have hT_mem : T ∈ ({S, S'} : Forest (UnorderedTree α)) :=
    Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
  rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
  exact hT_mem.elim hT_ne_S hT_ne_S'

private theorem mergePost_eq (lbl : α) (S S' : UnorderedTree α) :
    mergePost (R := R) lbl S S' = LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
      TensorProduct.map (graftBinaryAt lbl S S' ∘ₗ gammaMatch S S') LinearMap.id := by
  rw [mergePost, deltaMatch, ← TensorProduct.map_comp, LinearMap.id_comp]

/-- The post-coproduct chain kills every term whose left channel carries a forest that does not
    fit inside `{S, S'}`. -/
theorem mergePost_left_mul_eq_zero_of_not_le (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (b : ConnesKreimer R (UnorderedTree α))
    (hF : ¬ F ≤ ({S, S'} : Forest (UnorderedTree α)))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S' ((of' (R := R) F ⊗ₜ[R] b) * z) = 0 := by
  rw [mergePost_eq]
  exact mul'_map_tmul_mul_eq_zero _ (fun a ↦ by
    rw [LinearMap.comp_apply, gammaMatch_mul_eq_zero_of_not_le _ _ _ hF, map_zero]) b z

/-- The post-coproduct chain commutes with right multiplication by a right-channel factor
    `1 ⊗ y`, so a spectator workspace passes through it unchanged. -/
theorem mergePost_right_one_tmul (lbl : α) (S S' : UnorderedTree α)
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (y : ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S'
        (z * ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] y))
      = mergePost (R := R) (α := α) lbl S S' z * y := by
  rw [mergePost_eq]
  exact mul'_map_mul_one_tmul _ z y

/-! ### The unit stage `M_{β,1}`

The first stage of Internal Merge (Proposition 1.4.2) moves an accessible term `β` to the left
channel and leaves `T/β` on the right. Its grafting step is the identity, since
`B(β ⊔ 1) = M(β, 1) = β`. It is not a Merge in its own right: it occurs only composed with
`M_{T/β,β}` ([marcolli-chomsky-berwick-2025] Remark 1.4.3). -/

/-- The single-tree matching projection `γ_{β,1}` keeps the coefficient of the basis element
    `{β}`. -/
noncomputable def gammaMatchSingle (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  forestProj {β}

theorem gammaMatchSingle_apply_singleton (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    gammaMatchSingle (R := R) β (of' F) =
      if F = ({β} : Forest (UnorderedTree α)) then of' F else 0 :=
  forestProj_apply_of' _ F

/-- The matching operator `δ_{β,1} = γ_{β,1} ⊗ id`. -/
noncomputable def deltaMatchSingle (β : UnorderedTree α) :
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  TensorProduct.map (gammaMatchSingle (R := R) β) LinearMap.id

/-- The post-coproduct chain `⊔ ∘ δ_{β,1}` of the unit stage. -/
noncomputable def mergePostUnit (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ deltaMatchSingle (R := R) β

theorem mergePostUnit_basis_tensor (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (r : ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) (α := α) β (of' F ⊗ₜ[R] r)
      = if F = ({β} : Forest (UnorderedTree α))
          then of' ({β} : Forest (UnorderedTree α)) * r
          else 0 := by
  unfold mergePostUnit deltaMatchSingle
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      gammaMatchSingle_apply_singleton]
  by_cases hF : F = ({β} : Forest (UnorderedTree α))
  · subst hF
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact LinearMap.mul'_apply
  · rw [ite_eq_right hF, TensorProduct.zero_tmul, ite_eq_right hF]
    exact map_zero _

/-- The unit chain kills every term whose left channel carries a forest that does not fit inside
    `{β}`. -/
theorem mergePostUnit_left_mul_eq_zero_of_not_le (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (b : ConnesKreimer R (UnorderedTree α))
    (hF : ¬ F ≤ ({β} : Forest (UnorderedTree α)))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) β ((of' (R := R) F ⊗ₜ[R] b) * z) = 0 :=
  mul'_map_tmul_mul_eq_zero _ (forestProj_mul_eq_zero_of_not_le hF) b z

/-- The unit chain commutes with right multiplication by a right-channel factor `1 ⊗ y`. -/
theorem mergePostUnit_right_one_tmul (β : UnorderedTree α)
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (y : ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) β (z * ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] y))
      = mergePostUnit (R := R) β z * y :=
  mul'_map_mul_one_tmul _ z y

/-! ### Merge over a cut enumeration -/

/-- Merge `M_{S,S'}` over a cut enumeration `cuts`, whose coproduct is `comulAlgHomNG cuts`. -/
noncomputable def mergeOpG (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α))
    (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ (comulAlgHomNG cuts).toLinearMap

/-- The unit stage `M_{β,1}` over a cut enumeration `cuts`. -/
noncomputable def mergeOpUnitG (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePostUnit (R := R) (α := α) β ∘ₗ (comulAlgHomNG cuts).toLinearMap

/-- The Merge operator `M_{S,S'}` of [marcolli-chomsky-berwick-2025] Definition 1.3.4, Merge at
    the deletion cuts `cutSummandsDN`, whose coproduct is `Δ^d`, with root label `lbl`. -/
noncomputable def mergeOp (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergeOpG (R := R) cutSummandsDN lbl S S'

/-- The unit stage `M_{β,1}` at the deletion cuts, the operator of Definition 1.3.4 that
    Proposition 1.4.2 composes with External Merge. -/
noncomputable def mergeOpUnit (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergeOpUnitG (R := R) cutSummandsDN β

/-- Merge on a workspace `F` grafts `{S, S'}` beside the trunk of each forest cut of `F` with crown
    `{S, S'}` ([marcolli-chomsky-berwick-2025] (1.3.11)). -/
theorem mergeOpG_apply_of' (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    mergeOpG (R := R) cuts lbl S S' (of' F) = of' {UnorderedTree.node lbl {S, S'}} *
      (((forestCutsG cuts F).filter (·.1 = {S, S'})).map fun p ↦ of' (R := R) p.2).sum := by
  rw [mergeOpG, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomNG_apply_of',
    comulForestNG_eq_sum, map_multiset_sum, Multiset.map_map, Multiset.sum_map_filter,
    ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ ↦ ?_)
  rw [Function.comp_apply, cutTensor, mergePost_basis_tensor, mul_ite, mul_zero]

/-- Merge on a workspace `F` is a sum of workspaces, one for each choice of a cut of each tree of
    `F` whose crowns together are `{S, S'}`. -/
theorem mergeOpG_apply_of'_eq_sum (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    mergeOpG (R := R) cuts lbl S S' (of' F) =
      (((forestCutChoicesG cuts F).filter (·.crown = {S, S'})).map
        fun s ↦ of' ({UnorderedTree.node lbl {S, S'}} + s.trunk)).sum := by
  rw [mergeOpG_apply_of', forestCutsG_eq_map_forestCutChoicesG, Multiset.filter_map,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  simp only [Function.comp_def, of'_add]

/-- The unit stage on a workspace `F` is a sum of workspaces, one for each choice of a cut of each
    tree of `F` whose crowns together are `{β}`. -/
theorem mergeOpUnitG_apply_of'_eq_sum (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    mergeOpUnitG (R := R) cuts β (of' F) =
      (((forestCutChoicesG cuts F).filter (·.crown = {β})).map
        fun s ↦ of' ({β} + s.trunk)).sum := by
  rw [mergeOpUnitG, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomNG_apply_of',
    comulForestNG_eq_sum, forestCutsG_eq_map_forestCutChoicesG, Multiset.map_map,
    map_multiset_sum, Multiset.map_map, Multiset.sum_map_filter]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ ↦ ?_)
  simp only [Function.comp_apply, cutTensor, mergePostUnit_basis_tensor]
  split_ifs
  · rw [← of'_add]
  · simp

/-- Merge does not depend on the order of the pair. -/
theorem mergeOpG_comm (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α) :
    mergeOpG (R := R) cuts lbl S S' = mergeOpG cuts lbl S' S := by
  simp only [mergeOpG, mergePost, deltaMatch, gammaMatch, graftBinaryAt, Multiset.pair_comm S S']

/-- The unit stage vanishes on the empty workspace, which has no `β` to extract. -/
theorem mergeOpUnitG_one (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    mergeOpUnitG (R := R) cuts β 1 = 0 := by
  rw [mergeOpUnitG, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
    Algebra.TensorProduct.one_def, ← of'_zero, mergePostUnit_basis_tensor,
    ite_eq_right (Multiset.singleton_ne_zero β).symm]

/-! ### Deletion and pruning

Merge at the deletion cuts reaches the pruning coproduct through the contraction `Π_{d,ρ}` of the
right channel, `rename UnorderedTree.contractUnary`, which commutes with the matching since the two
act on different channels. -/

section Contraction

omit [DecidableEq (UnorderedTree α)] in
private theorem comulAlgHomNG_cutSummandsDN_apply (x : ConnesKreimer R (UnorderedTree α)) :
    comulAlgHomNG cutSummandsDN x = TensorProduct.map LinearMap.id
      (rename (R := R) UnorderedTree.contractUnary).toLinearMap (comulAlgHomN x) := by
  rw [comulAlgHomNG_cutSummandsDN, comulDAlgHomN, AlgHom.comp_apply,
    Algebra.TensorProduct.map, Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply]
  rfl

/-- Merge at `Δ^d` is `⊔ ∘ (B ⊗ id) ∘ (id ⊗ Π_{d,ρ}) ∘ δ_{S,S'} ∘ Δ^ρ`, the matching taken through
    the pruning coproduct and the remainder contracted after it
    ([marcolli-chomsky-berwick-2025] (1.3.10)). -/
theorem mergeOp_eq_comp_comulAlgHomN (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' = LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
      TensorProduct.map (graftBinaryAt lbl S S') LinearMap.id ∘ₗ
      TensorProduct.map LinearMap.id (rename (R := R) UnorderedTree.contractUnary).toLinearMap ∘ₗ
      deltaMatch S S' ∘ₗ (comulAlgHomN (R := R) (α := α)).toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOp, mergeOpG, mergePost, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    comulAlgHomNG_cutSummandsDN_apply]
  generalize comulAlgHomN (R := R) (α := α) x = y
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [deltaMatch]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Grafting a pair without unary vertices gives a tree the contraction fixes. -/
private theorem rename_contractUnary_graftBinaryAt (lbl : α) {S S' : UnorderedTree α}
    (hS : S.numUnary = 0) (hS' : S'.numUnary = 0) (a : ConnesKreimer R (UnorderedTree α)) :
    rename UnorderedTree.contractUnary (graftBinaryAt lbl S S' a) = graftBinaryAt lbl S S' a := by
  induction a using ConnesKreimer.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single F r =>
    rw [← smul_of', map_smul, map_smul, graftBinaryAt_apply_singleton]
    split_ifs
    · rw [rename_of', Multiset.map_singleton, UnorderedTree.contractUnary_node_pair,
        UnorderedTree.contractUnary_eq_self_iff.mpr hS,
        UnorderedTree.contractUnary_eq_self_iff.mpr hS']
    · rw [map_zero]

/-- On objects without unary vertices, Merge at the deletion cuts is Merge at the pruning cuts
    followed by contracting the unary vertices of the workspace. -/
theorem mergeOp_eq_rename_contractUnary_comp (lbl : α) {S S' : UnorderedTree α}
    (hS : S.numUnary = 0) (hS' : S'.numUnary = 0) :
    mergeOp (R := R) lbl S S' = (rename (R := R) UnorderedTree.contractUnary).toLinearMap ∘ₗ
      mergeOpG (R := R) cutSummandsN lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOp_eq_comp_comulAlgHomN, mergeOpG, mergePost, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, comulAlgHomN]
  generalize deltaMatch S S' (comulAlgHomNG (R := R) cutSummandsN x) = y
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [rename_contractUnary_graftBinaryAt lbl hS hS']
  | add y z hy hz => simp only [map_add, hy, hz]

/-- A singleton matching of a tree without unary vertices is fixed by the contraction. -/
private theorem rename_contractUnary_gammaMatchSingle {β : UnorderedTree α} (hβ : β.numUnary = 0)
    (a : ConnesKreimer R (UnorderedTree α)) :
    rename UnorderedTree.contractUnary (gammaMatchSingle β a) = gammaMatchSingle β a := by
  induction a using ConnesKreimer.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single F r =>
    rw [← smul_of', map_smul, map_smul, gammaMatchSingle_apply_singleton]
    split_ifs with h
    · rw [rename_of', h, Multiset.map_singleton, UnorderedTree.contractUnary_eq_self_iff.mpr hβ]
    · rw [map_zero]

/-- On a tree without unary vertices, the unit stage at the deletion cuts is the unit stage at the
    pruning cuts followed by contracting the unary vertices of the workspace. -/
theorem mergeOpUnit_eq_rename_contractUnary_comp {β : UnorderedTree α} (hβ : β.numUnary = 0) :
    mergeOpUnit (R := R) β = (rename (R := R) UnorderedTree.contractUnary).toLinearMap ∘ₗ
      mergeOpUnitG (R := R) cutSummandsN β := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOpUnit, mergeOpUnitG, mergePostUnit, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, comulAlgHomNG_cutSummandsDN_apply, comulAlgHomN]
  generalize comulAlgHomNG (R := R) cutSummandsN x = y
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [deltaMatchSingle, rename_contractUnary_gammaMatchSingle hβ]
  | add y z hy hz => simp only [map_add, hy, hz]

end Contraction

end DecidableEq

/-! ### Merge at the trace cuts -/

/-- The trace Merge operator is Merge at the trace cuts `cutSummandsCN τ`, whose trunks carry a
    trace leaf at each cut site. -/
noncomputable def mergeOpC {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpG (R := R) (cutSummandsCN τ) lbl S S'

/-- The unit stage `M_{S,1}` at the trace cuts `cutSummandsCN τ`. -/
noncomputable def mergeOpUnitC {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (S : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpUnitG (R := R) (cutSummandsCN τ) S

end Minimalist.Merge
