module

public import Linglib.Core.Algebra.RootedTree.Coproduct.AdmissibleCut
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Data.UnorderedTree.Leaves
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
`cuts` (`mergeOpOfCuts`). The book's `Δ` is the deletion coproduct `Δ^d`, and `mergeOp` is Merge at
the deletion cuts; `traceMergeOp` is Merge at the trace cuts. The unit stage `M_{β,1}` of Internal
Merge (Proposition 1.4.2) has no grafting step (`mergeOpUnitOfCuts`).

On a workspace `F`, Merge grafts `{S, S'}` beside the trunk of each forest cut of `F` whose crown
is `{S, S'}`, summed over all such cuts (`mergeOpOfCuts_apply_of'`, the book's (1.3.11)). Each form
of Merge in their §1.4 is this sum on a particular workspace.

External, Internal and Sideward Merge are in `Merge/External.lean`, `Merge/Internal.lean` and
`Merge/Sideward.lean`; the Minimal-Search weighting is in `Merge/MinimalSearch.lean`.

## Main definitions

* `Minimalist.Merge.mergeOpOfCuts`, `mergeOp`, `traceMergeOp`: Merge over a cut enumeration, at the
  deletion cuts, and at the trace cuts.
* `Minimalist.Merge.mergeOpUnitOfCuts`, `mergeOpUnit`, `traceMergeOpUnit`: the unit stage `M_{β,1}`.
* `Minimalist.Merge.IsMergeCuts`: cut enumerations whose nonempty crowns have fewer edges than
  their tree.

## Main results

* `Minimalist.Merge.mergeOpOfCuts_apply_of'`, `mergeOpOfCuts_apply_of'_eq_sum`: Merge on a workspace
  is a sum over its forest cuts, or over a choice of cut for each of its trees.
* `Minimalist.Merge.mergeOpOfCuts_comm`: Merge does not depend on the order of the pair.
* `Minimalist.Merge.mergeOp_eq_comp_comulAlgHom`, `mergeOp_eq_comp_traceComulAlgHom`: Merge at `Δ^d`
  through the Connes–Kreimer coproduct and through the trace coproduct, the two expressions of the
  book's (1.3.10).
* `Minimalist.Merge.mergeOp_eq_rename_contractUnary_comp`,
  `mergeOpUnit_eq_rename_contractUnary_comp`: on objects without unary vertices, Merge at the
  deletion cuts is Merge at the admissible cuts followed by contracting unary vertices.
* `Minimalist.Merge.eraseTraces_comp_traceMergeOp`, `mergeOp_eq_comp_traceMergeOp`,
  `mergeOpUnit_eq_comp_traceMergeOpUnit`: on trees without traces, erasing the traces of Merge at
  the trace cuts gives Merge at the admissible cuts, and contracting too gives Merge at the deletion
  cuts.

## Implementation notes

Definition 1.3.4 fixes the deletion coproduct `Δ^d`, which contracts the unary vertex a cut leaves,
and `mergeOp` is Merge at the deletion cuts. The Connes–Kreimer coproduct `Δ^ρ` keeps that vertex.
The two extract the same accessible terms, but `⊔` multiplies the remainder into the result, so
Merge at the admissible cuts (`mergeOpOfCuts admissibleCuts`) is not the book's operator: its
Internal Merge leaves a unary vertex, which no syntactic object has. The book writes (1.3.7) through
`Δ^ρ` only with the right channel contracted after the matching (`mergeOp_eq_comp_comulAlgHom`).

The deletion cuts do not admit Merge in the sense of `IsMergeCuts`: on a tree with a unary vertex
the trunk of the empty cut is the contracted tree, not the tree. The book's objects are binary
trees, which have none, and on them `mergeOp` is Merge at the admissible cuts followed by the
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
    the deletion cuts `deletionCuts`, whose coproduct is `Δ^d`, with root label `lbl`. -/
noncomputable def mergeOp (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergeOpOfCuts (R := R) deletionCuts lbl S S'

/-- The unit stage `M_{β,1}` at the deletion cuts, the operator of Definition 1.3.4 that
    Proposition 1.4.2 composes with External Merge. -/
noncomputable def mergeOpUnit (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergeOpUnitOfCuts (R := R) deletionCuts β

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

/-- Merge does not depend on the order of the pair. -/
theorem mergeOpOfCuts_comm (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α) :
    mergeOpOfCuts (R := R) cuts lbl S S' = mergeOpOfCuts cuts lbl S' S := by
  simp only [mergeOpOfCuts, mergePost, deltaMatch, gammaMatch, graftBinaryAt,
    Multiset.pair_comm S S']

/-- The unit stage vanishes on the empty workspace, which has no `β` to extract. -/
theorem mergeOpUnitOfCuts_one (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    mergeOpUnitOfCuts (R := R) cuts β 1 = 0 := by
  rw [mergeOpUnitOfCuts, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
    Algebra.TensorProduct.one_def, ← of'_zero, mergePostUnit_basis_tensor,
    ite_eq_right (Multiset.singleton_ne_zero β).symm]

/-! ### Deletion and admissible cuts

Merge at the deletion cuts reaches the Connes–Kreimer coproduct through the contraction `Π_{d,ρ}` of
the right channel, `rename UnorderedTree.contractUnary`, which commutes with the matching since the
two act on different channels. -/

section Contraction

omit [DecidableEq (UnorderedTree α)] in
private theorem comulOfCuts_deletionCuts_apply (x : ConnesKreimer R (UnorderedTree α)) :
    comulOfCuts deletionCuts x = TensorProduct.map LinearMap.id
      (rename (R := R) UnorderedTree.contractUnary).toLinearMap (comulAlgHom x) := by
  rw [comulOfCuts_deletionCuts, deletionComulAlgHom, AlgHom.comp_apply,
    Algebra.TensorProduct.map, Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply]
  rfl

/-- Merge at `Δ^d` is `⊔ ∘ (B ⊗ id) ∘ (id ⊗ Π_{d,ρ}) ∘ δ_{S,S'} ∘ Δ^ρ`, the matching taken through
    the Connes–Kreimer coproduct and the remainder contracted after it
    ([marcolli-chomsky-berwick-2025] (1.3.10)). -/
theorem mergeOp_eq_comp_comulAlgHom (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' = LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
      TensorProduct.map (graftBinaryAt lbl S S') LinearMap.id ∘ₗ
      TensorProduct.map LinearMap.id (rename (R := R) UnorderedTree.contractUnary).toLinearMap ∘ₗ
      deltaMatch S S' ∘ₗ (comulAlgHom (R := R) (α := α)).toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOp, mergeOpOfCuts, mergePost, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    comulOfCuts_deletionCuts_apply]
  generalize comulAlgHom (R := R) (α := α) x = y
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

/-- On objects without unary vertices, Merge at the deletion cuts is Merge at the admissible cuts
    followed by contracting the unary vertices of the workspace. -/
theorem mergeOp_eq_rename_contractUnary_comp (lbl : α) {S S' : UnorderedTree α}
    (hS : S.numUnary = 0) (hS' : S'.numUnary = 0) :
    mergeOp (R := R) lbl S S' = (rename (R := R) UnorderedTree.contractUnary).toLinearMap ∘ₗ
      mergeOpOfCuts (R := R) admissibleCuts lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOp_eq_comp_comulAlgHom, mergeOpOfCuts, mergePost, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, comulAlgHom]
  generalize deltaMatch S S' (comulOfCuts (R := R) admissibleCuts x) = y
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
    admissible cuts followed by contracting the unary vertices of the workspace. -/
theorem mergeOpUnit_eq_rename_contractUnary_comp {β : UnorderedTree α} (hβ : β.numUnary = 0) :
    mergeOpUnit (R := R) β = (rename (R := R) UnorderedTree.contractUnary).toLinearMap ∘ₗ
      mergeOpUnitOfCuts (R := R) admissibleCuts β := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [mergeOpUnit, mergeOpUnitOfCuts, mergePostUnit, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, comulOfCuts_deletionCuts_apply, comulAlgHom]
  generalize comulOfCuts (R := R) admissibleCuts x = y
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [deltaMatchSingle, rename_contractUnary_gammaMatchSingle hβ]
  | add y z hy hz => simp only [map_add, hy, hz]

end Contraction

end DecidableEq

/-! ### Merge at the trace cuts -/

/-- The trace Merge operator is Merge at the trace cuts `traceCuts τ`, whose trunks carry a
    trace leaf at each cut site. -/
noncomputable def traceMergeOp {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpOfCuts (R := R) (traceCuts τ) lbl S S'

/-- The unit stage `M_{S,1}` at the trace cuts `traceCuts τ`. -/
noncomputable def traceMergeOpUnit {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (S : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpUnitOfCuts (R := R) (traceCuts τ) S

/-! ### Erasing the traces of Merge

An injective relabelling commutes with matching and grafting, and the embedding of the trees
without traces is a section of the erasure `eraseTraces`. So erasure carries the chain of Merge at
an embedded pair to the chain at the pair, and the relations between the coproducts pass to
Merge. -/

section Relabel

variable {γ : Type*} [DecidableEq (UnorderedTree α)] [DecidableEq (UnorderedTree γ)]
  {g : α → γ} (hg : Function.Injective g)
include hg

/-- An injective relabelling commutes with the projection onto a forest. -/
theorem forestProj_rename (F₀ : Forest (UnorderedTree α))
    (x : ConnesKreimer R (UnorderedTree α)) :
    forestProj (F₀.map (UnorderedTree.map g)) (rename (UnorderedTree.map g) x) =
      rename (UnorderedTree.map g) (forestProj F₀ x) := by
  induction x using ConnesKreimer.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single F r =>
    rw [← smul_of']
    by_cases h : F = F₀
    · subst h; simp [forestProj_apply_of']
    · simp [forestProj_apply_of', h,
        (Multiset.map_injective (UnorderedTree.map_injective hg)).ne h]

/-- An injective relabelling commutes with grafting. -/
theorem graftBinaryAt_rename (lbl : α) (S S' : UnorderedTree α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    graftBinaryAt (g lbl) (S.map g) (S'.map g) (rename (UnorderedTree.map g) x) =
      rename (UnorderedTree.map g) (graftBinaryAt lbl S S' x) := by
  induction x using ConnesKreimer.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single F r =>
    have hpair : ({S.map g, S'.map g} : Forest (UnorderedTree γ)) =
        ({S, S'} : Forest (UnorderedTree α)).map (UnorderedTree.map g) := by simp
    rw [← smul_of', map_smul, map_smul, map_smul, rename_of', graftBinaryAt_apply_singleton,
      graftBinaryAt_apply_singleton, hpair]
    by_cases h : F = {S, S'}
    · subst h; simp [UnorderedTree.map_node]
    · rw [ite_eq_right h,
        ite_eq_right ((Multiset.map_injective (UnorderedTree.map_injective hg)).ne h),
        smul_zero, smul_zero, map_zero]

end Relabel

section Erasure

variable {β : Type*} (τ : UnorderedTree (α ⊕ β) → β)

/-- The embedding of the trees without traces into the trees with traces. -/
local notation "ι" => rename (R := R) (UnorderedTree.map (Sum.inl : α → α ⊕ β))

/-- The projection `Π_{d,c}`: erase the traces, then contract the unary vertices. -/
local notation "Π_dc" => AlgHom.comp (rename (R := R) (UnorderedTree.contractUnary (α := α)))
  (eraseTraces (R := R) (α := α) (β := β))

/-- A left channel that absorbs the embedding absorbs it in a pair of channels. -/
private theorem mul'_map_rename_inl {L : ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α)}
    {L' : ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree α)}
    (hL : ∀ x, L' (ι x) = L x)
    (y : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    LinearMap.mul' R _ (TensorProduct.map L' LinearMap.id
      (Algebra.TensorProduct.map ι (.id R _) y)) =
      LinearMap.mul' R _ (TensorProduct.map L LinearMap.id y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [hL]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Erasing the product of the two channels of `Δ^c` on an embedded tree gives the product of the
    two channels of `Δ^ρ`, for a left channel that erasure carries to `L`. -/
private theorem eraseTraces_mul'_traceComulAlgHom
    {L : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α)}
    {L' : ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β))}
    (hL : ∀ x, eraseTraces (R := R) (L' (ι x)) = L x) (x : ConnesKreimer R (UnorderedTree α)) :
    eraseTraces (R := R) (LinearMap.mul' R _ (TensorProduct.map L' LinearMap.id
      (traceComulAlgHom τ (ι x)))) =
      LinearMap.mul' R _ (TensorProduct.map L LinearMap.id (comulAlgHom x)) := by
  have hmul (z : ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
      ConnesKreimer R (UnorderedTree (α ⊕ β))) :
      eraseTraces (R := R) (LinearMap.mul' R _ (TensorProduct.map L' LinearMap.id z)) =
        LinearMap.mul' R _ (TensorProduct.map (eraseTraces.toLinearMap ∘ₗ L') LinearMap.id
          (Algebra.TensorProduct.map (.id R _) eraseTraces z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have h := DFunLike.congr_fun (eraseTraces_traceComulAlgHom (R := R) τ) x
  simp only [AlgHom.comp_apply] at h
  rw [hmul, h]
  exact mul'_map_rename_inl (L' := eraseTraces.toLinearMap ∘ₗ L') hL _

variable [DecidableEq (UnorderedTree α)] [DecidableEq (UnorderedTree (α ⊕ β))]

omit τ in
private theorem eraseTraces_graft_gamma_rename_inl (lbl : α) (S S' : UnorderedTree α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    (eraseTraces.toLinearMap ∘ₗ
        graftBinaryAt (R := R) (Sum.inl lbl : α ⊕ β) (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ
        gammaMatch (S.map Sum.inl) (S'.map Sum.inl)) (ι x) =
      (graftBinaryAt lbl S S' ∘ₗ gammaMatch S S') x := by
  have hpair : ({S.map Sum.inl, S'.map Sum.inl} : Forest (UnorderedTree (α ⊕ β))) =
      ({S, S'} : Forest (UnorderedTree α)).map (UnorderedTree.map Sum.inl) := by simp
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [gammaMatch, gammaMatch, hpair, forestProj_rename Sum.inl_injective,
    graftBinaryAt_rename Sum.inl_injective]
  exact DFunLike.congr_fun (eraseTraces_comp_rename_inl (R := R) (β := β)) _

/-- Erasing the traces of Merge at the trace cuts gives Merge at the admissible cuts, on trees
    without traces. -/
theorem eraseTraces_comp_traceMergeOp (lbl : α) (S S' : UnorderedTree α) :
    eraseTraces.toLinearMap ∘ₗ
        traceMergeOp (R := R) τ (Sum.inl lbl) (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ (ι).toLinearMap =
      mergeOpOfCuts admissibleCuts lbl S S' := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, traceMergeOp, mergeOpOfCuts, AlgHom.toLinearMap_apply,
    mergePost_eq]
  exact eraseTraces_mul'_traceComulAlgHom τ (eraseTraces_graft_gamma_rename_inl lbl S S') x

/-- Erasing the traces of the unit stage at the trace cuts gives the unit stage at the admissible
    cuts, on trees without traces. -/
theorem eraseTraces_comp_traceMergeOpUnit (S : UnorderedTree α) :
    eraseTraces.toLinearMap ∘ₗ traceMergeOpUnit (R := R) τ (S.map Sum.inl) ∘ₗ (ι).toLinearMap =
      mergeOpUnitOfCuts admissibleCuts S := by
  refine LinearMap.ext fun x ↦ eraseTraces_mul'_traceComulAlgHom τ (L := gammaMatchSingle S)
    (L' := gammaMatchSingle (S.map Sum.inl)) (fun y ↦ ?_) x
  rw [gammaMatchSingle, gammaMatchSingle, ← Multiset.map_singleton,
    forestProj_rename Sum.inl_injective]
  exact DFunLike.congr_fun (eraseTraces_comp_rename_inl (R := R) (β := β)) _

/-- Merge at `Δ^d` through the trace coproduct, the second expression of
    [marcolli-chomsky-berwick-2025] (1.3.10): `⊔ ∘ (B ⊗ id) ∘ (id ⊗ Π_{d,c}) ∘ δ_{S,S'} ∘ Δ^c`. The
    chain runs on the embedded tree, and `B` lands in the trees without traces through erasure. -/
theorem mergeOp_eq_comp_traceComulAlgHom (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' = LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
      TensorProduct.map
        (eraseTraces.toLinearMap ∘ₗ graftBinaryAt (Sum.inl lbl) (S.map Sum.inl) (S'.map Sum.inl))
        LinearMap.id ∘ₗ
      TensorProduct.map LinearMap.id (Π_dc).toLinearMap ∘ₗ
      deltaMatch (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ (traceComulAlgHom τ).toLinearMap ∘ₗ
      (ι).toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  have h := DFunLike.congr_fun (contractUnary_eraseTraces_traceComulAlgHom (R := R) τ) x
  simp only [AlgHom.comp_apply] at h
  have hchain {L : ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree α)}
      (z : ConnesKreimer R (UnorderedTree (α ⊕ β)) ⊗[R]
        ConnesKreimer R (UnorderedTree (α ⊕ β))) :
      TensorProduct.map L LinearMap.id (TensorProduct.map LinearMap.id (Π_dc).toLinearMap
          (deltaMatch (S.map Sum.inl) (S'.map Sum.inl) z)) =
        TensorProduct.map (L ∘ₗ gammaMatch (S.map Sum.inl) (S'.map Sum.inl)) LinearMap.id
          (Algebra.TensorProduct.map (.id R _) Π_dc z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [deltaMatch]
    | add y z hy hz => simp only [map_add, hy, hz]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, mergeOp, mergeOpOfCuts, mergePost_eq]
  rw [hchain, h, comulOfCuts_deletionCuts]
  exact (mul'_map_rename_inl (eraseTraces_graft_gamma_rename_inl (R := R) (β := β) lbl S S')
    (deletionComulAlgHom x)).symm

/-- On objects without unary vertices, Merge at the deletion cuts is the projection `Π_{d,c}` of
    Merge at the trace cuts. -/
theorem mergeOp_eq_comp_traceMergeOp (lbl : α) {S S' : UnorderedTree α} (hS : S.numUnary = 0)
    (hS' : S'.numUnary = 0) :
    mergeOp (R := R) lbl S S' = (Π_dc).toLinearMap ∘ₗ
      traceMergeOp τ (Sum.inl lbl : α ⊕ β) (S.map Sum.inl) (S'.map Sum.inl) ∘ₗ (ι).toLinearMap := by
  rw [mergeOp_eq_rename_contractUnary_comp lbl hS hS', ← eraseTraces_comp_traceMergeOp τ]
  rfl

/-- On a tree without unary vertices, the unit stage at the deletion cuts is the projection
    `Π_{d,c}` of the unit stage at the trace cuts: the remainder `T/d T_v` that the book sends to
    Externalization is `Π_{d,c}` of the remainder `T/c T_v` that it sends to semantic interpretation
    ([marcolli-chomsky-berwick-2025] p. 82). -/
theorem mergeOpUnit_eq_comp_traceMergeOpUnit {S : UnorderedTree α} (hS : S.numUnary = 0) :
    mergeOpUnit (R := R) S =
      (Π_dc).toLinearMap ∘ₗ traceMergeOpUnit τ (S.map Sum.inl) ∘ₗ (ι).toLinearMap := by
  rw [mergeOpUnit_eq_rename_contractUnary_comp hS, ← eraseTraces_comp_traceMergeOpUnit τ]
  rfl

end Erasure

end Minimalist.Merge
