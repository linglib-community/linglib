module

public import Linglib.Syntax.Minimalist.Workspace.Merge.External

/-!
# Internal Merge

Internal Merge (Proposition 1.4.2 of Marcolli, Chomsky and Berwick) is the composition
`M_{T/β,β} ∘ M_{β,1}`. The unit stage selects a cut of `T` with crown `{β}`, giving the two-object
workspace `{β, T/β}`, and External Merge then merges `β` with the quotient. When one cut extracts
`β`, the composition yields `node lbl {T/β, β}` over every cut enumeration admitting Merge
(`mergeOpG_im_composition`). At the deletion cuts of the book's Merge the quotient is the remainder
with its unary vertex contracted (`mergeOp_im_composition`); at the pruning cuts that vertex stays,
and at the trace cuts a trace takes the place of `β` (`mergeOpC_im_composition`).

## Main results

* `Minimalist.Merge.mergeOpUnitG_apply_singleton`, `mergeOpUnitG_apply_singleton_unique`: the
  unit stage on one tree, a sum over the cuts with crown `{β}`.
* `Minimalist.Merge.mergeOpUnitG_ofTree_mul`,
  `mergeOpUnitG_apply_singleton_unique_residual`: the unit stage beside a spectator workspace.
* `Minimalist.Merge.mergeOpG_im_composition`, `mergeOp_im_composition`,
  `mergeOpC_im_composition`: Internal Merge as a composition of Merges.
* `Minimalist.Merge.mergeOpG_im_composition_residual`: Internal Merge beside a spectator
  workspace.

## Implementation notes

The composition theorems assume a single cut extracting `β`, as in the book's worked example.
Proposition 1.4.2 does not; with several occurrences of `β` the unit stage is a sum over them
(`mergeOpUnitG_apply_singleton`).

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
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}

/-- On one tree `T`, the primitive term of the unit stage contributes `β` if `T = β`, and each
    cut with crown `{β}` contributes `β` beside its trunk. -/
theorem mergeOpUnitG_apply_singleton (β T : UnorderedTree α) :
    mergeOpUnitG (R := R) cuts β (of' ({T} : Forest (UnorderedTree α)))
      = (if T = β then of' ({β} : Forest (UnorderedTree α)) else 0)
        + ((cuts T).map
            (fun p => if p.1 = ({β} : Forest (UnorderedTree α))
              then of' (R := R) ({β} : Forest (UnorderedTree α)) * ofTree p.2 else 0)).sum := by
  rw [mergeOpUnitG, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    show (of' ({T} : Forest (UnorderedTree α)) : ConnesKreimer R (UnorderedTree α)) = ofTree T
      from rfl, comulAlgHomNG_apply_ofTree, comulTreeNG, map_add, map_multiset_sum,
    Multiset.map_map]
  congr 1
  · rw [show (ofTree T : ConnesKreimer R (UnorderedTree α)) = of' {T} from rfl,
      mergePostUnit_basis_tensor, mul_one]
    simp only [Multiset.singleton_inj]
  · exact congrArg Multiset.sum
      (Multiset.map_congr rfl fun p _ ↦ mergePostUnit_basis_tensor β p.1 (ofTree p.2))

/-- When `T ≠ β` and exactly one cut of `T` has crown `{β}`, the unit stage moves `β` to its own
    component beside that cut's trunk. -/
theorem mergeOpUnitG_apply_singleton_unique (β T : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (hTβ : T ≠ β) :
    mergeOpUnitG (R := R) cuts β (of' ({T} : Forest (UnorderedTree α)))
      = of' (R := R) ({β} : Forest (UnorderedTree α)) * ofTree p0.2 := by
  have hp0 : p0 ∈ (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) := by
    rw [h_filter]; exact Multiset.mem_singleton_self p0
  rw [mergeOpUnitG_apply_singleton, ite_eq_right hTβ, zero_add,
    ← Multiset.filter_add_not (fun p => p.1 = ({β} : Forest (UnorderedTree α))) (cuts T),
    Multiset.map_add, Multiset.sum_add, h_filter, Multiset.map_singleton, Multiset.sum_singleton,
    ite_eq_left (Multiset.mem_filter.mp hp0).2, Multiset.sum_eq_zero, add_zero]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  exact ite_eq_right (Multiset.mem_filter.mp hp).2

/-- The unit stage commutes with a spectator component `T` that does not have `β` as a subtree. -/
theorem mergeOpUnitG_ofTree_mul [IsMergeCuts cuts] {β T : UnorderedTree α}
    (hT : β ∉ T.subtrees) (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpUnitG (R := R) cuts β (ofTree T * w) = ofTree T * mergeOpUnitG (R := R) cuts β w := by
  rw [mergeOpUnitG, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, map_mul, comulAlgHomNG_apply_ofTree, comulTreeNG, add_mul, map_add,
    ← of'_singleton]
  -- The primitive term vanishes, since `T ≠ β`.
  rw [mergePostUnit_left_mul_eq_zero_of_not_le _ _ _ ?prim, zero_add]
  case prim =>
    intro h_le
    rw [Multiset.singleton_le, Multiset.mem_singleton] at h_le
    exact hT (h_le ▸ T.self_mem_subtrees)
  -- Split off the empty cut `(0, T)`; the nonempty cuts vanish.
  rw [← Multiset.sum_map_mul_right,
    ← Multiset.filter_add_not (fun pf => pf.1.card = 0) (cuts T),
    Multiset.map_add, Multiset.sum_add, map_add, IsMergeCuts.filter_empty,
    Multiset.map_singleton, Multiset.sum_singleton, _root_.map_multiset_sum,
    Multiset.sum_eq_zero, add_zero]
  · rw [of'_zero,
      mul_comm ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree T) _,
      mergePostUnit_right_one_tmul, mul_comm]
    rfl
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.map_map _ _ _ ▸ hx)
    obtain ⟨hp, hcard⟩ := Multiset.mem_filter.mp hp
    refine mergePostUnit_left_mul_eq_zero_of_not_le _ _ _ (fun h_le ↦ hcard ?_) _
    rw [Multiset.card_eq_zero]
    refine Multiset.eq_zero_of_forall_notMem fun x hx_mem => ?_
    rw [Multiset.mem_singleton.mp (Multiset.subset_of_le h_le hx_mem)] at hx_mem
    exact hT (IsMergeCuts.mem_subtrees_of_mem_crown hp hx_mem)

/-- With a residual workspace `F̂` none of whose components has `β` as a subtree, the unit stage
    on `{T} + F̂` splits `β` off `T` and leaves `F̂` unchanged. -/
theorem mergeOpUnitG_apply_singleton_unique_residual [IsMergeCuts cuts] (β T : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (hTβ : T ≠ β) {Fhat : Forest (UnorderedTree α)} (hF : ∀ U ∈ Fhat, β ∉ U.subtrees) :
    mergeOpUnitG (R := R) cuts β (of' (({T} : Forest (UnorderedTree α)) + Fhat))
      = of' (({β, p0.2} : Forest (UnorderedTree α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero, mergeOpUnitG_apply_singleton_unique β T p0 h_filter hTβ,
      ← of'_singleton, ← of'_add]
    rfl
  | cons U Fhat' ih =>
    rw [Multiset.add_cons, Multiset.add_cons, of'_cons, of'_cons,
      mergeOpUnitG_ofTree_mul (hF U (Multiset.mem_cons_self _ _)),
      ih fun V hV ↦ hF V (Multiset.mem_cons_of_mem hV)]

/-- Internal Merge as the composition `M_{T/β,β} ∘ M_{β,1}` over a cut enumeration admitting
    Merge, for `β` extracted from `T` by a single cut with trunk `Q`. -/
theorem mergeOpG_im_composition [IsMergeCuts cuts] (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) :
    mergeOpG (R := R) cuts lbl Q β
        (mergeOpUnitG (R := R) cuts β (of' ({T} : Forest (UnorderedTree α))))
      = of' ({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) := by
  rw [mergeOpUnitG_apply_singleton_unique β T p0 h_filter hTβ, h_remainder, ← of'_singleton,
    ← of'_add, add_comm]
  exact mergeOpG_pair lbl Q β

/-- Internal Merge with a residual workspace `F̂`, none of whose components has `β` or the trunk
    `Q` as a subtree. -/
theorem mergeOpG_im_composition_residual [IsMergeCuts cuts] (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cuts T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) {Fhat : Forest (UnorderedTree α)}
    (hF : ∀ U ∈ Fhat, Disjoint ({Q, β} : Forest (UnorderedTree α)) U.subtrees) :
    mergeOpG (R := R) cuts lbl Q β
        (mergeOpUnitG (R := R) cuts β (of' (({T} : Forest (UnorderedTree α)) + Fhat)))
      = of' (({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) + Fhat) := by
  rw [mergeOpUnitG_apply_singleton_unique_residual β T p0 h_filter hTβ
      fun U hU ↦ Multiset.disjoint_left.mp (hF U hU) (by simp), h_remainder,
    Multiset.pair_comm]
  exact mergeOpG_pair_residual lbl hF

/-- Internal Merge at the deletion cuts, for a mover `β` without unary vertices extracted by a
    single deletion cut with trunk `Q`. -/
theorem mergeOp_im_composition (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cutSummandsDN T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) (hβ : β.numUnary = 0) :
    mergeOp (R := R) lbl Q β (mergeOpUnit (R := R) β (of' ({T} : Forest (UnorderedTree α))))
      = of' ({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) := by
  obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp
    (Multiset.mem_of_mem_filter (h_filter.symm ▸ Multiset.mem_singleton_self p0))
  subst h_remainder
  rw [mergeOpUnit, mergeOpUnitG_apply_singleton_unique β T _ h_filter hTβ, ← of'_singleton,
    ← of'_add, add_comm]
  exact mergeOp_pair lbl (UnorderedTree.numUnary_contractUnary _) hβ

end DecidableEq

/-- At the trace cuts Internal Merge merges the mover `m` with the trunk `Q`, which keeps a trace
    in its place. -/
theorem mergeOpC_im_composition {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (m T Q : UnorderedTree (α ⊕ β))
    (p0 : Forest (UnorderedTree (α ⊕ β)) × UnorderedTree (α ⊕ β))
    (h_filter : (cutSummandsCN τ T).filter
      (fun p => p.1 = ({m} : Forest (UnorderedTree (α ⊕ β)))) = {p0})
    (h_remainder : p0.2 = Q) (hTm : T ≠ m) :
    mergeOpC (R := R) τ lbl Q m
        (mergeOpUnitC (R := R) τ m (of' ({T} : Forest (UnorderedTree (α ⊕ β)))))
      = of' ({UnorderedTree.node lbl {Q, m}} : Forest (UnorderedTree (α ⊕ β))) :=
  mergeOpG_im_composition lbl m T Q p0 h_filter h_remainder hTm

end Minimalist.Merge
