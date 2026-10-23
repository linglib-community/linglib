module

public import Linglib.Syntax.Minimalist.Workspace.Algebra.Merge.Internal
public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive
public import Mathlib.Algebra.Order.Monoid.Multiset

/-!
# Minimal Search as a weighting of Merge

Marcolli, Chomsky and Berwick implement Minimal Search by weighting the terms of the coproduct
(their §1.5). Extracting an accessible term at distance `d` from its root costs `ε^d`, the costs
of simultaneous extractions multiply, and Merge pays the weight of the terms it grafts, their
`M^ε_{S,S'} = ⊔ ∘ (B^ε ⊗ id) ∘ δ_{S,S'} ∘ Δ` of (1.5.1) and (1.5.2).

The weighted coproduct `comulEps ε` scales a tree by `ε` for each level it is moved down on its
way to the left channel. At `ε = 1` it is the pruning coproduct, so the weighted Merge
`mergeOpEps 1` is Merge. At `ε = 0` only whole components reach the left channel and the coproduct
is primitive, so `mergeOpEps 0` merges two components of the workspace and nothing else. At every
`ε`, weighted Merge agrees with its value at `ε = 0` up to a multiple of `ε`, and External and
Internal Merge have weight `1` (Proposition 1.5.1): they cost nothing, every Sideward term costs at
least one, and in the limit only External and Internal Merge remain.

## Main definitions

* `Minimalist.Merge.comulEps`: the depth-weighted coproduct.
* `Minimalist.Merge.mergeOpEps`: Merge weighted by Minimal Search.

## Main results

* `Minimalist.Merge.comulEps_one`, `comulEps_zero`: at `ε = 1` the weighted coproduct is the
  pruning coproduct, and at `ε = 0` it is the primitive coproduct.
* `Minimalist.Merge.mergeOpEps_pair`, `mergeOpEps_im_composition`: External and Internal Merge
  have weight `1` at every `ε`.
* `Minimalist.Merge.mergeOpEps_eq_add_smul`, `mergeOpEps_of'_eq_smul_of_not_le`: weighted Merge is
  its value at `ε = 0` plus a multiple of `ε`, so every form of Sideward Merge is a multiple of `ε`.
* `Minimalist.Merge.mergeOpEps_zero_of'_of_not_le`, `mergeOpEps_zero_pair_add`: at `ε = 0`, Merge
  vanishes unless both objects are components, and External Merge survives beside any spectators
  that do not repeat its objects.

## Implementation notes

* The book weights the left channel by `ε^d` and the right channel by `ε^{-d}`, and lets `B^ε` read
  the left weight. In a tensor product over `R` the two weights would cancel, so the weight is the
  coefficient of the left channel only. The book uses the right weight only to compute the cost
  `d - d = 0` of Internal Merge, which here is the cost `0` of merging two components.
* The unit stage `M_{β,1}` grafts nothing and costs nothing (the book's rule 4), so Internal Merge
  is `mergeOpEps ε lbl Q β ∘ mergeOpUnit β`, as the book writes it in proving Proposition 1.5.1.
* The weights are polynomial in `ε`, and the limit `ε → 0` is evaluation at `ε = 0`, the book's
  `M^ε_{S,S'}|_{ε=0}`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ### The empty-cut enumeration -/

instance : IsMergeCuts (emptyCuts (α := α)) where
  crown_numEdges_lt hp h := (h (congrArg Prod.fst (Multiset.mem_singleton.mp hp))).elim
  mem_subtrees_of_mem_crown hp hx := by
    rw [Multiset.mem_singleton.mp hp] at hx; exact absurd hx (Multiset.notMem_zero _)
  filter_empty T := by simp [emptyCuts, Multiset.filter_singleton]

/-! ### The weighted coproduct -/

/-- The step of the fold computing the weighted coproduct pairs the node rebuilt from its children
    with its weighted coproduct. -/
noncomputable def comulTreeEpsStep (ε : R) (a : α)
    (bs : Multiset (UnorderedTree α ×
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)))) :
    UnorderedTree α × (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  (UnorderedTree.node a (bs.map Prod.fst),
    ofTree (UnorderedTree.node a (bs.map Prod.fst)) ⊗ₜ[R] 1 +
      TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap (bPlusLin a)
        (bs.map Prod.snd).prod)

private theorem fold_comulTreeEpsStep_fst (ε : R) (T : UnorderedTree α) :
    (T.fold (comulTreeEpsStep ε)).1 = T := by
  induction T with
  | node a F ih =>
    rw [UnorderedTree.fold_node, comulTreeEpsStep, Multiset.map_map]
    exact congrArg _ ((Multiset.map_congr rfl ih).trans (Multiset.map_id F))

/-- The depth-weighted coproduct of a tree ([marcolli-chomsky-berwick-2025] §1.5.2), in which an
    extraction at distance `d` from the root has weight `ε^d`. -/
noncomputable def comulTreeEps (ε : R) (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (T.fold (comulTreeEpsStep ε)).2

/-- The weighted coproduct of a node keeps the node whole, or takes the weighted coproduct of its
    children with every extracted tree one level further down. -/
theorem comulTreeEps_node (ε : R) (a : α) (F : Forest (UnorderedTree α)) :
    comulTreeEps ε (UnorderedTree.node a F) =
      ofTree (UnorderedTree.node a F) ⊗ₜ[R] 1 +
        TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap (bPlusLin a)
          (F.map (comulTreeEps ε)).prod := by
  rw [comulTreeEps, UnorderedTree.fold_node, comulTreeEpsStep, Multiset.map_map, Multiset.map_map]
  have h : Prod.fst ∘ UnorderedTree.fold (comulTreeEpsStep (R := R) (α := α) ε) = id :=
    funext (fold_comulTreeEpsStep_fst ε)
  simp only [h, Multiset.map_id]
  rfl

/-- The depth-weighted coproduct on workspaces. -/
noncomputable def comulEps (ε : R) :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  aeval (comulTreeEps ε)

@[simp] theorem comulEps_ofTree (ε : R) (T : UnorderedTree α) :
    comulEps ε (ofTree T) = comulTreeEps ε T :=
  aeval_ofTree _ T

/-- At `ε = 1` every extraction has weight `1`, and the weighted coproduct is the pruning
    coproduct. -/
theorem comulEps_one : comulEps (1 : R) = comulAlgHomN (α := α) := by
  ext T
  rw [comulEps_ofTree, comulAlgHomN_apply_ofTree]
  induction T with
  | node a F ih =>
    have hθ : (aeval fun t ↦ (1 : R) • ofTree (R := R) (T := UnorderedTree α) t) = AlgHom.id R _ :=
      algHom_ext_ofTree fun t ↦ by simp
    rw [comulTreeEps_node, hθ, Multiset.map_congr rfl ih, ← comulAlgHomN_apply_ofTree,
      ← bPlusLin_of', comulAlgHomN_bPlusLin_cocycle, comulAlgHomN_apply_of']
    rfl

/-- At `ε = 0` every tree is primitive for the weighted coproduct, since only whole components reach
    the left channel. -/
theorem comulTreeEps_zero (T : UnorderedTree α) :
    comulTreeEps (0 : R) T = ofTree T ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ofTree T := by
  induction T with
  | node a F ih =>
    have hθ : (Algebra.TensorProduct.map (aeval fun t ↦ (0 : R) • ofTree (R := R) t)
        (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))) (F.map (comulTreeEps 0)).prod =
        Algebra.TensorProduct.includeRight (of' F) := by
      rw [map_multiset_prod, Multiset.map_map, ← prod_map_ofTree, map_multiset_prod,
        Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun c hc ↦ ?_)
      simp [ih c hc]
    have hmap (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
        TensorProduct.map (aeval fun t ↦ (0 : R) • ofTree (R := R) t).toLinearMap (bPlusLin a) z =
          LinearMap.lTensor _ (bPlusLin a) (Algebra.TensorProduct.map
            (aeval fun t ↦ (0 : R) • ofTree (R := R) t) (AlgHom.id R _) z) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [comulTreeEps_node, hmap, hθ, Algebra.TensorProduct.includeRight_apply,
      LinearMap.lTensor_tmul, bPlusLin_of']

/-- At `ε = 0` the weighted coproduct is the primitive coproduct. -/
theorem comulEps_zero : comulEps (0 : R) = comulPrim (T := UnorderedTree α) :=
  comulPrim_unique _ fun T ↦ by rw [comulEps_ofTree, comulTreeEps_zero]

/-! ### The weighted coproduct modulo `ε`

Every term of the weighted coproduct but those of `ε = 0` extracts a tree and so carries a factor
of `ε`, and every term but `T ⊗ 1` has a left factor with fewer vertices than `T`. -/

/-- A product of factors each congruent modulo `ε` is congruent modulo `ε`. -/
private theorem prod_map_eq_add_smul {A ι : Type*} [CommSemiring A] [Algebra R A] (ε : R)
    (m : Multiset ι) (f g : ι → A) (h : ∀ i ∈ m, ∃ w, f i = g i + ε • w) :
    ∃ w, (m.map f).prod = (m.map g).prod + ε • w := by
  induction m using Multiset.induction with
  | empty => exact ⟨0, by simp⟩
  | cons i m ih =>
    obtain ⟨w, hw⟩ := h i (Multiset.mem_cons_self _ _)
    obtain ⟨W, hW⟩ := ih fun j hj ↦ h j (Multiset.mem_cons_of_mem hj)
    refine ⟨w * (m.map g).prod + g i * W + ε • (w * W), ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, hw, hW, Algebra.smul_def]
    ring

/-- Scaling each tree by `ε` agrees with scaling it by `0` modulo `ε`. -/
private theorem aeval_smul_ofTree_eq_add_smul (ε : R) (x : ConnesKreimer R (UnorderedTree α)) :
    ∃ y, aeval (fun t ↦ ε • ofTree (R := R) t) x =
      aeval (fun t ↦ (0 : R) • ofTree (R := R) t) x + ε • y := by
  induction x using ConnesKreimer.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨y, hy⟩ := ha; obtain ⟨z, hz⟩ := hb
    exact ⟨y + z, by rw [map_add, map_add, hy, hz, smul_add]; abel⟩
  | single A r =>
    rw [← smul_of', map_smul, map_smul,
      aeval_of', aeval_of']
    obtain ⟨y, hy⟩ := prod_map_eq_add_smul ε A (fun t ↦ ε • ofTree (R := R) t)
      (fun t ↦ (0 : R) • ofTree (R := R) t) fun t _ ↦ ⟨ofTree t, by simp⟩
    exact ⟨r • y, by rw [hy, smul_add, smul_comm r ε]⟩

private theorem map_aeval_eq_add_smul (ε : R)
    (B : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    ∃ w, TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap B z =
      TensorProduct.map (aeval fun t ↦ (0 : R) • ofTree (R := R) t).toLinearMap B z + ε • w := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨x', hx⟩ := aeval_smul_ofTree_eq_add_smul ε x
    exact ⟨x' ⊗ₜ[R] B y, by
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hx, TensorProduct.add_tmul,
        TensorProduct.smul_tmul']⟩
  | add a b ha hb =>
    obtain ⟨y, hy⟩ := ha; obtain ⟨z, hz⟩ := hb
    exact ⟨y + z, by rw [map_add, map_add, hy, hz, smul_add]; abel⟩

private theorem comulTreeEps_eq_add_smul (ε : R) (T : UnorderedTree α) :
    ∃ w, comulTreeEps ε T = comulTreeEps 0 T + ε • w := by
  induction T with
  | node a F ih =>
    obtain ⟨W, hW⟩ := prod_map_eq_add_smul ε F (comulTreeEps ε) (comulTreeEps 0) ih
    obtain ⟨V, hV⟩ := map_aeval_eq_add_smul ε (bPlusLin a) (F.map (comulTreeEps 0)).prod
    refine ⟨V + TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap
      (bPlusLin a) W, ?_⟩
    rw [comulTreeEps_node, comulTreeEps_node, hW, map_add, map_smul, hV, smul_add]
    abel

/-- The weighted coproduct agrees with its value at `ε = 0` modulo `ε`. -/
theorem comulEps_eq_add_smul (ε : R) (x : ConnesKreimer R (UnorderedTree α)) :
    ∃ y, comulEps ε x = comulEps 0 x + ε • y := by
  induction x using ConnesKreimer.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨y, hy⟩ := ha; obtain ⟨z, hz⟩ := hb
    exact ⟨y + z, by rw [map_add, map_add, hy, hz, smul_add]; abel⟩
  | single A r =>
    rw [← smul_of', map_smul, map_smul]
    simp only [comulEps, aeval_of']
    obtain ⟨y, hy⟩ := prod_map_eq_add_smul ε A (comulTreeEps ε) (comulTreeEps 0)
      fun t _ ↦ comulTreeEps_eq_add_smul ε t
    exact ⟨r • y, by rw [hy, smul_add, smul_comm r ε]⟩

variable (R) in
/-- The span of the basis tensors whose left factor has at most `k` vertices. -/
private noncomputable def leftSpan (k : ℕ) :
    Submodule R (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  Submodule.span R {z | ∃ (A : Forest (UnorderedTree α)) (y : ConnesKreimer R (UnorderedTree α)),
    (A.map UnorderedTree.numNodes).sum ≤ k ∧ z = of' A ⊗ₜ[R] y}

private theorem tmul_mem_leftSpan {k : ℕ} {A : Forest (UnorderedTree α)}
    (hA : (A.map UnorderedTree.numNodes).sum ≤ k) (y : ConnesKreimer R (UnorderedTree α)) :
    of' A ⊗ₜ[R] y ∈ leftSpan R k :=
  Submodule.subset_span ⟨A, y, hA, rfl⟩

private theorem leftSpan_mono {m n : ℕ} (h : m ≤ n) : leftSpan R (α := α) m ≤ leftSpan R n :=
  Submodule.span_mono fun _ ⟨A, y, hA, hz⟩ ↦ ⟨A, y, hA.trans h, hz⟩

private theorem mul_mem_leftSpan {m n : ℕ}
    {z w : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)}
    (hz : z ∈ leftSpan R m) (hw : w ∈ leftSpan R n) : z * w ∈ leftSpan R (m + n) := by
  have : leftSpan R (α := α) m * leftSpan R n ≤ leftSpan R (m + n) := by
    rw [leftSpan, leftSpan, Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨A, y, hA, rfl⟩, _, ⟨A', y', hA', rfl⟩, rfl⟩
    refine ⟨A + A', y * y', ?_, ?_⟩
    · rw [Multiset.map_add, Multiset.sum_add]; omega
    · show of' A ⊗ₜ[R] y * of' A' ⊗ₜ[R] y' = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, of'_add]
  exact this (Submodule.mul_mem_mul hz hw)

private theorem prod_mem_leftSpan {ι : Type*} (m : Multiset ι)
    (f : ι → ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (k : ι → ℕ) (h : ∀ i ∈ m, f i ∈ leftSpan R (k i)) :
    (m.map f).prod ∈ leftSpan R (m.map k).sum := by
  induction m using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
    rw [Algebra.TensorProduct.one_def, ← of'_zero]
    exact tmul_mem_leftSpan (by simp) 1
  | cons i m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact mul_mem_leftSpan (h i (Multiset.mem_cons_self _ _))
      (ih fun j hj ↦ h j (Multiset.mem_cons_of_mem hj))

private theorem aeval_smul_of' (ε : R) (A : Forest (UnorderedTree α)) :
    ∃ r : R, aeval (R := R) (fun t ↦ ε • ofTree (R := R) t) (of' A) = r • of' (R := R) A := by
  induction A using Multiset.induction with
  | empty => exact ⟨1, by simp⟩
  | cons t A ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨ε * r, ?_⟩
    rw [of'_cons, map_mul, hr, aeval_ofTree,
      smul_mul_smul_comm ε (ofTree (R := R) t) r (of' (R := R) A)]

private theorem map_mem_leftSpan (ε : R)
    (B : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α)) {k : ℕ}
    {z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)}
    (hz : z ∈ leftSpan R k) :
    TensorProduct.map (aeval fun t ↦ ε • ofTree (R := R) t).toLinearMap B z ∈ leftSpan R k := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A, y, hA, rfl⟩ := hz
    obtain ⟨r, hr⟩ := aeval_smul_of' ε A
    rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hr, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ r (tmul_mem_leftSpan hA _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Besides the term `T ⊗ 1`, every term of the weighted coproduct of a tree has a left factor
    with fewer vertices than the tree. -/
private theorem comulTreeEps_eq_add_mem (ε : R) (T : UnorderedTree α) :
    ∃ z ∈ leftSpan R (T.numNodes - 1), comulTreeEps ε T = ofTree T ⊗ₜ[R] 1 + z := by
  induction T with
  | node a F ih =>
    refine ⟨_, ?_, comulTreeEps_node ε a F⟩
    have h := prod_mem_leftSpan F (comulTreeEps ε) UnorderedTree.numNodes fun c hc ↦ by
      obtain ⟨z, hz, hc'⟩ := ih c hc
      rw [hc']
      refine Submodule.add_mem _ ?_ (leftSpan_mono (Nat.sub_le _ _) hz)
      rw [← of'_singleton]
      exact tmul_mem_leftSpan (by simp) _
    rw [UnorderedTree.numNodes_node, Nat.add_sub_cancel]
    exact map_mem_leftSpan ε _ h

/-! ### Weighted Merge -/

variable [DecidableEq (UnorderedTree α)]

/-- Merge weighted by Minimal Search ([marcolli-chomsky-berwick-2025] (1.5.1)) grafts each
    matching term with the weight of its extractions. -/
noncomputable def mergeOpEps (ε : R) (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost lbl S S' ∘ₗ (comulEps ε).toLinearMap

/-- At `ε = 1` weighted Merge is Merge. -/
theorem mergeOpEps_one (lbl : α) (S S' : UnorderedTree α) :
    mergeOpEps (1 : R) lbl S S' = mergeOp lbl S S' := by
  rw [mergeOpEps, comulEps_one]; rfl

/-- At `ε = 0` weighted Merge is Merge at the empty-cut enumeration. -/
theorem mergeOpEps_zero (lbl : α) (S S' : UnorderedTree α) :
    mergeOpEps (0 : R) lbl S S' = mergeOpG emptyCuts lbl S S' := by
  rw [mergeOpEps, comulEps_zero, ← comulAlgHomNG_emptyCuts]; rfl

/-- At `ε = 0` Merge vanishes on a workspace unless `S` and `S'` are both components of it
    ([marcolli-chomsky-berwick-2025] Proposition 1.5.1). This covers each form of Sideward Merge,
    in which `S` or `S'` is an accessible term of a component. -/
theorem mergeOpEps_zero_of'_of_not_le (lbl : α) {S S' : UnorderedTree α}
    {F : Forest (UnorderedTree α)} (h : ¬ ({S, S'} : Forest (UnorderedTree α)) ≤ F) :
    mergeOpEps (0 : R) lbl S S' (of' F) = 0 := by
  rw [mergeOpEps_zero, mergeOpG_apply_of', forestCutsG_emptyCuts,
    (Multiset.filter_eq_nil (p := fun p : Forest _ × Forest _ ↦ p.1 = {S, S'})).mpr
      fun p hp hpS ↦ h (by rw [← hpS, ← Multiset.mem_antidiagonal.mp hp]; exact le_self_add),
    Multiset.map_zero, Multiset.sum_zero, mul_zero]

/-- At `ε = 0` Merge commutes with a spectator tree `U` other than `S` and `S'`, whatever
    accessible terms `U` has. -/
theorem mergeOpEps_zero_ofTree_mul (lbl : α) {S S' U : UnorderedTree α} (hS : U ≠ S)
    (hS' : U ≠ S') (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpEps (0 : R) lbl S S' (ofTree U * w) = ofTree U * mergeOpEps (0 : R) lbl S S' w := by
  rw [mergeOpEps, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, map_mul, comulEps_ofTree, comulTreeEps_zero, add_mul, map_add,
    ← of'_singleton, mergePost_left_mul_eq_zero_of_not_le _ _ _ _ _ ?_, zero_add,
    mul_comm ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] _), mergePost_right_one_tmul,
    mul_comm, of'_singleton]
  intro h
  rcases Multiset.mem_cons.mp (Multiset.singleton_le.mp h) with h | h
  exacts [hS h, hS' (Multiset.mem_singleton.mp h)]

/-- At `ε = 0` a spectator workspace passes through Merge whenever neither `S` nor `S'` is one of
    its components. -/
theorem mergeOpEps_zero_of'_mul (lbl : α) {S S' : UnorderedTree α} {F : Forest (UnorderedTree α)}
    (hS : S ∉ F) (hS' : S' ∉ F) (w : ConnesKreimer R (UnorderedTree α)) :
    mergeOpEps (0 : R) lbl S S' (of' F * w) = of' F * mergeOpEps (0 : R) lbl S S' w := by
  induction F using Multiset.induction generalizing w with
  | empty => rw [of'_zero, one_mul, one_mul]
  | cons U F ih =>
    rw [Multiset.mem_cons, not_or] at hS hS'
    rw [of'_cons, mul_assoc,
      mergeOpEps_zero_ofTree_mul lbl (Ne.symm hS.1) (Ne.symm hS'.1), ih hS.2 hS'.2, ← mul_assoc]

/-- External Merge survives at `ε = 0` ([marcolli-chomsky-berwick-2025] Proposition 1.5.1), beside
    any spectator workspace that does not repeat `S` or `S'` as a component. -/
theorem mergeOpEps_zero_pair_add (lbl : α) {S S' : UnorderedTree α}
    {F : Forest (UnorderedTree α)} (hS : S ∉ F) (hS' : S' ∉ F) :
    mergeOpEps (0 : R) lbl S S' (of' (({S, S'} : Forest (UnorderedTree α)) + F)) =
      of' (({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) + F) := by
  rw [add_comm, of'_add, mergeOpEps_zero_of'_mul lbl hS hS', mergeOpEps_zero, mergeOpG_pair,
    ← of'_add, add_comm]

/-- Weighted Merge agrees with its value at `ε = 0` modulo `ε`, so External Merge and Internal
    Merge, which survive at `ε = 0`, are its leading terms ([marcolli-chomsky-berwick-2025]
    Proposition 1.5.1). -/
theorem mergeOpEps_eq_add_smul (ε : R) (lbl : α) (S S' : UnorderedTree α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    ∃ y, mergeOpEps ε lbl S S' x = mergeOpEps 0 lbl S S' x + ε • y := by
  obtain ⟨y, hy⟩ := comulEps_eq_add_smul ε x
  exact ⟨mergePost lbl S S' y, by
    rw [mergeOpEps, mergeOpEps, LinearMap.comp_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hy, map_add, map_smul]⟩

/-- Unless `S` and `S'` are both components of the workspace, weighted Merge is a multiple of `ε`,
    so every form of Sideward Merge costs at least one ([marcolli-chomsky-berwick-2025]
    Proposition 1.5.1). -/
theorem mergeOpEps_of'_eq_smul_of_not_le (ε : R) (lbl : α) {S S' : UnorderedTree α}
    {F : Forest (UnorderedTree α)} (h : ¬ ({S, S'} : Forest (UnorderedTree α)) ≤ F) :
    ∃ y, mergeOpEps ε lbl S S' (of' F) = ε • y := by
  obtain ⟨y, hy⟩ := mergeOpEps_eq_add_smul ε lbl S S' (of' F)
  exact ⟨y, by rw [hy, mergeOpEps_zero_of'_of_not_le lbl h, zero_add]⟩

private theorem mergePost_eq_zero_of_mem_leftSpan (lbl : α) {S S' : UnorderedTree α} {k : ℕ}
    (hk : k < S.numNodes + S'.numNodes)
    {z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)}
    (hz : z ∈ leftSpan R k) : mergePost lbl S S' z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A, y, hA, rfl⟩ := hz
    rw [mergePost_basis_tensor, ite_eq_right]
    rintro rfl
    simp [Multiset.insert_eq_cons] at hA
    omega
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- External Merge has weight `1` at every `ε` ([marcolli-chomsky-berwick-2025]
    Proposition 1.5.1), since its two objects are taken whole, at no cost. -/
theorem mergeOpEps_pair (ε : R) (lbl : α) (S S' : UnorderedTree α) :
    mergeOpEps ε lbl S S' (of' ({S, S'} : Forest (UnorderedTree α))) =
      of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) := by
  obtain ⟨z, hz, hS⟩ := comulTreeEps_eq_add_mem ε S
  obtain ⟨z', hz', hS'⟩ := comulTreeEps_eq_add_mem ε S'
  have hpos := S.numNodes_pos
  have hpos' := S'.numNodes_pos
  have h1 : ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) ∈ leftSpan R S.numNodes := by
    rw [← of'_singleton]; exact tmul_mem_leftSpan (by simp) _
  have h2 : ofTree S' ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) ∈
      leftSpan R S'.numNodes := by
    rw [← of'_singleton]; exact tmul_mem_leftSpan (by simp) _
  have hrest : ofTree S ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) * z' +
      z * (ofTree S' ⊗ₜ[R] 1) + z * z' ∈ leftSpan R (S.numNodes + S'.numNodes - 1) :=
    Submodule.add_mem _ (Submodule.add_mem _
      (leftSpan_mono (by omega) (mul_mem_leftSpan h1 hz'))
      (leftSpan_mono (by omega) (mul_mem_leftSpan hz h2)))
      (leftSpan_mono (by omega) (mul_mem_leftSpan hz hz'))
  rw [mergeOpEps, LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulEps, aeval_of',
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, hS, hS',
    show ∀ a b c d : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α),
      (a + b) * (c + d) = a * c + (a * d + b * c + b * d) from fun a b c d ↦ by ring,
    map_add, mergePost_eq_zero_of_mem_leftSpan lbl (by omega) hrest, add_zero,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_singleton, ← of'_add,
    mergePost_basis_tensor, ite_eq_left (show ({S} : Forest (UnorderedTree α)) + {S'} = {S, S'}
      from rfl), mul_one]
  rfl

/-- Internal Merge has weight `1` at every `ε` ([marcolli-chomsky-berwick-2025]
    Proposition 1.5.1), since its unit stage is weightless and its second stage merges two
    components. -/
theorem mergeOpEps_im_composition (ε : R) (lbl : α) (β T Q : UnorderedTree α)
    (p0 : Forest (UnorderedTree α) × UnorderedTree α)
    (h_filter : (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (UnorderedTree α))) = {p0})
    (h_remainder : p0.2 = Q) (hTβ : T ≠ β) :
    mergeOpEps ε lbl Q β (mergeOpUnit (R := R) β (of' ({T} : Forest (UnorderedTree α)))) =
      of' ({UnorderedTree.node lbl {Q, β}} : Forest (UnorderedTree α)) := by
  rw [mergeOpUnit, mergeOpUnitG_apply_singleton_unique β T p0 h_filter hTβ, h_remainder,
    ← of'_singleton, ← of'_add, add_comm]
  exact mergeOpEps_pair ε lbl Q β

end Minimalist.Merge
