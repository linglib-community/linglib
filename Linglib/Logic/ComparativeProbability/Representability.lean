module

public import Linglib.Logic.ComparativeProbability.Basic
public import Linglib.Logic.ComparativeProbability.Content
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Representability of qualitative probability orders

This file defines representability: a relation on events is representable when a probability
measure induces it. Agreement on disjoint comparisons suffices, a null atom can be dropped, and
representability descends along any injection of carriers. `CancellationFin4.lean` derives
representability up to four atoms from Scott cancellation, and `Completeness.lean` holds Kraft,
Pratt and Seidenberg's five-atom order, which is not representable.

## Main statements

* `Representable`: the representability predicate on relations.
* `reduce_to_disjoint`: agreement on disjoint comparisons suffices.
* `null_elem_reduce`: representability past a null atom.
* `Representable.of_preimage`: representability descends along an injection.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

/-- A relation on events is **representable** when some probability measure induces it. -/
def Representable {W : Type*} [MeasurableSpace W] (r : Set W → Set W → Prop) : Prop :=
  ∃ μ : Measure W, IsProbabilityMeasure μ ∧ μ.inducedGe = r

attribute [local instance] Classical.propDecidable

/-! ### Reductions -/

/-- Agreement on disjoint pairs suffices for full representability, since additivity reduces
    every comparison to a disjoint one. -/
theorem reduce_to_disjoint {W : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {r : Set W → Set W → Prop} [IsQualitativeAdditive r] (μ : Measure W) [IsFiniteMeasure μ]
    (h : ∀ C D : Set W, Disjoint C D → (r C D ↔ μ D ≤ μ C)) : μ.inducedGe = r := by
  funext A B
  rw [qadd (r := r) A B]
  exact propext ((Measure.measure_le_iff_sdiff_le μ B A).trans (h _ _ disjoint_sdiff_sdiff).symm)

theorem null_removal_disjoint {W : Type*} {r : Set W → Set W → Prop}
    [IsQualitativeProbability r] (j : W) (hj : r ∅ {j}) (C D : Set W) (hdisj : Disjoint C D) :
    r C D ↔ r (C \ {j}) (D \ {j}) := by
  have null_sub : ∀ S : Set W, r (S \ {j}) S := by
    intro S
    by_cases hj_in : j ∈ S
    · rw [qadd (r := r) (S \ {j}) S, Set.sdiff_eq_empty.mpr Set.sdiff_subset,
        Set.sdiff_sdiff_cancel_left (Set.singleton_subset_iff.mpr hj_in)]
      exact hj
    · rw [Set.sdiff_singleton_eq_self hj_in]; exact refl_of r S
  by_cases hjC : j ∈ C
  · rw [Set.sdiff_singleton_eq_self (Set.disjoint_left.mp hdisj hjC)]
    exact ⟨fun h ↦ trans_of r (null_sub C) h, fun h ↦ trans_of r (mono _ _ Set.sdiff_subset) h⟩
  · rw [Set.sdiff_singleton_eq_self hjC]
    by_cases hjD : j ∈ D
    · exact ⟨fun h ↦ trans_of r h (mono _ _ Set.sdiff_subset), fun h ↦ trans_of r h (null_sub D)⟩
    · rw [Set.sdiff_singleton_eq_self hjD]

private theorem succ_image_preimage {n : ℕ} (S : Set (Fin (n + 1))) :
    Fin.succ '' (Fin.succ ⁻¹' S) = S \ {(0 : Fin (n + 1))} := by
  rw [Set.image_preimage_eq_range_inter, Fin.range_succ]
  ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_sdiff]; exact And.comm

/-- If atom `0` is null in a qualitative probability on `Fin (n+2)` and some atom is not,
    representability reduces along `Fin.succ` to `Fin (n+1)`. -/
theorem null_elem_reduce {n : ℕ} (r : Set (Fin (n + 2)) → Set (Fin (n + 2)) → Prop)
    [IsQualitativeProbability r] (hn0 : r ∅ {0}) (hnn : ∃ i : Fin (n + 1), ¬r ∅ {Fin.succ i})
    (sub_repr : ∀ r' : Set (Fin (n + 1)) → Set (Fin (n + 1)) → Prop,
      IsQualitativeProbability r' → Representable r') :
    Representable r := by
  have hnt : ¬r ∅ (Set.range (Fin.succ : Fin (n + 1) → Fin (n + 2))) := by
    obtain ⟨i, hi⟩ := hnn
    exact fun h ↦ hi (trans_of r h (mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_range_self i))))
  obtain ⟨μ, hμ, hm⟩ := sub_repr _ (isQualitativeProbability_image (Fin.succ_injective _) hnt)
  -- push the sub-measure forward (the null element gets weight 0)
  have hmap : ∀ C, μ.map Fin.succ C = μ (Fin.succ ⁻¹' C) := fun C ↦
    Measure.map_apply (.of_discrete) (.of_discrete)
  refine ⟨μ.map Fin.succ, inferInstance, reduce_to_disjoint _ fun C D hdisj ↦ ?_⟩
  rw [null_removal_disjoint 0 hn0 C D hdisj, hmap, hmap,
      ← succ_image_preimage C, ← succ_image_preimage D]
  exact iff_of_eq (congrFun₂ hm _ _).symm

/-! ### Transport along injections -/

theorem perm_null_iff {n : ℕ} (σ : Fin n ≃ Fin n) (r : Set (Fin n) → Set (Fin n) → Prop)
    (j : Fin n) : (Set.preimage σ ⁻¹'o r) ∅ {j} ↔ r ∅ {σ.symm j} := by
  show r (σ ⁻¹' ∅) (σ ⁻¹' {j}) ↔ _
  rw [Set.preimage_empty, show σ ⁻¹' {j} = {σ.symm j} by ext; simp [Equiv.eq_symm_apply]]

/-- Representability descends along an injection `f`: if comparing sets by their preimages under
    `f` is represented by `μ`, then `r` is represented by `μ.comap f`, which weights each set by
    its image. The sets outside the range of `f` are null for `μ`, as `r` is reflexive. -/
theorem Representable.of_preimage {W α : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] {r : Set W → Set W → Prop} [Std.Refl r]
    {f : W → α} (hf : Function.Injective f) (h : Representable (Set.preimage f ⁻¹'o r)) :
    Representable r := by
  obtain ⟨μ, _, hμ⟩ := h
  have hnull : μ (Set.range f)ᶜ = 0 := by
    have : μ.inducedGe ∅ (Set.range f)ᶜ := hμ ▸ by simpa [Order.Preimage] using refl_of r ∅
    simpa [Measure.inducedGe] using this
  have hcomap (A : Set W) : μ.comap f A = μ (f '' A) :=
    Measure.comap_apply _ hf (fun _ _ ↦ .of_discrete) μ .of_discrete
  refine ⟨μ.comap f, isProbabilityMeasure_comap hf (ae_iff.mpr hnull) fun _ _ ↦ .of_discrete,
    funext₂ fun A B ↦ ?_⟩
  simpa [Measure.inducedGe, hcomap, Order.Preimage, Set.preimage_image_eq _ hf] using
    congrFun₂ hμ (f '' A) (f '' B)

end ComparativeProbability
