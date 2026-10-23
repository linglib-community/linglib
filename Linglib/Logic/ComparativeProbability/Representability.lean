module

public import Linglib.Logic.ComparativeProbability.Basic
public import Linglib.Logic.ComparativeProbability.Content
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Representability of qualitative probability orders

A qualitative probability is representable when a probability measure induces it. Kraft,
Pratt and Seidenberg show that every order on at most four atoms is representable and give a
five-atom order that is not. This file holds the predicate and the
reductions to disjoint comparisons and past a null atom; `CancellationFin4.lean` derives the
cases up to four atoms from Scott cancellation, and `Completeness.lean` holds the five-atom
counterexample and its padding to every larger size.

## Main statements

* `Representable`: the representability predicate on relations.
* `reduce_to_disjoint`, `null_elem_reduce`, `perm_repr`: the reductions.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

/-- A relation on events is **representable** when some probability measure induces it. -/
def Representable {W : Type*} [MeasurableSpace W] (r : Set W → Set W → Prop) : Prop :=
  ∃ μ : Measure W, IsProbabilityMeasure μ ∧ ∀ A B, r A B ↔ μ B ≤ μ A

attribute [local instance] Classical.propDecidable

/-! ### Reductions -/

theorem reduce_to_disjoint {W : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {r : Set W → Set W → Prop} [IsQualitativeAdditive r] (μ : Measure W) [IsFiniteMeasure μ]
    (h : ∀ C D : Set W, Disjoint C D → (r C D ↔ μ D ≤ μ C)) :
    ∀ A B, r A B ↔ μ B ≤ μ A := by
  intro A B
  rw [qadd (r := r) A B]
  exact (h _ _ disjoint_sdiff_sdiff).trans (Measure.measure_le_iff_sdiff_le μ B A).symm

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
  exact hm (Fin.succ ⁻¹' C) (Fin.succ ⁻¹' D)

/-! ### Transport along equivalences -/

theorem transfer_repr {W α : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] (e : W ≃ α) (r : Set W → Set W → Prop)
    (μ : Measure α) (hm : ∀ A B : Set α, (Set.preimage e ⁻¹'o r) A B ↔ μ B ≤ μ A) :
    ∀ A B : Set W, r A B ↔ μ.map e.symm B ≤ μ.map e.symm A := by
  intro A B
  have h := hm (e '' A) (e '' B)
  simp only [Order.Preimage, Equiv.preimage_image] at h
  rwa [Measure.map_apply (.of_discrete) (.of_discrete),
    Measure.map_apply (.of_discrete) (.of_discrete), ← Equiv.image_eq_preimage_symm,
    ← Equiv.image_eq_preimage_symm]

theorem perm_null_iff {n : ℕ} (σ : Fin n ≃ Fin n) (r : Set (Fin n) → Set (Fin n) → Prop)
    (j : Fin n) : (Set.preimage σ ⁻¹'o r) ∅ {j} ↔ r ∅ {σ.symm j} := by
  show r (σ ⁻¹' ∅) (σ ⁻¹' {j}) ↔ _
  rw [Set.preimage_empty, show σ ⁻¹' {j} = {σ.symm j} by ext; simp [Equiv.eq_symm_apply]]

theorem perm_repr {W α : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] (σ : W ≃ α) (r : Set W → Set W → Prop)
    (h : Representable (Set.preimage σ ⁻¹'o r)) : Representable r := by
  obtain ⟨μ, hμ, hm⟩ := h
  exact ⟨μ.map σ.symm, inferInstance, transfer_repr σ r μ hm⟩

end ComparativeProbability
