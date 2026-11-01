module

public import Linglib.Logic.ComparativeProbability.Basic
public import Linglib.Logic.ComparativeProbability.Content
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Representability of qualitative probability orders

This file defines representability: a relation on events is representable when a probability
measure induces it. Agreement on disjoint comparisons suffices, a null complement can be
dropped, and representability descends along any injection of carriers.
`CancellationFin4.lean` derives representability up to four atoms from Scott cancellation, and
`Completeness.lean` holds Kraft, Pratt and Seidenberg's five-atom order, which is not
representable.

## Main statements

* `Representable`: the representability predicate on relations.
* `reduce_to_disjoint`: agreement on disjoint comparisons suffices.
* `Representable.of_image`: representability ascends past a null complement.
* `Representable.of_preimage`: representability descends along an injection.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

open MeasureTheory

namespace ComparativeProbability

/-- A relation on events is **representable** when some probability measure induces it. -/
def Representable {W : Type*} [MeasurableSpace W] (r : Set W → Set W → Prop) : Prop :=
  ∃ μ : Measure W, IsProbabilityMeasure μ ∧ inducedGe μ = r

attribute [local instance] Classical.propDecidable

/-! ### Reductions -/

/-- Agreement on disjoint pairs suffices for full representability, since additivity reduces
    every comparison to a disjoint one. -/
theorem reduce_to_disjoint {W : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {r : Set W → Set W → Prop} [IsQualitativeAdditive r] (μ : Measure W) [IsFiniteMeasure μ]
    (h : ∀ C D : Set W, Disjoint C D → (r C D ↔ μ D ≤ μ C)) : inducedGe μ = r := by
  funext A B
  rw [qadd (r := r) A B]
  exact propext ((Measure.measure_le_iff_sdiff_le μ B A).trans (h _ _ disjoint_sdiff_sdiff).symm)

/-! ### Transport along maps -/

/-- Representability ascends along a map `f` whose range has a null complement: if comparing
    sets by their images under `f` is represented by `μ`, then `r` is represented by `μ.map f`,
    since removing the null complement changes no comparison. -/
theorem Representable.of_image {W α : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] {r : Set W → Set W → Prop}
    [IsQualitativeProbability r] {f : α → W} (hnull : r ∅ (Set.range f)ᶜ)
    (h : Representable (Set.image f ⁻¹'o r)) : Representable r := by
  obtain ⟨μ, _, hμ⟩ := h
  have hmap (C : Set W) : μ.map f C = μ (f ⁻¹' C) := Measure.map_apply .of_discrete .of_discrete
  refine ⟨μ.map f, inferInstance, funext₂ fun A B ↦ propext ?_⟩
  rw [← rel_sdiff_sdiff_iff hnull, Set.sdiff_compl, Set.sdiff_compl,
    ← Set.image_preimage_eq_inter_range, ← Set.image_preimage_eq_inter_range]
  exact iff_of_eq (by rw [inducedGe, hmap, hmap]; exact congrFun₂ hμ _ _)

/-- Representability descends along an injection `f`: if comparing sets by their preimages under
    `f` is represented by `μ`, then `r` is represented by `μ.comap f`, which weights each set by
    its image. The sets outside the range of `f` are null for `μ`, as `r` is reflexive. -/
theorem Representable.of_preimage {W α : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] {r : Set W → Set W → Prop} [Std.Refl r]
    {f : W → α} (hf : Function.Injective f) (h : Representable (Set.preimage f ⁻¹'o r)) :
    Representable r := by
  obtain ⟨μ, _, hμ⟩ := h
  have hnull : μ (Set.range f)ᶜ = 0 := by
    have : inducedGe μ ∅ (Set.range f)ᶜ := hμ ▸ by simpa [Order.Preimage] using refl_of r ∅
    simpa [inducedGe] using this
  have hcomap (A : Set W) : μ.comap f A = μ (f '' A) :=
    Measure.comap_apply _ hf (fun _ _ ↦ .of_discrete) μ .of_discrete
  refine ⟨μ.comap f, isProbabilityMeasure_comap hf (ae_iff.mpr hnull) fun _ _ ↦ .of_discrete,
    funext₂ fun A B ↦ ?_⟩
  simpa [inducedGe, hcomap, Order.Preimage, Set.preimage_image_eq _ hf] using
    congrFun₂ hμ (f '' A) (f '' B)

end ComparativeProbability
