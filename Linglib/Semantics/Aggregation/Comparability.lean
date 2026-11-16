module

public import Linglib.Semantics.Aggregation.Basic
public import Linglib.Semantics.MeasurementTheory.Difference
public import Linglib.Semantics.MeasurementTheory.Extensive
public import Linglib.Semantics.MeasurementTheory.Scale

import Mathlib.Tactic.Linarith

/-!
# Comparability classes from what the individuals share

A profile measures each object for each individual, and two profiles carry the same information when
they measure the same qualitative facts. Which class of changes of scale relates them depends on
what those facts are and on what the individuals share. When each individual only orders the
objects, the profiles differ by [a strictly increasing map for
each](##Aggregation.forall_le_iff_le_iff_exists_mem_ordinal); when one order ranks the
object–individual pairs, [by one such map for
all](##Aggregation.forall_uncurry_le_iff_iff_exists_mem_ordinalLevel). When each individual has
differences of its own, the profiles differ by [a positive affine map for
each](##Aggregation.exists_mem_cardinal_smul_eq); when the differences are comparable across
individuals, [by positive affine maps with a common
unit](##Aggregation.exists_mem_cardinalUnit_smul_eq); and when all values are degrees of one kind,
[by one positive affine map](##Aggregation.exists_mem_cardinalFull_smul_eq). Additive quantities
give the similarities, [one for each](##Aggregation.exists_mem_ratio_smul_eq) or [one for
all](##Aggregation.exists_mem_ratioFull_smul_eq).

## Implementation notes

The ordinal cases take a finite set of objects and values in an ordered field, where two measures
that order alike differ by an order automorphism of the field; on an infinite set they need differ
only by a map on the range of the first.

## References

* [sen-1970]
* [krantz-1971]
* [blackorby-donaldson-weymark-1990]
-/

@[expose] public section

namespace Aggregation

open Function MeasurementTheory

variable {ι α : Type*}

/-! ### Orders -/

section Ordinal

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {v w : Profile ι α K}

/-- Two profiles order the objects alike for each individual exactly when they differ by a strictly
increasing map for each. -/
theorem forall_le_iff_le_iff_exists_mem_ordinal [Finite α] :
    (∀ i x y, w x i ≤ w y i ↔ v x i ≤ v y i) ↔ ∃ f ∈ ordinal ι K, w = f • v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose g hg using fun i ↦ exists_orderIso_comp_eq (μ := (v · i)) (ν := (w · i)) (h i)
    exact ⟨fun i ↦ (g i).toOrderEmbedding, mem_ordinal _, funext₂ fun x i ↦ congrFun (hg i) x⟩
  · rintro ⟨f, -, rfl⟩ i x y
    exact (f i).le_iff_le

/-- Two profiles order the object–individual pairs alike exactly when they differ by one strictly
increasing map applied to every individual. -/
theorem forall_uncurry_le_iff_iff_exists_mem_ordinalLevel [Finite α] [Finite ι] :
    (∀ p q : α × ι, uncurry w p ≤ uncurry w q ↔ uncurry v p ≤ uncurry v q) ↔
      ∃ f ∈ ordinalLevel ι K, w = f • v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨g, hg⟩ := exists_orderIso_comp_eq (μ := uncurry v) (ν := uncurry w) h
    exact ⟨const ι g.toOrderEmbedding, ⟨_, rfl⟩, funext₂ fun x i ↦ congrFun hg (x, i)⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩ p q
    exact u.le_iff_le

end Ordinal

/-! ### Differences -/

section Difference

/-- Profiles measuring each individual's own differences differ by a positive affine map for
each. -/
theorem exists_mem_cardinal_smul_eq {V P : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, LinearOrder (V i)] [∀ i, IsOrderedAddMonoid (V i)] [∀ i, AddTorsor (V i) (P i)]
    {φ ψ : ∀ i, P i → ℝ} (hφ : ∀ i, IsDifferenceMeasure (φ i))
    (hψ : ∀ i, IsDifferenceMeasure (ψ i)) (d : ∀ i, α → P i) :
    ∃ f ∈ cardinal ι ℝ, (fun x i ↦ ψ i (d i x)) = f • fun x i ↦ φ i (d i x) := by
  choose u hu huψ using fun i ↦ exists_mem_positiveAffine_comp_eq (hφ i) (hψ i)
  refine ⟨fun i ↦ (u i).toOrderEmbedding, fun i _ ↦ ?_, funext₂ fun x i ↦ congrFun (huψ i) (d i x)⟩
  obtain ⟨c, hc, b, h⟩ := hu i
  exact ⟨c, hc, b, h⟩

variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- Profiles measuring differences that are comparable across individuals, each individual with
an origin of its own, differ by positive affine maps with a common unit. -/
theorem exists_mem_cardinalUnit_smul_eq {P : ι → Type*} [∀ i, AddTorsor V (P i)]
    {φ ψ : ∀ i, P i → ℝ}
    (hφ : ∀ i j (a b : P i) (c d : P j), φ i a - φ i b ≤ φ j c - φ j d ↔ a -ᵥ b ≤ c -ᵥ d)
    (hψ : ∀ i j (a b : P i) (c d : P j), ψ i a - ψ i b ≤ ψ j c - ψ j d ↔ a -ᵥ b ≤ c -ᵥ d)
    (d : ∀ i, α → P i) :
    ∃ f ∈ cardinalUnit ι ℝ, (fun x i ↦ ψ i (d i x)) = f • fun x i ↦ φ i (d i x) := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · exact ⟨fun i ↦ isEmptyElim i, ⟨1, one_pos, fun i ↦ isEmptyElim i, fun i ↦ isEmptyElim i⟩,
      funext₂ fun _ i ↦ isEmptyElim i⟩
  -- a difference has one measure, whichever individual's degrees realize it
  have key {χ : ∀ i, P i → ℝ}
      (hχ : ∀ i j (a b : P i) (c d : P j), χ i a - χ i b ≤ χ j c - χ j d ↔ a -ᵥ b ≤ c -ᵥ d)
      (hχ₀ : IsDifferenceMeasure (χ i₀)) (i : ι) (a b : P i) :
      χ i a - χ i b = hχ₀.toOrderAddMonoidHom (a -ᵥ b) := by
    rw [← vadd_vsub (a -ᵥ b) (Classical.arbitrary (P i₀)),
      IsDifferenceMeasure.toOrderAddMonoidHom_vsub]
    exact le_antisymm ((hχ i i₀ _ _ _ _).2 (by simp)) ((hχ i₀ i _ _ _ _).2 (by simp))
  have hφ₀ : IsDifferenceMeasure (φ i₀) := hφ i₀ i₀
  have hψ₀ : IsDifferenceMeasure (ψ i₀) := hψ i₀ i₀
  obtain ⟨c, hc, h⟩ := hφ₀.toOrderAddMonoidHom.exists_pos_forall_eq_mul hψ₀.toOrderAddMonoidHom
    hφ₀.toOrderAddMonoidHom_injective hψ₀.toOrderAddMonoidHom_injective
  let b : ι → ℝ := fun i ↦ ψ i (Classical.arbitrary (P i)) - c * φ i (Classical.arbitrary (P i))
  refine ⟨fun i ↦ ((OrderIso.mulLeft₀ c hc).trans (OrderIso.addRight (b i))).toOrderEmbedding,
    ⟨c, hc, b, fun i t ↦ by simp⟩, funext₂ fun x i ↦ ?_⟩
  have := key hψ hψ₀ i (d i x) (Classical.arbitrary (P i))
  rw [h, ← key hφ hφ₀] at this
  change ψ i (d i x) = c * φ i (d i x) + b i
  simp only [b]
  linarith

/-- Profiles measuring degrees of one kind for every individual differ by one positive affine map
applied to every individual. -/
theorem exists_mem_cardinalFull_smul_eq {P : Type*} [AddTorsor V P] {φ ψ : P → ℝ}
    (hφ : IsDifferenceMeasure φ) (hψ : IsDifferenceMeasure ψ) (d : α → ι → P) :
    ∃ f ∈ cardinalFull ι ℝ, (fun x i ↦ ψ (d x i)) = f • fun x i ↦ φ (d x i) := by
  obtain ⟨u, ⟨c, hc, b, hu⟩, rfl⟩ := exists_mem_positiveAffine_comp_eq hφ hψ
  exact ⟨const ι u.toOrderEmbedding, ⟨_, ⟨c, hc, b, hu⟩, rfl⟩, rfl⟩

end Difference

/-! ### Additive quantities -/

section Extensive

/-- Profiles measuring each individual's own additive quantities differ by a similarity for
each. -/
theorem exists_mem_ratio_smul_eq {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, LinearOrder (M i)] [∀ i, IsOrderedAddMonoid (M i)] (f g : ∀ i, M i →+o ℝ)
    (hf : ∀ i, Injective (f i)) (hg : ∀ i, Injective (g i)) (d : ∀ i, α → M i) :
    ∃ u ∈ ratio ι ℝ, (fun x i ↦ g i (d i x)) = u • fun x i ↦ f i (d i x) := by
  choose u hu hgu using fun i ↦ exists_mem_similarity_comp_eq (f i) (g i) (hf i) (hg i)
  refine ⟨fun i ↦ (u i).toOrderEmbedding, mem_ratio.2 fun i ↦ ?_,
    funext₂ fun x i ↦ congrFun (hgu i) (d i x)⟩
  obtain ⟨c, hc, h⟩ := hu i
  exact ⟨c, hc, h⟩

/-- Profiles measuring additive quantities of one kind for every individual differ by one
similarity applied to every individual. -/
theorem exists_mem_ratioFull_smul_eq {M : Type*} [AddCommGroup M] [LinearOrder M]
    [IsOrderedAddMonoid M] (f g : M →+o ℝ) (hf : Injective f) (hg : Injective g)
    (d : α → ι → M) :
    ∃ u ∈ ratioFull ι ℝ, (fun x i ↦ g (d x i)) = u • fun x i ↦ f (d x i) := by
  obtain ⟨u, ⟨c, hc, hu⟩, hgu⟩ := exists_mem_similarity_comp_eq f g hf hg
  exact ⟨const ι u.toOrderEmbedding, ⟨_, ⟨c, hc, hu⟩, rfl⟩,
    funext₂ fun x i ↦ congrFun hgu (d x i)⟩

end Extensive

end Aggregation
