module

public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.Kernel.OfWeights
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.UniformOn

/-!
# Tilted measures

Tilting is invariant under scaling the measure, `(c • μ).tilted f = μ.tilted f` for a finite
nonzero `c`, since the normalization absorbs the factor. On a finite type the tilt reweights each
atom by the exponential of `f` and renormalizes, so tilting the counting measure, or the uniform
measure, gives `Real.softmax f`.

Tilting commutes with pushing the measure forward along a map, when the tilting function is pulled
back along it. The counting measure does not: its pushforward counts preimages. So pushing forward
the softmax of pulled-back scores weights each point by its number of preimages, and a point that
is split into several copies gains mass.

## Main results

* `MeasureTheory.tilted_smul`: tilting is invariant under scaling the measure.
* `MeasureTheory.map_tilted_comp`: tilting commutes with pushing forward.
* `MeasureTheory.map_count_tilted_comp_real_singleton`: the pushforward of a softmax of pulled-back
  scores weights each point by its number of preimages.
* `MeasureTheory.tilted_real_singleton`, `MeasureTheory.count_tilted_real_singleton`: the tilted
  measure of an atom on a finite type.
* `MeasureTheory.uniformOn_univ_tilted`: tilting the uniform measure on a finite type is tilting
  the counting measure.
* `MeasureTheory.eq_tilted_iff`: a measure on a finite type is a tilt exactly when its atoms are
  proportional to the reweighted ones.
* `ProbabilityTheory.Kernel.ofWeights_apply_eq_tilted`: normalizing the reweighted atoms gives
  the tilt.
-/

public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

section Smul

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- Tilting is invariant under scaling the measure by a finite nonzero constant. -/
theorem tilted_smul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) : (c • μ).tilted f = μ.tilted f := by
  rw [Measure.tilted, Measure.tilted, integral_smul_measure, withDensity_smul_measure]
  by_cases hz : ∫ x, Real.exp (f x) ∂μ = 0
  · simp [hz]
  ext s hs
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  rw [Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ hc]
  refine lintegral_congr fun x ↦ ?_
  rw [smul_eq_mul, ← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_mul hc'.le,
    ENNReal.toReal_ofReal hc'.le]
  congr 1
  field_simp

/-- On a finite type, tilting the uniform measure is tilting the counting measure. -/
theorem uniformOn_univ_tilted [Fintype α] [Nonempty α] :
    (uniformOn Set.univ).tilted f = Measure.count.tilted f := by
  rw [uniformOn, ProbabilityTheory.cond, Measure.restrict_univ, tilted_smul (by simp) (by simp)]

end Smul

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

/-- On a finite type, the tilted measure at an atom is the atom's mass reweighted by the
exponential of `f` and renormalized. -/
theorem tilted_real_singleton (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (a : α) :
    (μ.tilted f).real {a} = μ.real {a} * Real.exp (f a) / ∑ b, μ.real {b} * Real.exp (f b) := by
  have hZ : 0 ≤ ∫ x, Real.exp (f x) ∂μ := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  rw [measureReal_def, tilted_apply, lintegral_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ), ← measureReal_def,
    integral_fintype .of_finite]
  simp only [smul_eq_mul]
  ring

/-- Tilting commutes with pushing forward: tilting by a function pulled back along `f` and then
pushing forward along `f` is pushing forward and then tilting. -/
theorem map_tilted_comp {β : Type*} [MeasurableSpace β] {f : β → α} (hf : Measurable f)
    {g : α → ℝ} (hg : Measurable g) (μ : Measure β) :
    (μ.tilted (g ∘ f)).map f = (μ.map f).tilted g := by
  ext s hs
  rw [Measure.map_apply hf hs, tilted_apply' _ _ (hf hs), tilted_apply' _ _ hs,
    setLIntegral_map hs (by fun_prop) hf, integral_map hf.aemeasurable (by fun_prop)]
  rfl

/-- Pushing forward the softmax of scores pulled back along `f` weights each point by its number
of preimages: a point with more copies gets more mass. -/
theorem map_count_tilted_comp_real_singleton {β : Type*} [MeasurableSpace β] [Fintype β]
    [MeasurableSingletonClass β] (f : β → α) (g : α → ℝ) (a : α) :
    ((Measure.count.tilted (g ∘ f)).map f).real {a} =
      (f ⁻¹' {a}).ncard * Real.exp (g a) / ∑ b, (f ⁻¹' {b}).ncard * Real.exp (g b) := by
  have hcount (b : α) : (Measure.count.map f).real {b} = (f ⁻¹' {b}).ncard := by
    rw [measureReal_def, Measure.map_apply .of_discrete (measurableSet_singleton b),
      Measure.count_apply_finite _ (Set.toFinite _), ENNReal.toReal_natCast,
      Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  rw [map_tilted_comp .of_discrete .of_discrete, tilted_real_singleton]
  simp_rw [hcount]

/-- On a finite type, a probability measure is the tilt of `ν` by `f` exactly when its atoms are
proportional to those of `ν` reweighted by the exponential of `f`. -/
theorem eq_tilted_iff (μ ν : Measure α) [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [NeZero ν]
    (f : α → ℝ) : μ = ν.tilted f ↔ ∃ Z > 0, ∀ a, μ.real {a} = ν.real {a} * Real.exp (f a) / Z := by
  have hZ : 0 < ∑ b, ν.real {b} * Real.exp (f b) := by
    obtain ⟨a, ha⟩ : ∃ a, ν {a} ≠ 0 := by
      by_contra! h
      exact NeZero.ne ν (Measure.ext_iff_singleton.2 fun a ↦ by simp [h a])
    exact (mul_pos (ENNReal.toReal_pos ha (measure_ne_top _ _)) (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun b _ ↦ mul_nonneg measureReal_nonneg (Real.exp_pos _).le)
        (Finset.mem_univ a))
  constructor
  · rintro rfl
    exact ⟨_, hZ, tilted_real_singleton ν f⟩
  · rintro ⟨Z, hZ0, h⟩
    have hZeq : Z = ∑ b, ν.real {b} * Real.exp (f b) := by
      have := sum_measureReal_singleton_eq_one μ
      simp_rw [h, ← Finset.sum_div] at this
      exact ((div_eq_one_iff_eq hZ0.ne').1 this).symm
    have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted .of_finite
    refine Measure.ext_iff_singleton.2 fun a ↦ ?_
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
      ← measureReal_def, ← measureReal_def, h, tilted_real_singleton, hZeq]

/-- On a finite type, normalizing the atoms of `ν` reweighted by the exponential of `f` gives the
tilt of `ν` by `f`. -/
theorem _root_.ProbabilityTheory.Kernel.ofWeights_apply_eq_tilted {ι : Type*} [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (ν : Measure α) [IsFiniteMeasure ν] [NeZero ν]
    {w : ι → α → ℝ≥0∞} {i : ι} {f : α → ℝ}
    (hw : ∀ a, w i a = ν {a} * ENNReal.ofReal (Real.exp (f a))) :
    Kernel.ofWeights w i = ν.tilted f := by
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted .of_finite
  have hfin (a : α) : w i a ≠ ∞ := by
    rw [hw]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  refine Measure.ext_iff_singleton.2 fun a ↦ ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, Kernel.ofWeights_real_singleton _ _ hfin, tilted_real_singleton]
  simp only [hw, ENNReal.toReal_mul, ENNReal.toReal_ofReal, Real.exp_nonneg, ← measureReal_def]

/-- On a finite type, the counting measure tilted by `f` gives each point its softmax
probability. -/
theorem count_tilted_real_singleton (f : α → ℝ) (a : α) :
    (Measure.count.tilted f).real {a} = Real.softmax f a := by
  simp [tilted_real_singleton, Real.softmax_apply]


end MeasureTheory
