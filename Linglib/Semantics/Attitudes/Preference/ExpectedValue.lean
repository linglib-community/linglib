module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.ConditionalProbability
public import Linglib.Semantics.MeasurementTheory.Intermediate

/-!
# Expected value of a proposition

We define the expected value of a proposition `φ : Set W`, for a prior `μ : Measure W` and a value
function `V : W → ℝ` on worlds, as the average of `V` over `φ`:
`expectedValue μ V φ = ⨍ w in φ, V w ∂μ`. It is the integral of `V` against the prior conditioned
on `φ`, `∫ w, V w ∂μ[|φ]`, and on a finite set of worlds it is the weighted sum
`(∑ w ∈ φ, μ {w} * V w) / ∑ w ∈ φ, μ {w}`. This is the measure of the goodness of a proposition
in [lassiter-2017], which takes it from [jeffrey-1965]. Relative to a domain `D` of worlds the
expected value of `φ` is that of `D ∩ φ`, which is the expected value of `φ` under the prior
conditioned on `D`.

For disjoint `φ` and `ψ` the expected value of `φ ∪ ψ` is the average of the expected values of
`φ` and `ψ` weighted by their probabilities. It therefore lies between them, and strictly between
them when they differ and both propositions have positive probability, so expected value is an
intermediate measure of propositions. A positive affine change of the value function changes every
expected value by the same map, so comparisons of expected value are invariant under such changes.

The pair of a prior and a value function is determined by the expected values only up to a larger
family of changes, given in [jeffrey-1965]. For reals `a`, `b`, `c`, `d` with `c * V + d` positive,
the prior with density `c * V + d` and the value function `(a * V + b) / (c * V + d)` give every
proposition of positive probability the expected value `(a * x + b) / (c * x + d)`, where `x` is
its expected value under the original pair, and multiply its probability by `c * x + d`. The
positive affine changes are the case `c = 0`, `d = 1`.

## Main definitions

* `Desire.expectedValue`: the average of a value function over a proposition.

## Main results

* `Desire.expectedValue_eq_integral_cond`: expected value as an integral against the conditioned
  prior.
* `Desire.expectedValue_cond`: conditioning the prior on a domain restricts the proposition to it.
* `Desire.expectedValue_union`: the expected value of a disjoint union is a weighted average.
* `Desire.isIntermediate_expectedValue`: expected value is an intermediate measure.
* `Desire.expectedValue_union_mem_Ioo`: the expected value of a disjoint union of propositions of
  positive probability lies strictly between unequal expected values.
* `Desire.invariant_positiveAffine_expectedValue_le`: comparisons of expected value are invariant
  under positive affine changes of the value function.
* `Desire.expectedValue_withDensity_fractionalLinear`: reweighting the prior by `c * V + d` and
  dividing the value function by it changes expected values by a fractional linear map.
* `Desire.withDensity_real_apply_eq_mul_expectedValue`: the reweighted probability of a
  proposition.

## Implementation notes

The definition is mathlib's `MeasureTheory.average` of a restricted measure, so the expected value
of a proposition of probability zero is `0`, where [lassiter-2017] leaves it undefined. With that
value `isIntermediate_expectedValue` needs no hypothesis that the propositions have positive
probability: when one of two disjoint propositions is null, their union has the expected value of
the other.

## References

* [lassiter-2017]
* [jeffrey-1965]
-/

@[expose] public section

namespace Desire

open MeasureTheory ProbabilityTheory MeasurementTheory Set

variable {W : Type*} [MeasurableSpace W] (μ : Measure W) (V : W → ℝ) (φ : Set W)

/-- The expected value of the proposition `φ` is the average over `φ` of the value function `V`
with respect to the prior `μ`. -/
-- [lassiter-2017] (7.22)
noncomputable def expectedValue : ℝ := ⨍ w in φ, V w ∂μ

variable {μ V φ} {ψ D : Set W}

/-- The expected value of `φ` is the expectation of the value function under the prior conditioned
on `φ`. -/
theorem expectedValue_eq_integral_cond : expectedValue μ V φ = ∫ w, V w ∂μ[|φ] :=
  setAverage_eq' μ V φ

variable [IsFiniteMeasure μ]

/-- On finitely many worlds the expected value of `φ` is the sum of the values of its worlds
weighted by their conditional probabilities given `φ`. -/
-- [lassiter-2017] (7.22)
theorem expectedValue_eq_sum [Fintype W] [MeasurableSingletonClass W] [DecidablePred (· ∈ φ)] :
    expectedValue μ V φ = (∑ w with w ∈ φ, μ.real {w} * V w) / ∑ w with w ∈ φ, μ.real {w} := by
  have hden : ∑ w with w ∈ φ, μ.real {w} = μ.real φ := by
    rw [sum_measureReal_singleton]
    congr 1
    ext w
    simp
  have hnum : ∑ w with w ∈ φ, μ.real {w} * V w = ∫ w in φ, V w ∂μ := by
    rw [integral_fintype .of_finite, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [smul_eq_mul, measureReal_restrict_apply (measurableSet_singleton w)]
    by_cases hw : w ∈ φ <;> simp [hw]
  rw [hden, hnum, expectedValue, setAverage_eq, smul_eq_mul, inv_mul_eq_div]

/-- The expected value of `φ` under the prior conditioned on a domain `D` is the expected value of
`D ∩ φ`. -/
theorem expectedValue_cond (hD : MeasurableSet D) (hφ : MeasurableSet φ) :
    expectedValue μ[|D] V φ = expectedValue μ V (D ∩ φ) := by
  rw [expectedValue_eq_integral_cond, expectedValue_eq_integral_cond,
    cond_cond_eq_cond_inter hD hφ]

/-! ### Disjoint unions -/

section Union

variable (hd : Disjoint φ ψ) (hψ : MeasurableSet ψ) (hV : Integrable V μ)
include hd hψ hV

/-- The expected value of a disjoint union is the average of the expected values of its parts
weighted by their probabilities. -/
-- [lassiter-2017] p. 188
theorem expectedValue_union :
    expectedValue μ V (φ ∪ ψ) =
      μ.real φ / (μ.real φ + μ.real ψ) * expectedValue μ V φ +
        μ.real ψ / (μ.real φ + μ.real ψ) * expectedValue μ V ψ :=
  average_union hd.aedisjoint hψ.nullMeasurableSet (measure_ne_top _ _) (measure_ne_top _ _)
    hV.integrableOn hV.integrableOn

theorem expectedValue_union_mem_uIcc :
    expectedValue μ V (φ ∪ ψ) ∈ uIcc (expectedValue μ V φ) (expectedValue μ V ψ) :=
  (segment_eq_uIcc _ _).subset <| average_union_mem_segment hd.aedisjoint hψ.nullMeasurableSet
    (measure_ne_top _ _) (measure_ne_top _ _) hV.integrableOn hV.integrableOn

/-- The expected value of a disjoint union of propositions of positive probability lies strictly
between their expected values when these differ. -/
-- [lassiter-2017] (7.18)
theorem expectedValue_union_mem_Ioo (hφ₀ : μ φ ≠ 0) (hψ₀ : μ ψ ≠ 0)
    (h : expectedValue μ V ψ < expectedValue μ V φ) :
    expectedValue μ V (φ ∪ ψ) ∈ Ioo (expectedValue μ V ψ) (expectedValue μ V φ) := by
  rw [← openSegment_eq_Ioo h, openSegment_symm]
  exact average_union_mem_openSegment hd.aedisjoint hψ.nullMeasurableSet hφ₀ hψ₀
    (measure_ne_top _ _) (measure_ne_top _ _) hV.integrableOn hV.integrableOn

end Union

/-- Expected value is an intermediate measure of propositions. -/
-- [lassiter-2017] (7.18), p. 188
theorem isIntermediate_expectedValue [DiscreteMeasurableSpace W] (hV : Integrable V μ) :
    IsIntermediate (expectedValue μ V) :=
  fun _ _ hd ↦ expectedValue_union_mem_uIcc hd .of_discrete hV

/-! ### Changes of the value function -/

-- [lassiter-2017] pp. 187–188
theorem expectedValue_const_mul_add_const (hφ : μ φ ≠ 0) (hV : Integrable V μ) (a b : ℝ) :
    expectedValue μ (fun w ↦ a * V w + b) φ = a * expectedValue μ V φ + b := by
  have := cond_isProbabilityMeasure hφ
  have hV' : Integrable V μ[|φ] := hV.restrict.smul_measure (by simp [hφ])
  simp only [expectedValue_eq_integral_cond]
  rw [integral_add (hV'.const_mul a) (integrable_const b), integral_const_mul, integral_const,
    probReal_univ, one_smul]

/-- A positive affine change of the value function changes the expected value of a proposition of
positive probability by the same map. -/
theorem expectedValue_smul (hφ : μ φ ≠ 0) (hV : Integrable V μ) {g : ℝ ↪o ℝ}
    (hg : g ∈ positiveAffine) : expectedValue μ (g • V) φ = g (expectedValue μ V φ) := by
  obtain ⟨a, -, b, hg⟩ := hg
  rw [show g • V = fun w ↦ a * V w + b from funext fun w ↦ hg (V w),
    expectedValue_const_mul_add_const hφ hV, hg]

/-- Comparisons of expected value are invariant under positive affine changes of the value
function. -/
theorem invariant_positiveAffine_expectedValue_le [Finite W] [MeasurableSingletonClass W]
    (hφ : μ φ ≠ 0) (hψ : μ ψ ≠ 0) :
    Invariant (positiveAffine : Set (ℝ ↪o ℝ)) fun V : W → ℝ ↦
      expectedValue μ V ψ ≤ expectedValue μ V φ :=
  fun g hg V ↦ by
    beta_reduce
    rw [expectedValue_smul hψ .of_finite hg, expectedValue_smul hφ .of_finite hg, g.le_iff_le]

/-! ### Fractional linear changes -/

section FractionalLinear

variable {c d : ℝ}

/-- Reweighting the prior by `c * V + d` multiplies the probability of a proposition by the value
of `c * x + d` at its expected value. -/
-- [jeffrey-1965] (6-1)
theorem withDensity_real_apply_eq_mul_expectedValue (hV : Integrable V μ)
    (hpos : ∀ w, 0 < c * V w + d) :
    (μ.withDensity fun w ↦ ENNReal.ofReal (c * V w + d)).real φ =
      μ.real φ * (c * expectedValue μ V φ + d) := by
  have hint : IntegrableOn (fun w ↦ c * V w + d) φ μ :=
    ((hV.const_mul c).add (integrable_const d)).integrableOn
  rw [measureReal_def, withDensity_apply' _ φ,
    ← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun w ↦ (hpos w).le),
    ENNReal.toReal_ofReal (integral_nonneg fun w ↦ (hpos w).le),
    integral_add (hV.const_mul c).integrableOn (integrable_const d).integrableOn,
    integral_const_mul, integral_const, ← measure_smul_setAverage V (measure_ne_top μ φ),
    measureReal_restrict_apply_univ, expectedValue]
  simp only [smul_eq_mul]
  ring

/-- Reweighting the prior by `c * V + d` and dividing the value function `a * V + b` by the same
weight sends the expected value of every proposition of positive probability through the
fractional linear map `x ↦ (a * x + b) / (c * x + d)`. -/
-- [jeffrey-1965] (6-2)
theorem expectedValue_withDensity_fractionalLinear (hφ : μ φ ≠ 0) (hm : Measurable V)
    (hV : Integrable V μ) (hpos : ∀ w, 0 < c * V w + d) (a b : ℝ) :
    expectedValue (μ.withDensity fun w ↦ ENNReal.ofReal (c * V w + d))
        (fun w ↦ (a * V w + b) / (c * V w + d)) φ =
      (a * expectedValue μ V φ + b) / (c * expectedValue μ V φ + d) := by
  have hw (w : W) : (ENNReal.ofReal (c * V w + d)).toReal • ((a * V w + b) / (c * V w + d)) =
      a * V w + b := by
    rw [ENNReal.toReal_ofReal (hpos w).le, smul_eq_mul, mul_div_cancel₀ _ (hpos w).ne']
  rw [expectedValue, setAverage_eq, withDensity_real_apply_eq_mul_expectedValue hV hpos,
    setIntegral_withDensity_eq_setIntegral_toReal_smul' φ
      ((hm.const_mul c).add_const d).ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [hw]
  rw [integral_add (hV.const_mul a).integrableOn (integrable_const b).integrableOn,
    integral_const_mul, integral_const, ← measure_smul_setAverage V (measure_ne_top μ φ),
    measureReal_restrict_apply_univ, ← expectedValue, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_left_comm, ← mul_add, inv_mul_eq_div,
    mul_div_mul_left _ _ ((measureReal_ne_zero_iff (measure_ne_top μ φ)).2 hφ)]

end FractionalLinear

end Desire
