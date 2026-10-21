module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Core.Probability.Kernel.OfWeights
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The softmax kernel of an extended-real score

This file defines `ProbabilityTheory.Kernel.softmax`, the kernel whose row at `w` is proportional
to the exponential of an extended-real score. A point of score `⊥` gets no mass, so the score
both ranks the points and says which of them are available.

## Main definitions

* `ProbabilityTheory.Kernel.softmax`: the weight kernel of `EReal.exp (score w u)`.

## Main results

* `ProbabilityTheory.Kernel.softmax_coe_real_singleton`: a real score gives each row
  `Real.softmax` of the score.
* `ProbabilityTheory.Kernel.softmax_real_singleton_lt_iff`: row preference is score comparison.
* `ProbabilityTheory.Kernel.softmax_real_singleton_of_pair`: with two available points the share
  of one is the logistic function of the score difference.
* `ProbabilityTheory.Kernel.softmax_eq_tilted`,
  `ProbabilityTheory.Kernel.isGreatest_freeEnergy_softmax`: a row is the uniform measure on the
  available points tilted by the score, and so maximizes the expected score less the divergence
  from that uniform measure, by the Gibbs variational principle.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

section Softmax

variable [Countable α] [MeasurableSingletonClass α] [Fintype β] {score : α → β → EReal}

/-- The softmax kernel of an extended-real score has row `w` proportional to the exponential of the
score, so a point of score `⊥` gets no mass. -/
noncomputable def softmax (score : α → β → EReal) : Kernel α β :=
  ofWeights fun w u ↦ EReal.exp (score w u)

instance (score : α → β → EReal) : IsFiniteKernel (softmax score) :=
  inferInstanceAs (IsFiniteKernel (ofWeights _))

/-- The softmax kernel is a probability kernel whenever every row has a point of score above `⊥`
and no score is `⊤`. -/
theorem isMarkovKernel_softmax (h0 : ∀ w, ∃ u, score w u ≠ ⊥)
    (htop : ∀ w u, score w u ≠ ⊤) : IsMarkovKernel (softmax score) :=
  isMarkovKernel_ofWeights (fun w ↦ (h0 w).imp fun _ hu ↦ mt EReal.exp_eq_zero_iff.mp hu)
    fun w u ↦ mt EReal.exp_eq_top_iff.mp (htop w u)

variable [MeasurableSingletonClass β]

@[simp] theorem softmax_apply_singleton (score : α → β → EReal) (w : α) (u : β) :
    softmax score w {u} = EReal.exp (score w u) / ∑ u', EReal.exp (score w u') :=
  ofWeights_apply_singleton _ w u

/-- A point of score `⊥` gets no mass. -/
theorem softmax_apply_singleton_eq_zero {w : α} {u : β} (h : score w u = ⊥) :
    softmax score w {u} = 0 :=
  ofWeights_apply_singleton_eq_zero (by rw [h, EReal.exp_bot])

/-- A point of score above `⊥` gets positive mass when no score is `⊤`. -/
theorem softmax_apply_singleton_ne_zero {w : α} {u : β} (h : score w u ≠ ⊥)
    (htop : ∀ u', score w u' ≠ ⊤) : softmax score w {u} ≠ 0 :=
  ofWeights_apply_singleton_ne_zero (mt EReal.exp_eq_zero_iff.mp h)
    fun u' ↦ mt EReal.exp_eq_top_iff.mp (htop u')

/-- Two rows whose scores differ by a real constant are the same. -/
theorem softmax_apply_eq_of_add {w₁ w₂ : α} {k : ℝ} (h : ∀ u, score w₂ u = score w₁ u + k) :
    softmax score w₂ = softmax score w₁ :=
  ofWeights_apply_eq_of_mul (mt EReal.exp_eq_zero_iff.mp (EReal.coe_ne_bot k))
    (mt EReal.exp_eq_top_iff.mp (EReal.coe_ne_top k)) fun u ↦ by rw [h, EReal.exp_add]

/-- Two scores differing by a real constant per row give the same kernel, since a term that does
not depend on the point cancels in the normalization. -/
theorem softmax_eq_of_add {score' : α → β → EReal} {k : α → ℝ}
    (h : ∀ w u, score' w u = score w u + k w) : softmax score' = softmax score :=
  ofWeights_eq_of_mul (fun w ↦ mt EReal.exp_eq_zero_iff.mp (EReal.coe_ne_bot (k w)))
    (fun w ↦ mt EReal.exp_eq_top_iff.mp (EReal.coe_ne_top (k w))) fun w u ↦ by
      rw [h, EReal.exp_add]

/-- Row preference of the softmax kernel is score comparison, since the normalization cancels. -/
theorem softmax_real_singleton_lt_iff {w : α} (htop : ∀ u, score w u ≠ ⊤)
    (h0 : ∃ u, score w u ≠ ⊥) {u u' : β} :
    (softmax score w).real {u} < (softmax score w).real {u'} ↔
      score w u < score w u' := by
  rw [softmax, ofWeights_real_singleton_lt_iff w
      (fun h ↦ let ⟨u₀, hu₀⟩ := h0
        hu₀ (EReal.exp_eq_zero_iff.mp (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _))))
      (ENNReal.sum_ne_top.mpr fun u _ ↦ mt EReal.exp_eq_top_iff.mp (htop u)),
    EReal.exp_lt_exp_iff]

/-- A real-valued score gives each row the softmax of the score. -/
theorem softmax_coe_real_singleton (f : α → β → ℝ) (w : α) (u : β) :
    (softmax (fun w u ↦ (f w u : EReal)) w).real {u} = Real.softmax (f w) u := by
  rw [softmax, ofWeights_real_singleton _ w fun u ↦ mt EReal.exp_eq_top_iff.mp (EReal.coe_ne_top _),
    Real.softmax_apply]
  simp only [EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- A real-valued score excludes no point, so row preference is comparison of reals. -/
theorem softmax_coe_real_singleton_lt_iff (f : α → β → ℝ) (w : α) {u u' : β} :
    (softmax (fun w u ↦ (f w u : EReal)) w).real {u} <
        (softmax (fun w u ↦ (f w u : EReal)) w).real {u'} ↔ f w u < f w u' := by
  have : Nonempty β := ⟨u⟩
  rw [softmax_coe_real_singleton, softmax_coe_real_singleton, Real.softmax_lt_softmax_iff]

/-- When exactly two points of a row have score above `⊥`, the share of one is the logistic
function of the score difference. -/
theorem softmax_real_singleton_of_pair {w : α} {u u' : β} (huu' : u ≠ u')
    (hu : score w u ≠ ⊥) (hu' : score w u' ≠ ⊥) (htop : ∀ v, score w v ≠ ⊤)
    (hsupp : ∀ v, score w v ≠ ⊥ → v = u ∨ v = u') :
    (softmax score w).real {u} =
      Real.sigmoid ((score w u).toReal - (score w u').toReal) := by
  rw [softmax, ofWeights_real_singleton_of_pair w huu'
      (fun v ↦ mt EReal.exp_eq_top_iff.mp (htop v))
      (fun v hv ↦ hsupp v (mt EReal.exp_eq_zero_iff.mpr hv)),
    ← EReal.coe_toReal (htop u) hu, ← EReal.coe_toReal (htop u') hu', EReal.exp_coe,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.exp_div_add_exp_eq_sigmoid, EReal.toReal_coe,
    EReal.toReal_coe]

end Softmax

/-! ### The softmax row as a Gibbs measure -/

section Gibbs

open InformationTheory

variable [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  {score : α → β → EReal} {w : α}

/-- A row of the softmax kernel is the uniform measure on the points of score above `⊥`, tilted by
the score. -/
theorem softmax_eq_tilted (htop : ∀ u, score w u ≠ ⊤) (h0 : ∃ u, score w u ≠ ⊥) :
    softmax score w =
      (uniformOn {u | score w u ≠ ⊥}).tilted fun u ↦ (score w u).toReal := by
  classical
  set S : Set β := {u | score w u ≠ ⊥}
  have := isProbabilityMeasure_uniformOn S.toFinite h0
  set c : ℝ := ((Measure.count S)⁻¹).toReal
  have hc : c ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨ENNReal.inv_ne_zero.2 (Measure.count_apply_lt_top.2 S.toFinite).ne,
      ENNReal.inv_ne_top.2 (Measure.count_ne_zero_iff.2 h0)⟩
  have hν (b : β) : (uniformOn S).real {b} = S.indicator (fun _ ↦ c) b := by
    rw [measureReal_def, uniformOn, cond_apply S.toFinite.measurableSet]
    by_cases hb : b ∈ S
    · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hb), Measure.count_singleton, mul_one,
        Set.indicator_of_mem hb]
    · rw [Set.inter_singleton_eq_empty.2 hb, measure_empty, mul_zero, ENNReal.toReal_zero,
        Set.indicator_of_notMem hb]
  have he (b : β) : (EReal.exp (score w b)).toReal =
      S.indicator (fun b ↦ Real.exp (score w b).toReal) b := by
    by_cases hb : score w b = ⊥
    · rw [hb, EReal.exp_bot, ENNReal.toReal_zero, Set.indicator_of_notMem (by simpa [S] using hb)]
    · rw [Set.indicator_of_mem hb, ← EReal.coe_toReal (htop b) hb, EReal.exp_coe,
        ENNReal.toReal_ofReal (Real.exp_pos _).le, EReal.toReal_coe]
  have key (b : β) : S.indicator (fun _ ↦ c) b * Real.exp (score w b).toReal =
      c * S.indicator (fun b ↦ Real.exp (score w b).toReal) b := by
    by_cases hb : b ∈ S <;> simp [hb]
  refine Measure.ext_iff_singleton.2 fun a ↦ ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, softmax,
    ofWeights_real_singleton (fun w u ↦ EReal.exp (score w u)) w
      (fun u ↦ mt EReal.exp_eq_top_iff.mp (htop u)),
    tilted_real_singleton]
  simp_rw [he, hν, key, ← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- A row of the softmax kernel attains the log partition function as its free energy relative to
the uniform measure on the points of score above `⊥`. -/
theorem freeEnergy_softmax (htop : ∀ u, score w u ≠ ⊤) (h0 : ∃ u, score w u ≠ ⊥) :
    (uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal)
        (softmax score w) =
      cgf (fun u ↦ (score w u).toReal) (uniformOn {u | score w u ≠ ⊥}) 1 := by
  have := isProbabilityMeasure_uniformOn (Set.toFinite {u | score w u ≠ ⊥}) h0
  rw [softmax_eq_tilted htop h0]
  exact freeEnergy_tilted _ .of_finite .of_finite .of_finite

/-- A row of the softmax kernel is the Gibbs optimizer. Among the distributions absolutely
continuous with respect to the uniform measure on the points of score above `⊥`, it has the
greatest expected score less divergence from that uniform measure. -/
theorem isGreatest_freeEnergy_softmax (htop : ∀ u, score w u ≠ ⊤)
    (h0 : ∃ u, score w u ≠ ⊥) :
    IsGreatest ((uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal) ''
        {q | IsProbabilityMeasure q ∧ q ≪ uniformOn {u | score w u ≠ ⊥} ∧
          Integrable (llr q (uniformOn {u | score w u ≠ ⊥})) q ∧
          Integrable (fun u ↦ (score w u).toReal) q})
      ((uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal)
        (softmax score w)) := by
  have := isProbabilityMeasure_uniformOn (Set.toFinite {u | score w u ≠ ⊥}) h0
  rw [freeEnergy_softmax htop h0]
  exact isGreatest_cgf _ .of_finite .of_finite .of_finite

end Gibbs

end ProbabilityTheory.Kernel
