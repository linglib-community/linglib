module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The softmax kernel of an extended-real score

This file defines `ProbabilityTheory.Kernel.softmax`, the kernel whose row at `w` is proportional
to the exponential of an extended-real score. A point of score `⊥` gets no mass, so the score
both ranks the points and says which of them are available.

## Main definitions

* `ProbabilityTheory.Kernel.softmax`: the weight kernel of `EReal.exp (score w u)`.

## Main results

* `ProbabilityTheory.Kernel.softmax_coe_eq_count_tilted`,
  `ProbabilityTheory.Kernel.softmax_coe_real_singleton`: a real score gives each row the counting
  measure tilted by the score, whose atoms are `Real.softmax` of the score.
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

theorem isMarkovKernel_softmax (h0 : ∀ w, ∃ u, score w u ≠ ⊥)
    (htop : ∀ w u, score w u ≠ ⊤) : IsMarkovKernel (softmax score) :=
  isMarkovKernel_ofWeights (fun w ↦ (h0 w).imp fun _ hu ↦ mt EReal.exp_eq_zero_iff.mp hu)
    fun w u ↦ mt EReal.exp_eq_top_iff.mp (htop w u)

variable [MeasurableSingletonClass β]

@[simp] theorem softmax_apply_singleton (score : α → β → EReal) (w : α) (u : β) :
    softmax score w {u} = EReal.exp (score w u) / ∑ u', EReal.exp (score w u') :=
  ofWeights_apply_singleton _ w u

theorem softmax_apply_singleton_eq_zero {w : α} {u : β} (h : score w u = ⊥) :
    softmax score w {u} = 0 :=
  ofWeights_apply_singleton_eq_zero (by rw [h, EReal.exp_bot])

theorem softmax_apply_singleton_ne_zero {w : α} {u : β} (h : score w u ≠ ⊥)
    (htop : ∀ u', score w u' ≠ ⊤) : softmax score w {u} ≠ 0 :=
  ofWeights_apply_singleton_ne_zero (mt EReal.exp_eq_zero_iff.mp h)
    fun u' ↦ mt EReal.exp_eq_top_iff.mp (htop u')

theorem softmax_apply_eq_of_add {w₁ w₂ : α} {k : ℝ} (h : ∀ u, score w₂ u = score w₁ u + k) :
    softmax score w₂ = softmax score w₁ :=
  ofWeights_apply_eq_of_mul (mt EReal.exp_eq_zero_iff.mp (EReal.coe_ne_bot k))
    (mt EReal.exp_eq_top_iff.mp (EReal.coe_ne_top k)) fun u ↦ by rw [h, EReal.exp_add]

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

theorem softmax_eq_tilted (htop : ∀ u, score w u ≠ ⊤) (h0 : ∃ u, score w u ≠ ⊥) :
    softmax score w =
      (uniformOn {u | score w u ≠ ⊥}).tilted fun u ↦ (score w u).toReal := by
  set S : Set β := {u | score w u ≠ ⊥}
  have := isProbabilityMeasure_uniformOn S.toFinite h0
  have hw (u : β) : EReal.exp (score w u) ≠ ⊤ := mt EReal.exp_eq_top_iff.mp (htop u)
  have : IsProbabilityMeasure (softmax score w) :=
    isProbabilityMeasure_ofWeights (h0.imp fun _ hu ↦ mt EReal.exp_eq_zero_iff.mp hu) hw
  have he (u : β) : (EReal.exp (score w u)).toReal =
      S.indicator (fun u ↦ Real.exp (score w u).toReal) u := by
    by_cases hu : score w u = ⊥
    · rw [hu, EReal.exp_bot, ENNReal.toReal_zero, Set.indicator_of_notMem (by simpa [S] using hu)]
    · rw [Set.indicator_of_mem hu, ← EReal.coe_toReal (htop u) hu, EReal.exp_coe,
        ENNReal.toReal_ofReal (Real.exp_pos _).le, EReal.toReal_coe]
  have hn : (0 : ℝ) < S.ncard := Nat.cast_pos.2 ((Set.ncard_pos S.toFinite).2 h0)
  have hZ : 0 < ∑ u, (EReal.exp (score w u)).toReal := by
    obtain ⟨u, hu⟩ := h0
    refine (Finset.sum_pos_iff_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg).2 ⟨u, by simp, ?_⟩
    rw [he, Set.indicator_of_mem hu]
    exact Real.exp_pos _
  refine (eq_tilted_iff _ _ _).2 ⟨(∑ u, (EReal.exp (score w u)).toReal) / S.ncard,
    by positivity, fun u ↦ ?_⟩
  rw [softmax, ofWeights_real_singleton _ w hw, uniformOn_real_apply_of_finite S.toFinite, he]
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu, Set.inter_singleton_of_mem hu, Set.ncard_singleton,
      Nat.cast_one]
    field_simp
  · rw [Set.indicator_of_notMem hu, Set.inter_singleton_eq_empty.2 hu]
    simp

theorem softmax_coe_eq_count_tilted [Nonempty β] (f : α → β → ℝ) (w : α) :
    softmax (fun w u ↦ (f w u : EReal)) w = Measure.count.tilted (f w) := by
  rw [softmax_eq_tilted (score := fun w u ↦ (f w u : EReal)) (w := w)
    (fun _ ↦ EReal.coe_ne_top _) ⟨Classical.arbitrary β, EReal.coe_ne_bot _⟩]
  simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true, Set.ofPred_true, EReal.toReal_coe]
  exact uniformOn_univ_tilted

theorem softmax_coe_real_singleton (f : α → β → ℝ) (w : α) (u : β) :
    (softmax (fun w u ↦ (f w u : EReal)) w).real {u} = Real.softmax (f w) u := by
  have : Nonempty β := ⟨u⟩
  rw [softmax_coe_eq_count_tilted, count_tilted_real_singleton]

/-- A real-valued score excludes no point, so row preference is comparison of reals. -/
theorem softmax_coe_real_singleton_lt_iff (f : α → β → ℝ) (w : α) {u u' : β} :
    (softmax (fun w u ↦ (f w u : EReal)) w).real {u} <
        (softmax (fun w u ↦ (f w u : EReal)) w).real {u'} ↔ f w u < f w u' := by
  have : Nonempty β := ⟨u⟩
  rw [softmax_coe_real_singleton, softmax_coe_real_singleton, Real.softmax_lt_softmax_iff]

theorem freeEnergy_softmax (htop : ∀ u, score w u ≠ ⊤) (h0 : ∃ u, score w u ≠ ⊥) :
    (uniformOn {u | score w u ≠ ⊥}).freeEnergy (fun u ↦ (score w u).toReal)
        (softmax score w) =
      cgf (fun u ↦ (score w u).toReal) (uniformOn {u | score w u ≠ ⊥}) 1 := by
  have := isProbabilityMeasure_uniformOn (Set.toFinite {u | score w u ≠ ⊥}) h0
  rw [softmax_eq_tilted htop h0]
  exact freeEnergy_tilted _ .of_finite .of_finite .of_finite

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
