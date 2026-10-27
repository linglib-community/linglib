/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Processing.Surprisal.Generalized
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Studies.Levy2008

/-!
# Meister, Giulianelli and Pimentel (2024): Towards a Similarity-Adjusted Surprisal Theory

Similarity-adjusted surprisal is the negative logarithm of the expected similarity of a language
model's alternatives to the observed word, and similarity-adjusted entropy, Ricotta and Szeidl's
diversity index, is its expectation. Both are generalized surprisal in the sense of Giulianelli,
Opedal and Cotterell, with the negative logarithm and a similarity score. The identity
similarity regards different words as completely distinct and recovers surprisal and Shannon
entropy.

## Implementation notes

* Scores take the alternative first and the target second; the paper writes the similarity with
  the target first.
* Theorem 1 assumes an integrable distance and information values below one, where the paper's
  similarity-adjusted surprisal is finite; `Real.log 0 = 0` would make the infinite value zero.
* Theorem 3 is stated over Levy's structures, each yielding one string (footnote 7), and reads
  the ratio in (20b) as a Radon–Nikodym derivative. Under the identity similarity the posterior
  (17d) is Bayes' (`simAdjPosterior_indicatorScore`).
* `tendsto_simAdjSurprisal_rpow` assumes the similarity below one off the diagonal, which the
  normalized cosine (7) satisfies only when distinct words have non-parallel embeddings.

## Errata

* (19a) writes the target as `w'`, the variable (19b) sums over; it is `w_t`.
* (19c) and (19d) hold only for meanings that yield `w_t`, the ones (20b) weighs; for another
  meaning, the sum in (19b) is the similarity of `w_t` to that meaning's word.

## TODO

* The reading-time regressions (Tables 1–4, Fig. 1).

## References

* [meister-giulianelli-pimentel-2024]
* [giulianelli-opedal-cotterell-2024]
* [levy-2008]
* [ricotta-szeidl-2006]
-/

@[expose] public section

namespace MeisterGiulianelliPimentel2024

open InformationTheory MeasureTheory ProbabilityTheory Surprisal Real Filter Topology

variable {C A W : Type*} [MeasurableSpace C] [MeasurableSpace A]

/-- Similarity-adjusted surprisal (Definition 1, eq. (6)): the negative logarithm of the expected
similarity `z` of the alternatives to the target. -/
noncomputable def simAdjSurprisal (L : Kernel C A) (z : A → W → C → ℝ) : C → W → ℝ :=
  genSurprisal L (fun x ↦ -log x) z

/-- Similarity-adjusted entropy (eq. (4)): the expected similarity-adjusted surprisal of the
alternatives. -/
noncomputable def simAdjEntropy (L : Kernel C A) (z : A → A → C → ℝ) (c : C) : ℝ :=
  ∫ a, simAdjSurprisal L z c a ∂(L c)

/-! ### Identity and class similarity -/

section indicatorScore

variable [MeasurableSpace W] [MeasurableSingletonClass W] (L : Kernel C W) (c : C)

theorem simAdjSurprisal_indicatorScore (w : W) :
    simAdjSurprisal L indicatorScore c w = surprisal (L c) w :=
  genSurprisal_negLog_indicatorScore L c w

/-- With the identity similarity, similarity-adjusted entropy is Shannon entropy (p. 16487)
((4)). -/
theorem simAdjEntropy_indicatorScore [Countable W] [IsMarkovKernel L]
    (hL : Integrable (surprisal (L c)) (L c)) :
    simAdjEntropy L indicatorScore c = Hm[L c] := by
  simp only [simAdjEntropy, simAdjSurprisal_indicatorScore]
  exact (measureEntropy_eq_integral_surprisal _ hL).symm

omit [MeasurableSingletonClass W] in
/-- The part-of-speech similarity (eq. (8)) is one when the tagger `f` puts the two words in
the same class, and then similarity-adjusted surprisal is the surprisal of the target's class. -/
theorem simAdjSurprisal_indicatorScore_comp {V : Type*} [MeasurableSpace V]
    [MeasurableSingletonClass V] {f : C → W → V} (hf : Measurable (f c)) (w : W) :
    simAdjSurprisal L (fun a w c ↦ indicatorScore (f c a) (f c w) c) c w =
      surprisal ((L c).map (f c)) (f c w) := by
  have (a : W) : ({f c w} : Set V).indicator (1 : V → ℝ) (f c a) =
      (f c ⁻¹' {f c w}).indicator 1 a := (Set.indicator_comp_right _).symm
  simp only [simAdjSurprisal, genSurprisal, indicatorScore, surprisal, this]
  rw [integral_indicator_one (hf (measurableSet_singleton _)),
    map_measureReal_apply hf (measurableSet_singleton _)]

end indicatorScore

/-- Raising the similarity to the power `α` (App. E.1): as `α` grows, similarity-adjusted
surprisal tends to surprisal when the similarity is one on the diagonal and below one off it. -/
theorem tendsto_simAdjSurprisal_rpow [MeasurableSpace W] [MeasurableSingletonClass W]
    (L : Kernel C W) [IsFiniteKernel L] {z : W → W → C → ℝ} {c : C} {w : W}
    (hm : Measurable fun a ↦ z a w c) (h0 : ∀ a, 0 ≤ z a w c) (hw : z w w c = 1)
    (h1 : ∀ a ≠ w, z a w c < 1) (hL : L c {w} ≠ 0) :
    Tendsto (fun α : ℝ ↦ simAdjSurprisal L (z ^ α) c w) atTop
      (𝓝 (surprisal (L c) w)) := by
  have hle (a : W) : z a w c ≤ 1 := by
    rcases eq_or_ne a w with rfl | ha
    exacts [hw.le, (h1 a ha).le]
  have hlim : Tendsto (fun α : ℝ ↦ ∫ a, z a w c ^ α ∂(L c)) atTop
      (𝓝 (∫ a, indicatorScore a w c ∂(L c))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
      (.of_forall fun α ↦ (hm.pow_const α).aestronglyMeasurable) ?_ (integrable_const 1)
      (.of_forall fun a ↦ ?_)
    · filter_upwards [eventually_ge_atTop 0] with α hα
      exact .of_forall fun a ↦ by
        rw [norm_of_nonneg (rpow_nonneg (h0 a) α)]
        exact rpow_le_one (h0 a) (hle a) hα
    · rcases eq_or_ne a w with rfl | ha
      · simp [indicatorScore, hw]
      · simpa [indicatorScore, ha] using
          tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le (h0 a)) (h1 a ha)
  simp only [indicatorScore, integral_indicator_one (measurableSet_singleton w)] at hlim
  exact ((continuousAt_log (ENNReal.toReal_ne_zero.2 ⟨hL, measure_ne_top _ _⟩)).neg.tendsto).comp
    hlim

/-! ### Information value -/

section informationValue

variable (L : Kernel C A) [IsMarkovKernel L] (d : A → W → C → ℝ)

theorem simAdjSurprisal_one_sub {c : C} {w : W} (hd : Integrable (fun a ↦ d a w c) (L c)) :
    simAdjSurprisal L (1 - d) c w = -log (1 - informationValue L d c w) := by
  simp only [simAdjSurprisal, informationValue, genSurprisal, id, Pi.sub_apply, Pi.one_apply,
    integral_sub (integrable_const 1) hd, integral_const, probReal_univ, one_smul]

/-- Theorem 1 (eqs. (11)–(12)): with the similarity one minus the distance, similarity-adjusted
surprisal increases strictly with information value. -/
theorem simAdjSurprisal_lt_simAdjSurprisal_iff {c c' : C} {w w' : W}
    (hd : Integrable (fun a ↦ d a w c) (L c)) (hd' : Integrable (fun a ↦ d a w' c') (L c'))
    (h : informationValue L d c w < 1) (h' : informationValue L d c' w' < 1) :
    simAdjSurprisal L (1 - d) c w < simAdjSurprisal L (1 - d) c' w' ↔
      informationValue L d c w < informationValue L d c' w' := by
  rw [simAdjSurprisal_one_sub L d hd, simAdjSurprisal_one_sub L d hd', neg_lt_neg_iff,
    log_lt_log_iff (sub_pos.2 h') (sub_pos.2 h), sub_lt_sub_iff_left]

end informationValue

/-! ### Processing cost -/

section cost

open Levy2008 AutoregressiveSequenceModel

variable {T : Type*} [MeasurableSpace T] [MeasurableSpace W] (P : Measure T) (str : T → List W)
  (z : Option W → Option W → List W → ℝ) (ws : List W) (w : W)

/-- The similarity-adjusted posterior (17d): the posterior after `ws`, weighted by the similarity
of the target to the symbol each structure yields next, over the expected similarity (17a). -/
noncomputable def simAdjPosterior : Measure T :=
  (posterior P str ws).withDensity fun t ↦ .ofReal (z (str t)[ws.length]? (some w) ws /
    ∫ a, z a (some w) ws ∂(ofMeasure (P.map str)).next ws)

/-- The similarity-adjusted processing cost (20a–b): the expected log-likelihood ratio, under the
posterior after the target, of the similarity-adjusted posterior to the posterior before it. -/
noncomputable def simAdjCost : ℝ :=
  ∫ t, llr (simAdjPosterior P str z ws w) (posterior P str ws) t ∂posterior P str (ws ++ [w])

variable [DiscreteMeasurableSpace T] [IsProbabilityMeasure P]

theorem simAdjPosterior_indicatorScore [MeasurableSingletonClass W]
    (h : P (consistent str (ws ++ [w])) ≠ 0) :
    simAdjPosterior P str indicatorScore ws w = posterior P str (ws ++ [w]) := by
  have hws : P (consistent str ws) ≠ 0 :=
    fun h0 ↦ h (measure_mono_null (consistent_anti str (List.prefix_append ws [w])) h0)
  have : IsProbabilityMeasure (posterior P str ws) := cond_isProbabilityMeasure hws
  have hp : ∫ a, indicatorScore a (some w) ws ∂(ofMeasure (P.map str)).next ws =
      (posterior P str ws).real (consistent str (ws ++ [w])) := by
    simp only [indicatorScore]
    rw [integral_indicator_one (measurableSet_singleton _), measureReal_def, measureReal_def,
      posterior_consistent_append]
  have hE : posterior P str ws (consistent str (ws ++ [w])) ≠ 0 := by
    rw [posterior, cond_apply_of_subset .of_discrete
      (consistent_anti str (List.prefix_append ws [w]))]
    exact ENNReal.div_ne_zero.2 ⟨h, measure_ne_top _ _⟩
  have hρ : (fun t ↦ ENNReal.ofReal (indicatorScore (str t)[ws.length]? (some w) ws /
      (posterior P str ws).real (consistent str (ws ++ [w])))) =ᵐ[posterior P str ws]
      (consistent str (ws ++ [w])).indicator fun _ ↦
        (posterior P str ws (consistent str (ws ++ [w])))⁻¹ := by
    filter_upwards [ae_cond_mem (μ := P) (MeasurableSet.of_discrete (s := consistent str ws))]
      with t ⟨r, hr⟩
    have hnext : (str t)[ws.length]? = r.head? := by
      rw [← hr]
      cases r <;> simp
    have hmem : t ∈ consistent str (ws ++ [w]) ↔ r.head? = some w := by
      simp only [consistent, Set.mem_preimage, Set.mem_ofPred_eq, ← hr,
        List.prefix_append_right_inj]
      cases r <;> simp [eq_comm]
    by_cases ht : t ∈ consistent str (ws ++ [w])
    · rw [Set.indicator_of_mem ht, hnext, hmem.1 ht, measureReal_def, indicatorScore,
        Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_div,
        ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hE (measure_ne_top _ _)),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · rw [Set.indicator_of_notMem ht, hnext, indicatorScore,
        Set.indicator_of_notMem (Set.notMem_singleton_iff.2 (mt hmem.2 ht)), zero_div,
        ENNReal.ofReal_zero]
  simp only [simAdjPosterior, hp]
  rw [withDensity_congr_ae hρ, withDensity_indicator .of_discrete, withDensity_const,
    ← posterior_incremental]
  rfl

/-- Theorem 3 (eq. (18)): the similarity-adjusted processing cost is similarity-adjusted
surprisal. -/
theorem simAdjCost_eq_simAdjSurprisal (h : P (consistent str (ws ++ [w])) ≠ 0)
    (hz : z (some w) (some w) ws = 1) (hz0 : ∀ a, 0 ≤ z a (some w) ws) :
    simAdjCost P str z ws w = simAdjSurprisal (ofMeasure (P.map str)).next z ws (some w) := by
  have hws : P (consistent str ws) ≠ 0 :=
    fun h0 ↦ h (measure_mono_null (consistent_anti str (List.prefix_append ws [w])) h0)
  have : IsProbabilityMeasure (posterior P str ws) := cond_isProbabilityMeasure hws
  have : IsProbabilityMeasure (posterior P str (ws ++ [w])) := cond_isProbabilityMeasure h
  have hac : posterior P str (ws ++ [w]) ≪ posterior P str ws :=
    posterior_incremental P str ws w ▸ cond_absolutelyContinuous
  have hp : 0 ≤ ∫ a, z a (some w) ws ∂(ofMeasure (P.map str)).next ws := integral_nonneg hz0
  have hae : ∀ᵐ t ∂posterior P str (ws ++ [w]), llr (simAdjPosterior P str z ws w)
      (posterior P str ws) t = -log (∫ a, z a (some w) ws ∂(ofMeasure (P.map str)).next ws) := by
    filter_upwards [hac.ae_le (Measure.rnDeriv_withDensity _ .of_discrete),
      ae_cond_mem (μ := P) (MeasurableSet.of_discrete (s := consistent str (ws ++ [w])))]
      with t ht ⟨r, hr⟩
    have hnext : (str t)[ws.length]? = some w := by simp [← hr]
    rw [llr, simAdjPosterior, ht, hnext, hz, ENNReal.toReal_ofReal (by positivity), one_div,
      log_inv]
  rw [simAdjCost, integral_congr_ae hae, integral_const, probReal_univ, one_smul]
  rfl

theorem simAdjCost_indicatorScore [MeasurableSingletonClass W]
    (h : P (consistent str (ws ++ [w])) ≠ 0) :
    simAdjCost P str indicatorScore ws w =
      (klDiv (posterior P str (ws ++ [w])) (posterior P str ws)).toReal := by
  rw [simAdjCost_eq_simAdjSurprisal P str _ ws w h (by simp [indicatorScore])
      fun a ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) a,
    simAdjSurprisal_indicatorScore, klDiv_posterior_eq_surprisal P str ws w h]
  exact (ENNReal.toReal_ofReal
    (neg_nonneg.2 (log_nonpos measureReal_nonneg measureReal_le_one))).symm

end cost

end MeisterGiulianelliPimentel2024
