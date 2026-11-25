module

public import Linglib.Pragmatics.Probabilistic.Literal
public import Linglib.Semantics.Exhaustification.MinimalWorlds

/-!
# The speaker and the minimal worlds

Against the literal listener, the speaker who knows the state is likelier to produce an utterance
at a state that makes fewer utterances true, since she has less to choose from there. That
comparison holds under every prior of full support, and it is the only comparison between two
states that does. The states at which some prior makes the speaker likeliest to produce an
utterance are therefore the minimal worlds of its denotation against the denotations of all the
utterances.

## Main results

* `RSA.forall_speaker_literalListener_dirac_lt_iff`: one state is a better state for an utterance
  than another under every prior exactly when it makes strictly fewer utterances true.
* `RSA.exhMW_range_eq_setOf_exists_forall_speaker_le`: minimal-world exhaustification as the
  states some prior puts on top.

## References

* [frank-goodman-2012]
* [spector-2016]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSingletonClass W]
  [Fintype W] [Fintype U] [MeasurableSingletonClass U] {α : ℝ}

/-- For every state `t` there is a prior of full support under which no state that makes true an
utterance false at `t` is a better state than `t` for any utterance. -/
theorem exists_forall_speaker_literalListener_dirac_le (hα : 0 < α) (C : U → ℝ)
    (sem : U → Set W) (t : W) :
    ∃ μ : Measure W, IsProbabilityMeasure μ ∧ (∀ x, μ {x} ≠ 0) ∧
      ∀ s u, t ∈ sem u → (∃ u', s ∈ sem u' ∧ t ∉ sem u') →
        speaker α C (literalListener μ sem) Measure.dirac s {u} ≤
          speaker α C (literalListener μ sem) Measure.dirac t {u} := by
  set K := ∑ v, Real.exp (-(α * C v))
  set M := ∑ v, |C v|
  set S := (1 + K * Real.exp (α * M)) ^ α⁻¹
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le
  have hS : 1 ≤ S := Real.one_le_rpow (le_add_of_nonneg_right (mul_nonneg hK (Real.exp_pos _).le))
    (inv_nonneg.2 hα.le)
  set ε : ℝ≥0∞ := (ENNReal.ofReal (2 * S))⁻¹
  have hε : ε ≤ 2⁻¹ := ENNReal.inv_le_inv.2 (by
    rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have hε1 : ε ≤ 1 := hε.trans (by norm_num)
  have hε0 : ε ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have : Nonempty W := ⟨t⟩
  set μ := (1 - ε) • Measure.dirac t + ε • uniformOn (Set.univ : Set W)
  have hprob : IsProbabilityMeasure μ := ⟨by simp [μ, tsub_add_cancel_of_le hε1]⟩
  have hfull (x : W) : μ {x} ≠ 0 := by
    simp only [μ, add_apply, smul_apply, smul_eq_mul]
    exact fun h ↦ mul_ne_zero hε0 (uniformOn_univ_singleton_ne_zero x) (add_eq_zero.1 h).2
  have ht : 2⁻¹ ≤ μ {t} := by
    simp only [μ, add_apply, smul_apply, smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_singleton t), mul_one]
    exact (ENNReal.one_sub_inv_two.symm.trans_le (tsub_le_tsub_left hε 1)).trans le_self_add
  have hcompl : μ {t}ᶜ ≤ ε := by
    simp only [μ, add_apply, smul_apply, smul_eq_mul,
      Measure.dirac_apply' t (MeasurableSet.singleton t).compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.2 (Set.mem_singleton t)), mul_zero, zero_add]
    exact mul_le_of_le_one_right' prob_le_one
  have key (u' : U) (hu' : t ∉ sem u') :
      ∑ v, {v | t ∈ sem v}.indicator
          (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) v ≤
        (μ (sem u'))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
    have hCu' : C u' ≤ M := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun v ↦ |C v|) (fun v _ ↦ abs_nonneg _) (Finset.mem_univ u'))
    have h1 : 1 ≤ Real.exp (α * M) * Real.exp (-(α * C u')) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have hreal : 2 ^ α * K ≤ (2 * S) ^ α * Real.exp (-(α * C u')) := by
      rw [Real.mul_rpow (by norm_num) (by linarith),
        Real.rpow_inv_rpow (by positivity) hα.ne', mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith [Real.exp_pos (-(α * C u'))]) (by positivity)
    calc ∑ v, {v | t ∈ sem v}.indicator
          (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) v
        ≤ ∑ v, 2 ^ α * ENNReal.ofReal (Real.exp (-(α * C v))) := Finset.sum_le_sum fun v _ ↦ ?_
      _ = ENNReal.ofReal (2 ^ α * K) := by
        rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ (Real.exp_pos _).le,
          ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hα.le,
          ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal ((2 * S) ^ α * Real.exp (-(α * C u'))) := ENNReal.ofReal_le_ofReal hreal
      _ = ε⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
        rw [inv_inv, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hα.le]
      _ ≤ _ := by
        gcongr
        exact (measure_mono (Set.subset_compl_singleton_iff.2 hu')).trans hcompl
    by_cases hv : t ∈ sem v
    · rw [Set.indicator_of_mem (show v ∈ {v | t ∈ sem v} from hv)]
      gcongr
      exact ENNReal.inv_le_iff_inv_le.2 (ht.trans (measure_mono (Set.singleton_subset_iff.2 hv)))
    · rw [Set.indicator_of_notMem (show v ∉ {v | t ∈ sem v} from hv)]
      exact zero_le
  refine ⟨μ, hprob, hfull, fun s u htu ⟨u', hsu', htu'⟩ ↦ ?_⟩
  by_cases hsu : s ∈ sem u
  swap
  · rw [speaker_literalListener_dirac_apply_singleton_eq_zero hα C μ sem hsu]
    exact zero_le
  rw [speaker_literalListener_apply_singleton hα (Measure.dirac_absolutelyContinuous (hfull s)),
    speaker_literalListener_apply_singleton hα (Measure.dirac_absolutelyContinuous (hfull t))]
  simp only [Measure.ae_dirac_mem_iff]
  rw [Set.indicator_of_mem (show u ∈ {v | s ∈ sem v} from hsu),
    Set.indicator_of_mem (show u ∈ {v | t ∈ sem v} from htu)]
  refine ENNReal.div_le_div_left ((key u' htu').trans ?_) _
  rw [← Set.indicator_of_mem (show u' ∈ {v | s ∈ sem v} from hsu')
    (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v))))]
  exact Finset.single_le_sum (fun v _ ↦ zero_le) (Finset.mem_univ u')

/-- One state is a better state for an utterance than another under every prior of full support
exactly when it makes strictly fewer utterances true. -/
theorem forall_speaker_literalListener_dirac_lt_iff (hα : 0 < α) (C : U → ℝ) (sem : U → Set W)
    {s t : W} {u : U} (hs : s ∈ sem u) (ht : t ∈ sem u) :
    (∀ μ : Measure W, IsProbabilityMeasure μ → (∀ x, μ {x} ≠ 0) →
      speaker α C (literalListener μ sem) Measure.dirac t {u} <
        speaker α C (literalListener μ sem) Measure.dirac s {u}) ↔
      {a | s ∈ sem a} ⊂ {a | t ∈ sem a} := by
  refine ⟨fun h ↦ ?_, fun hsub μ _ hμ ↦
    speaker_literalListener_dirac_lt_of_ssubset hα C μ sem (hμ s) (hμ t) hsub hs⟩
  obtain ⟨μ, hprob, hμ, hle⟩ := exists_forall_speaker_literalListener_dirac_le hα C sem t
  have hlt := h μ hprob hμ
  refine Set.ssubset_iff_subset_ne.2 ⟨fun v hv ↦ by_contra fun hv' ↦
    (hle s u ht ⟨v, hv, hv'⟩).not_gt hlt, fun heq ↦ ?_⟩
  rw [speaker_literalListener_dirac_congr hα C μ sem (hμ s) (hμ t) (Set.ext_iff.1 heq)] at hlt
  exact lt_irrefl _ hlt

/-- The minimal worlds of an utterance, against the denotations of all the utterances, are the
states at which some prior of full support makes the speaker likeliest to produce it. -/
theorem exhMW_range_eq_setOf_exists_forall_speaker_le (hα : 0 < α) (C : U → ℝ)
    (sem : U → Set W) (u : U) :
    Exhaustification.exhMW (Set.range sem) (sem u) =
      {t | t ∈ sem u ∧ ∃ μ : Measure W, IsProbabilityMeasure μ ∧ (∀ x, μ {x} ≠ 0) ∧
        ∀ s ∈ sem u, speaker α C (literalListener μ sem) Measure.dirac s {u} ≤
          speaker α C (literalListener μ sem) Measure.dirac t {u}} := by
  have key {x y : W} : {a ∈ Set.range sem | x ∈ a} ⊆ {a ∈ Set.range sem | y ∈ a} ↔
      {v | x ∈ sem v} ⊆ {v | y ∈ sem v} :=
    ⟨fun h v hv ↦ (h ⟨⟨v, rfl⟩, hv⟩).2, by rintro h _ ⟨⟨v, rfl⟩, hv⟩; exact ⟨⟨v, rfl⟩, h hv⟩⟩
  ext t
  refine ⟨fun ⟨htu, hmin⟩ ↦ ⟨htu, ?_⟩, fun ⟨htu, μ, _, hμ, hle⟩ ↦ ⟨htu, fun s hs hst ↦ ?_⟩⟩
  · obtain ⟨μ, hprob, hμ, hle⟩ := exists_forall_speaker_literalListener_dirac_le hα C sem t
    refine ⟨μ, hprob, hμ, fun s hs ↦ ?_⟩
    by_cases h : ∃ u', s ∈ sem u' ∧ t ∉ sem u'
    · exact hle s u htu h
    push Not at h
    have hts := key.1 (hmin hs (key.2 h))
    rw [speaker_literalListener_dirac_congr hα C μ sem (hμ t) (hμ s)
      fun v ↦ ⟨fun hv ↦ hts hv, h v⟩]
  · rw [key] at hst ⊢
    exact by_contra fun hts ↦ (hle s hs).not_gt
      (speaker_literalListener_dirac_lt_of_ssubset hα C μ sem (hμ s) (hμ t) ⟨hst, hts⟩ hs)

end RSA
