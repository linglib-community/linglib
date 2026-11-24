/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Pragmatics.Probabilistic.Listener
public import Linglib.Pragmatics.Probabilistic.Speaker

/-!
# Identifiability of the speaker's rationality and costs

The speaker of the Rational Speech Act model who knows the state chooses the utterance `u` at the
state `w` with probability proportional to `exp (α * (log (L u {w}) - C u))`, where `L` is the
listener she reasons about, `α` her rationality and `C` her costs. This file says when her choices
determine `α` and `C`.

The log odds of `u'` against `u` at `w` are
`α * (log (L u' {w}) - log (L u {w}) - (C u' - C u))`. Comparing them at two states cancels the
costs and leaves `α` times the same comparison for the listener. There are two cases.

* Where the listener's odds of two utterances differ between two states, the speaker determines
  `α`, and then her costs up to a constant.
* Where the listener's mass factors as `L u {w} = a u * h w`, the comparison is zero, and the
  speaker at one rationality is the speaker at any other with adjusted costs. The literal listener
  is of this kind: `a u` is the inverse of the prior probability that `u` is true, and `h w` is
  the prior probability of `w`.

## Main results

* `RSA.log_speaker_dirac_real_singleton_div`: the log odds of two utterances at a state.
* `RSA.log_speaker_dirac_real_singleton_div_sub`: comparing the log odds at two states cancels the
  costs.
* `RSA.rationality_eq_of_speaker_dirac_apply_eq`: where the listener's odds differ between two
  states, speakers who agree there have the same rationality.
* `RSA.cost_sub_eq_of_speaker_dirac_apply_eq`: speakers of one rationality who agree at a state
  have the same cost differences.
* `RSA.speaker_dirac_eq_iff`: when the listener rules out no state, two speakers are equal
  exactly when they have the same rationality and costs that differ by a constant, or every
  utterance has the same listener and only `α * C` matters.
* `RSA.speaker_dirac_eq_of_mul`: when the listener's mass factors, the speaker at one
  rationality is the speaker at any other with adjusted costs.
* `RSA.speaker_literalListener_dirac_eq_of_cost`: the same for the speaker who reasons about the
  literal listener, where the adjustment is a multiple of the log prior probability that the
  utterance is true.

## Implementation notes

The results concern the speaker who knows the state, `speaker α C L Measure.dirac`. Nothing is
proved here about a speaker with an uncertain belief or about later steps of the recursion.

## References

* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U : Type*} [MeasurableSpace W] [Fintype W] [MeasurableSpace U]
  [MeasurableSingletonClass U] [Fintype U] {α α' : ℝ} {C C' : U → ℝ}

section

variable [MeasurableSingletonClass W]

/-! ### Log odds -/

section LogOdds

variable {L : Kernel U W} [IsFiniteKernel L] {w w' : W} {u u' : U}

/-- The log odds of `u'` against `u` at the state `w` are
`α * (log (L u' {w}) - log (L u {w}) - (C u' - C u))`: the rationality times how much more useful
`u'` is than `u`. -/
theorem log_speaker_dirac_real_singleton_div (hα : 0 ≤ α) (hu : L u {w} ≠ 0)
    (hu' : L u' {w} ≠ 0) :
    Real.log ((speaker α C L Measure.dirac w).real {u'} /
        (speaker α C L Measure.dirac w).real {u}) =
      α * (Real.log (L u' {w}).toReal - Real.log (L u {w}).toReal - (C u' - C u)) := by
  have h := ENNReal.toReal_pos hu (measure_ne_top _ _)
  have h' := ENNReal.toReal_pos hu' (measure_ne_top _ _)
  rw [speaker_dirac_real_singleton_div hα hu,
    Real.log_mul (Real.rpow_pos_of_pos (div_pos h' h) _).ne' (Real.exp_pos _).ne',
    Real.log_rpow (div_pos h' h), Real.log_div h'.ne' h.ne', Real.log_exp]
  ring

/-- Comparing the log odds of `u'` against `u` at two states `w` and `w'` cancels the costs: the
difference is `α` times the same difference for the listener. -/
theorem log_speaker_dirac_real_singleton_div_sub (hα : 0 ≤ α) (hu : L u {w} ≠ 0)
    (hu' : L u' {w} ≠ 0) (hv : L u {w'} ≠ 0) (hv' : L u' {w'} ≠ 0) :
    Real.log ((speaker α C L Measure.dirac w).real {u'} /
          (speaker α C L Measure.dirac w).real {u}) -
        Real.log ((speaker α C L Measure.dirac w').real {u'} /
          (speaker α C L Measure.dirac w').real {u}) =
      α * (Real.log (L u' {w}).toReal - Real.log (L u {w}).toReal -
        (Real.log (L u' {w'}).toReal - Real.log (L u {w'}).toReal)) := by
  rw [log_speaker_dirac_real_singleton_div hα hu hu',
    log_speaker_dirac_real_singleton_div hα hv hv']
  ring

/-- The rationality is identified where the listener discriminates: if `L u' {w} / L u {w}`
differs from `L u' {w'} / L u {w'}`, two speakers who agree at the states `w` and `w'` have the
same `α`, whatever their costs. -/
theorem rationality_eq_of_speaker_dirac_apply_eq (hα : 0 ≤ α) (hα' : 0 ≤ α') (hu : L u {w} ≠ 0)
    (hu' : L u' {w} ≠ 0) (hv : L u {w'} ≠ 0) (hv' : L u' {w'} ≠ 0)
    (hL : L u' {w} * L u {w'} ≠ L u {w} * L u' {w'})
    (h : speaker α C L Measure.dirac w = speaker α' C' L Measure.dirac w)
    (h' : speaker α C L Measure.dirac w' = speaker α' C' L Measure.dirac w') : α = α' := by
  have key := log_speaker_dirac_real_singleton_div_sub (C := C) hα hu hu' hv hv'
  rw [h, h', log_speaker_dirac_real_singleton_div_sub hα' hu hu' hv hv'] at key
  refine (mul_right_cancel₀ (fun h0 ↦ hL ?_) key).symm
  have a := ENNReal.toReal_pos hu (measure_ne_top _ _)
  have a' := ENNReal.toReal_pos hu' (measure_ne_top _ _)
  have b := ENNReal.toReal_pos hv (measure_ne_top _ _)
  have b' := ENNReal.toReal_pos hv' (measure_ne_top _ _)
  have : Real.log ((L u' {w}).toReal * (L u {w'}).toReal) =
      Real.log ((L u {w}).toReal * (L u' {w'}).toReal) := by
    rw [Real.log_mul a'.ne' b.ne', Real.log_mul a.ne' b'.ne']
    linarith
  have := Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos a' b)) (Set.mem_Ioi.2 (mul_pos a b')) this
  rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul] at this
  exact (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (measure_ne_top _ _)
    (measure_ne_top _ _)) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 this

/-- The costs are identified up to a constant: two speakers of the same rationality who agree at
a state have the same cost differences `C u' - C u`. -/
theorem cost_sub_eq_of_speaker_dirac_apply_eq (hα : 0 < α) (hu : L u {w} ≠ 0)
    (hu' : L u' {w} ≠ 0)
    (h : speaker α C L Measure.dirac w = speaker α C' L Measure.dirac w) :
    C u' - C u = C' u' - C' u := by
  have key := log_speaker_dirac_real_singleton_div (C := C) hα.le hu hu'
  rw [h, log_speaker_dirac_real_singleton_div hα.le hu hu'] at key
  linarith [mul_left_cancel₀ hα.ne' key]

omit [IsFiniteKernel L] in
/-- When the listener rules out no state, two speakers are equal in exactly two cases: they
have the same `α` and costs that differ by a constant, or every utterance has the same listener
and `α * C` and `α' * C'` differ by a constant. -/
theorem speaker_dirac_eq_iff [IsMarkovKernel L] [Nonempty W] (hα : 0 < α) (hα' : 0 < α')
    (hL : ∀ u w, L u {w} ≠ 0) :
    speaker α C L Measure.dirac = speaker α' C' L Measure.dirac ↔
      (α = α' ∧ ∃ k, ∀ u, C u = C' u + k) ∨
        ((∀ u u', L u = L u') ∧ ∃ k, ∀ u, α * C u = α' * C' u + k) := by
  constructor
  · intro h
    have hw (w : W) : speaker α C L Measure.dirac w = speaker α' C' L Measure.dirac w := by
      rw [h]
    have key (w : W) (u u' : U) :
        α * (Real.log (L u' {w}).toReal - Real.log (L u {w}).toReal - (C u' - C u)) =
          α' * (Real.log (L u' {w}).toReal - Real.log (L u {w}).toReal - (C' u' - C' u)) := by
      rw [← log_speaker_dirac_real_singleton_div hα.le (hL u w) (hL u' w), hw w,
        log_speaker_dirac_real_singleton_div hα'.le (hL u w) (hL u' w)]
    obtain ⟨w₀⟩ := ‹Nonempty W›
    by_cases hαα : α = α'
    · subst hαα
      refine .inl ⟨rfl, ?_⟩
      rcases isEmpty_or_nonempty U with hU | ⟨⟨u₀⟩⟩
      · exact ⟨0, fun u ↦ isEmptyElim u⟩
      · exact ⟨C u₀ - C' u₀, fun u ↦ by linarith [mul_left_cancel₀ hα.ne' (key w₀ u₀ u)]⟩
    · have hLeq (u u' : U) : L u = L u' := by
        refine Measure.ext_of_singleton fun w ↦ ?_
        have hmul (w' : W) : L u' {w} * L u {w'} = L u {w} * L u' {w'} := by
          by_contra hne
          exact hαα (rationality_eq_of_speaker_dirac_apply_eq hα.le hα'.le (hL u w) (hL u' w)
            (hL u w') (hL u' w') hne (hw w) (hw w'))
        have := Finset.sum_congr (rfl : (Finset.univ : Finset W) = Finset.univ)
          fun w' _ ↦ hmul w'
        simpa [← Finset.mul_sum, sum_measure_singleton] using this.symm
      refine .inr ⟨hLeq, ?_⟩
      rcases isEmpty_or_nonempty U with hU | ⟨⟨u₀⟩⟩
      · exact ⟨0, fun u ↦ isEmptyElim u⟩
      · refine ⟨α * C u₀ - α' * C' u₀, fun u ↦ ?_⟩
        have := key w₀ u₀ u
        simp only [hLeq u u₀, sub_self, zero_sub] at this
        linarith
  · rintro (⟨rfl, k, hk⟩ | ⟨hLeq, k, hk⟩)
    · rw [speaker_dirac_eq_ofWeights, speaker_dirac_eq_ofWeights]
      refine Kernel.ofWeights_eq_of_mul (c := fun _ ↦ ENNReal.ofReal (Real.exp (-(α * k))))
        (fun _ ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') (fun _ ↦ ENNReal.ofReal_ne_top)
        fun w u ↦ ?_
      rw [hk u, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring
    · rcases isEmpty_or_nonempty U with hU | ⟨⟨u₀⟩⟩
      · exact Kernel.ext fun w ↦ Subsingleton.elim _ _
      · rw [speaker_dirac_eq_ofWeights, speaker_dirac_eq_ofWeights]
        refine Kernel.ofWeights_eq_of_mul
          (c := fun w ↦ L u₀ {w} ^ (α - α') * ENNReal.ofReal (Real.exp (-k)))
          (fun w ↦ mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 (hL u₀ w))
            (measure_ne_top _ _)).ne' (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
          (fun w ↦ ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (hL u₀ w)
            (measure_ne_top _ _)) ENNReal.ofReal_ne_top) fun w u ↦ ?_
        rw [hLeq u u₀, mul_mul_mul_comm, ← ENNReal.rpow_add _ _ (hL u₀ w) (measure_ne_top _ _),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3
        · ring
        · linarith [hk u]

end LogOdds

/-! ### Listeners whose mass factors -/

section Mimicry

variable {L : U → Measure W}

/-- The rationality is not identified when the listener's mass factors: if
`L u {w} = a u * h w` wherever it is not zero, the speaker at `α` with costs `C` is the speaker at
any `α'` with the costs `C'` given by `α' * C' u = α * C u + (α' - α) * log (a u)`. -/
theorem speaker_dirac_eq_of_mul {a : U → ℝ≥0∞} {h : W → ℝ≥0∞} (hα : 0 < α) (hα' : 0 < α')
    (ha0 : ∀ u, a u ≠ 0) (ha : ∀ u, a u ≠ ∞) (hh : ∀ w, h w ≠ ∞)
    (hL : ∀ u w, L u {w} = 0 ∨ L u {w} = a u * h w)
    (hC : ∀ u, α' * C' u = α * C u + (α' - α) * Real.log (a u).toReal) :
    speaker α' C' L Measure.dirac = speaker α C L Measure.dirac := by
  rw [speaker_dirac_eq_ofWeights, speaker_dirac_eq_ofWeights]
  refine Kernel.ext fun w ↦ ?_
  have hzero (u : U) (h0 : L u {w} = 0) (c : ℝ≥0∞) :
      L u {w} ^ α' * ENNReal.ofReal (Real.exp (-(α' * C' u))) =
        L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) * c := by
    rw [h0, ENNReal.zero_rpow_of_pos hα', ENNReal.zero_rpow_of_pos hα, zero_mul, zero_mul,
      zero_mul]
  by_cases hw0 : h w = 0
  · exact Kernel.ofWeights_apply_eq_of_mul (c := 1) one_ne_zero ENNReal.one_ne_top fun u ↦
      hzero u ((hL u w).elim id fun hm ↦ by rw [hm, hw0, mul_zero]) 1
  · refine Kernel.ofWeights_apply_eq_of_mul (c := h w ^ (α' - α))
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hw0) (hh w)).ne'
      (ENNReal.rpow_ne_top_of_ne_zero hw0 (hh w)) fun u ↦ ?_
    rcases hL u w with h0 | hm
    · exact hzero u h0 _
    · have hx := ENNReal.toReal_pos (ha0 u) (ha u)
      have hexp : ENNReal.ofReal (Real.exp (-((α' - α) * Real.log (a u).toReal))) =
          a u ^ (-(α' - α)) := by
        conv_rhs => rw [← ENNReal.ofReal_toReal (ha u), ENNReal.ofReal_rpow_of_pos hx,
          Real.rpow_def_of_pos hx]
        congr 2
        ring
      have e1 : a u ^ α' * a u ^ (-(α' - α)) = a u ^ α := by
        rw [← ENNReal.rpow_add _ _ (ha0 u) (ha u)]
        congr 1
        ring
      have e2 : h w ^ α * h w ^ (α' - α) = h w ^ α' := by
        rw [← ENNReal.rpow_add _ _ hw0 (hh w)]
        congr 1
        ring
      rw [hm, hC u, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, hexp,
        ENNReal.mul_rpow_of_ne_top (ha u) (hh w), ENNReal.mul_rpow_of_ne_top (ha u) (hh w),
        ← e1, ← e2]
      ring

end Mimicry

end

/-- The rationality of a speaker who reasons about the literal listener is not identified: the
speaker at `α` with costs `C` is the speaker at any `α'` whose costs satisfy
`α' * C' u = α * C u - (α' - α) * log (μ (sem u))`, a shift by a multiple of the log prior
probability that `u` is true. -/
theorem speaker_literalListener_dirac_eq_of_cost [DiscreteMeasurableSpace W] (hα : 0 < α)
    (hα' : 0 < α') (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    (hμ : ∀ u, μ (sem u) ≠ 0)
    (hC : ∀ u, α' * C' u = α * C u - (α' - α) * Real.log (μ.real (sem u))) :
    speaker α' C' (literalListener μ sem) Measure.dirac =
      speaker α C (literalListener μ sem) Measure.dirac := by
  classical
  refine speaker_dirac_eq_of_mul (a := fun u ↦ (μ (sem u))⁻¹) (h := fun w ↦ μ {w}) hα hα'
    (fun u ↦ ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) (fun u ↦ ENNReal.inv_ne_top.2 (hμ u))
    (fun w ↦ measure_ne_top _ _) (fun u w ↦ ?_) fun u ↦ ?_
  · by_cases hw : w ∈ sem u
    · exact .inr (literalListener_apply_singleton μ sem hw)
    · exact .inl (literalListener_apply_singleton_of_notMem μ sem hw)
  · rw [hC u, ENNReal.toReal_inv, Real.log_inv, measureReal_def]
    ring

end RSA
