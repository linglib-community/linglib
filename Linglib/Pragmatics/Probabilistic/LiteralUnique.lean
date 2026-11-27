module

public import Linglib.Core.Probability.Choice.ChoiceAxiom
public import Linglib.Pragmatics.Probabilistic.Literal

/-!
# Uniqueness of the speaker against the literal listener

The speaker against the literal listener conditions the ratio scale on the utterances true at her
state. This file characterizes her among the rules of the same kind. A rule of weight form weighs
each utterance by a function `f` of the prior probability of its extension and of its cost, and
conditions the weights on the utterances true at the state. If such a rule sends a product prior
with product denotations and added costs to the product of the rules for the two factors,
then `f (x * y) (c + d) * f 1 0 = f x c * f y d`. If moreover `f` strictly decreases in the
probability and decreases in the cost, then `f x c = f 1 0 * x ^ (-a) * exp (-(b * c))` for some
`a > 0` and `b ≥ 0`, and the rule is the speaker at rationality `a` with the costs multiplied by
`b / a`.

## Main definitions

* `RSA.weighted`: the measure that weighs each utterance by a function of the prior probability of
  its extension and of its cost.

## Main results

* `RSA.mul_eq_mul_of_cond_prod`: a rule of weight form that commutes with products has a weight
  function multiplicative in the probability and additive in the cost.
* `RSA.exists_cond_weighted_eq_speaker`: a rule of weight form with such a weight function,
  decreasing in both arguments, is the speaker against the literal listener.

## Implementation notes

That a rule has weight form is a hypothesis. It does not follow from invariance under pulling
the denotations back along a map of states together with commuting with products: a weight may
also depend on the other utterances true at the state. The conditioning of one measure on the
utterances true at each state, which is [luce-1959]'s ratio scale, is what excludes that.

## References

* [luce-1959]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace RSA

variable {W U : Type*} [MeasurableSpace W] [MeasurableSpace U]

/-- The measure that weighs each utterance by `f` of the prior probability of its extension and
of its cost. -/
noncomputable def weighted (f : ℝ → ℝ → ℝ) (μ : Measure W) (sem : U → Set W) (C : U → ℝ) :
    Measure U :=
  Measure.count.withDensity fun u ↦ ENNReal.ofReal (f (μ.real (sem u)) (C u))

/-- A weight function that is multiplicative in the probability and additive in the cost up to
the constant `f 1 0`, strictly decreasing in the probability and decreasing in the cost, is a
negative power of the probability times a decaying exponential of the cost. -/
theorem exists_eq_mul_rpow_neg_mul_exp_neg {f : ℝ → ℝ → ℝ} (h₁ : 0 < f 1 0)
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ c d,
      f (x * y) (c + d) * f 1 0 = f x c * f y d)
    (hx : StrictAntiOn (fun x ↦ f x 0) (Ioc 0 1)) (hc : Antitone (f 1)) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, ∀ c, f x c = f 1 0 * x ^ (-a) * exp (-(b * c)) := by
  have hI : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := right_mem_Ioc.2 one_pos
  obtain ⟨a, ha, hg⟩ := Real.exists_eq_rpow_neg_of_strictAntiOn (g := fun x ↦ f x 0 / f 1 0)
    (fun x hx y hy ↦ by
      rw [div_mul_div_comm, ← hmul x hx y hy, add_zero, mul_div_mul_right _ _ h₁.ne'])
    (fun _ hs _ ht hst ↦ div_lt_div_of_pos_right (hx hs ht hst) h₁)
  obtain ⟨b, hb, hh⟩ := Real.exists_eq_exp_neg_mul_of_antitone (h := fun c ↦ f 1 c / f 1 0)
    (div_pos h₁ h₁).ne'
    (fun c d ↦ by rw [div_mul_div_comm, ← hmul 1 hI 1 hI, mul_one, mul_div_mul_right _ _ h₁.ne'])
    (fun _ _ hcd ↦ div_le_div_of_nonneg_right (hc hcd) h₁.le)
  refine ⟨a, b, ha, hb, fun x hx c ↦ mul_right_cancel₀ h₁.ne' ?_⟩
  have e := hmul x hx 1 hI 0 c
  rw [mul_one, zero_add] at e
  rw [e, ← div_mul_cancel₀ (f x 0) h₁.ne', ← div_mul_cancel₀ (f 1 c) h₁.ne', hg x hx, hh c]
  ring

section Evaluation

variable [MeasurableSingletonClass U] {f : ℝ → ℝ → ℝ} {μ : Measure W} {sem : U → Set W}
  {C : U → ℝ}

private theorem weighted_real_singleton {u : U} (hu : 0 ≤ f (μ.real (sem u)) (C u)) :
    (weighted f μ sem C).real {u} = f (μ.real (sem u)) (C u) := by
  rw [measureReal_def]
  simp [weighted, withDensity_apply _ (measurableSet_singleton u), hu]

private theorem weighted_real_univ_pos [Finite U] [Nonempty U]
    (hf : ∀ u, 0 < f (μ.real (sem u)) (C u)) : 0 < (weighted f μ sem C).real univ := by
  have : IsFiniteMeasure (weighted f μ sem C) :=
    isFiniteMeasure_withDensity_ofReal Integrable.of_finite.hasFiniteIntegral
  obtain ⟨u⟩ := ‹Nonempty U›
  exact (hf u).trans_le ((weighted_real_singleton (hf u).le).symm.trans_le
    (measureReal_mono (subset_univ _)))

private theorem weighted_cond_univ_real_singleton (hf : ∀ u, 0 < f (μ.real (sem u)) (C u))
    (u : U) :
    ((weighted f μ sem C)[|univ]).real {u} =
      f (μ.real (sem u)) (C u) / (weighted f μ sem C).real univ := by
  rw [cond_real_apply _ MeasurableSet.univ, univ_inter, weighted_real_singleton (hf u).le]

end Evaluation

private theorem exists_measure_bool {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃ μ : Measure Bool, IsProbabilityMeasure μ ∧ μ.real {true} = x := by
  refine ⟨ENNReal.ofReal x • Measure.dirac true + ENNReal.ofReal (1 - x) • Measure.dirac false,
    ⟨?_⟩, ?_⟩
  · simp [← ENNReal.ofReal_add hx.1.le (sub_nonneg.2 hx.2)]
  · simp [measureReal_def, hx.1.le]

/-- A rule of weight form that sends every product prior on two pairs of states, with product
denotations of two pairs of utterances and added costs, to the product of the rules for the
factors has a weight function multiplicative in the probability and additive in the cost, up to
the constant `f 1 0`. -/
theorem mul_eq_mul_of_cond_prod {f : ℝ → ℝ → ℝ} (hpos : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ c, 0 < f x c)
    (h : ∀ (μ₁ μ₂ : Measure Bool) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      (sem₁ sem₂ : Bool → Set Bool) (C₁ C₂ : Bool → ℝ) (w₁ w₂ : Bool),
      μ₁ {w₁} ≠ 0 → μ₂ {w₂} ≠ 0 →
      (weighted f (μ₁.prod μ₂) (fun u : Bool × Bool ↦ sem₁ u.1 ×ˢ sem₂ u.2)
          fun u ↦ C₁ u.1 + C₂ u.2)[|{u | (w₁, w₂) ∈ sem₁ u.1 ×ˢ sem₂ u.2}] =
        ((weighted f μ₁ sem₁ C₁)[|{u | w₁ ∈ sem₁ u}]).prod
          ((weighted f μ₂ sem₂ C₂)[|{u | w₂ ∈ sem₂ u}])) :
    ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ c d,
      f (x * y) (c + d) * f 1 0 = f x c * f y d := by
  intro x hx y hy c d
  obtain ⟨μ₁, _, hμ₁⟩ := exists_measure_bool hx
  obtain ⟨μ₂, _, hμ₂⟩ := exists_measure_bool hy
  obtain ⟨sem, hst, hsf⟩ : ∃ sem : Bool → Set Bool, sem true = {true} ∧ sem false = univ :=
    ⟨fun u ↦ bif u then {true} else univ, rfl, rfl⟩
  have hsem {μ : Measure Bool} [IsProbabilityMeasure μ] {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1)
      (h : μ.real {true} = z) (u : Bool) : μ.real (sem u) ∈ Ioc (0 : ℝ) 1 := by
    cases u
    · rw [hsf, probReal_univ]
      exact ⟨one_pos, le_rfl⟩
    · rwa [hst, h]
  have hne {μ : Measure Bool} {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) (h : μ.real {true} = z) :
      μ {true} ≠ 0 := fun h0 ↦ hz.1.ne' (by rw [← h, measureReal_def, h0, ENNReal.toReal_zero])
  have hS : {u : Bool | true ∈ sem u} = univ :=
    eq_univ_of_forall fun u ↦ by cases u <;> simp [hst, hsf]
  have hS₂ : {u : Bool × Bool | (true, true) ∈ sem u.1 ×ˢ sem u.2} = univ :=
    eq_univ_of_forall fun ⟨u₁, u₂⟩ ↦ by cases u₁ <;> cases u₂ <;> simp [hst, hsf]
  have key := h μ₁ μ₂ sem sem (fun u ↦ bif u then c else 0) (fun u ↦ bif u then d else 0) true true
    (hne hx hμ₁) (hne hy hμ₂)
  rw [hS, hS₂] at key
  have h₁ (u : Bool) := hpos _ (hsem hx hμ₁ u) (bif u then c else 0)
  have h₂ (u : Bool) := hpos _ (hsem hy hμ₂ u) (bif u then d else 0)
  have h₁₂ (u : Bool × Bool) := hpos ((μ₁.prod μ₂).real (sem u.1 ×ˢ sem u.2)) (by
      obtain ⟨hp₁, hq₁⟩ := hsem hx hμ₁ u.1
      obtain ⟨hp₂, hq₂⟩ := hsem hy hμ₂ u.2
      rw [measureReal_prod_prod]
      exact ⟨mul_pos hp₁ hp₂, (mul_le_of_le_one_left hp₂.le hq₁).trans hq₂⟩)
    ((bif u.1 then c else 0) + bif u.2 then d else 0)
  have t₁ := congrArg (·.real ({true} ×ˢ {true})) key
  have t₂ := congrArg (·.real ({false} ×ˢ {false})) key
  simp only [measureReal_prod_prod] at t₁ t₂
  rw [singleton_prod_singleton, weighted_cond_univ_real_singleton h₁₂,
    weighted_cond_univ_real_singleton h₁, weighted_cond_univ_real_singleton h₂] at t₁ t₂
  simp only [hst, hsf, Bool.cond_true, Bool.cond_false, measureReal_prod_prod, hμ₁, hμ₂,
    probReal_univ, mul_one, add_zero] at t₁ t₂
  have alg {F P Q B Z Z₁ Z₂ : ℝ} (hB : 0 < B) (hZ : 0 < Z) (hZ₁ : 0 < Z₁) (hZ₂ : 0 < Z₂)
      (t₁ : F / Z = P / Z₁ * (Q / Z₂)) (t₂ : B / Z = B / Z₁ * (B / Z₂)) : F * B = P * Q := by
    rw [div_mul_div_comm, div_eq_div_iff hZ.ne' (mul_pos hZ₁ hZ₂).ne'] at t₁ t₂
    have t₂' : Z₁ * Z₂ = B * Z := mul_left_cancel₀ hB.ne' (t₂.trans (mul_assoc _ _ _))
    refine mul_right_cancel₀ hZ.ne' ?_
    linear_combination t₁ - F * t₂'
  exact alg (hpos 1 ⟨one_pos, le_rfl⟩ 0) (weighted_real_univ_pos h₁₂) (weighted_real_univ_pos h₁)
    (weighted_real_univ_pos h₂) t₁ t₂

private theorem cond_withDensity_congr {ν : Measure U} {g g' : U → ℝ≥0∞} {s : Set U}
    (hs : MeasurableSet s) (h : ∀ u ∈ s, g u = g' u) :
    (ν.withDensity g)[|s] = (ν.withDensity g')[|s] :=
  cond_eq_of_restrict_eq <| by
    rw [restrict_withDensity hs, restrict_withDensity hs]
    exact withDensity_congr_ae (ae_restrict_of_forall_mem hs h)

private theorem measureReal_pos_of_mem {μ : Measure W} [IsFiniteMeasure μ] {s : Set W} {w : W}
    (hw : μ {w} ≠ 0) (h : w ∈ s) : 0 < μ.real s :=
  ENNReal.toReal_pos (fun h0 ↦ hw (measure_mono_null (singleton_subset_iff.2 h) h0))
    (measure_ne_top _ _)

variable [MeasurableSingletonClass W] [Fintype W] [MeasurableSingletonClass U] [Fintype U]

/-- The speaker who knows the state is the rule of weight form whose weight is a negative power
of the probability times a decaying exponential of the cost. -/
theorem speaker_literalListener_dirac_eq_cond_weighted {K a b : ℝ} (hK : 0 < K) (ha : 0 < a)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) {w : W}
    (hw : μ {w} ≠ 0) :
    speaker a (fun u ↦ b / a * C u) (literalListener μ sem) Measure.dirac w =
      (weighted (fun x c ↦ K * x ^ (-a) * exp (-(b * c))) μ sem C)[|{u | w ∈ sem u}] := by
  rw [speaker_literalListener_dirac_eq_cond ha _ μ sem hw,
    ← cond_smul (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top, ratioScale,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine cond_withDensity_congr .of_discrete fun u hu ↦ ?_
  have hr := measureReal_pos_of_mem hw hu
  rw [Pi.smul_apply, smul_eq_mul, ← ofReal_measureReal (measure_ne_top μ (sem u)),
    ← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_rpow_of_pos (inv_pos.2 hr),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK.le, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le, ← mul_assoc a, mul_div_cancel₀ b ha.ne', ← mul_assoc]

/-- A rule of weight form whose weight function is multiplicative in the probability and additive
in the cost, strictly decreasing in the probability and decreasing in the cost, is the speaker
against the literal listener at some positive rationality, with the costs rescaled. -/
theorem exists_cond_weighted_eq_speaker {f : ℝ → ℝ → ℝ} (h₁ : 0 < f 1 0)
    (hmul : ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ c d,
      f (x * y) (c + d) * f 1 0 = f x c * f y d)
    (hx : StrictAntiOn (fun x ↦ f x 0) (Ioc 0 1)) (hc : Antitone (f 1)) :
    ∃ a k : ℝ, 0 < a ∧ 0 ≤ k ∧ ∀ (μ : Measure W) [IsProbabilityMeasure μ] (sem : U → Set W)
      (C : U → ℝ) (w : W), μ {w} ≠ 0 →
        (weighted f μ sem C)[|{u | w ∈ sem u}] =
          speaker a (fun u ↦ k * C u) (literalListener μ sem) Measure.dirac w := by
  obtain ⟨a, b, ha, hb, hf⟩ := exists_eq_mul_rpow_neg_mul_exp_neg h₁ hmul hx hc
  refine ⟨a, b / a, ha, div_nonneg hb ha.le, fun μ _ sem C w hw ↦ ?_⟩
  rw [speaker_literalListener_dirac_eq_cond_weighted h₁ ha C μ sem hw]
  refine cond_withDensity_congr .of_discrete fun u hu ↦ ?_
  rw [hf _ ⟨measureReal_pos_of_mem hw hu, measureReal_le_one⟩]

end RSA
