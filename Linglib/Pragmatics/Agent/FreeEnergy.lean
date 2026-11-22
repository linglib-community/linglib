module

public import Linglib.Core.InformationTheory.Entropy.Tilted
public import Linglib.Pragmatics.Agent.Basic

/-!
# The policy as a maximizer

At an observation, a distribution `q` over the actions of an agent has an entropy and an expected
value, and at rationality `β` their sum `Hm[q] + β * ∫ x, a.value o x ∂q` is what the agent's
policy maximizes among the distributions over its feasible actions. A distribution `q` falls
short of the policy by its divergence from it
(`Agent.measureEntropy_add_integral_value`), so the policy does at least as well as any
(`Agent.measureEntropy_add_integral_value_le`) and is the only distribution to do as well as
itself (`Agent.measureEntropy_add_integral_value_eq_iff`).

## TODO

* Rationality zero, where the policy is uniform over all the actions.
* The same for a reference measure over the actions other than the counting measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Agent

variable {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] {a : Agent O S A}
  [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] {β : ℝ} {o : O} {q : Measure A} [IsProbabilityMeasure q]

omit [Countable O] [MeasurableSingletonClass O] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
open Classical in
private theorem exp_score_ne_top (a : Agent O S A) (hβ : 0 < β) (o : O) (x : A) :
    EReal.exp (β * if a.Feasible o x then (a.value o x : EReal) else ⊥) ≠ ∞ := by
  rw [Ne, EReal.exp_eq_top_iff]
  split_ifs
  · rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  · rw [EReal.coe_mul_bot_of_pos hβ]; exact bot_ne_top

open Classical in
private theorem klDiv_policy_add (hβ : 0 < β) (hq : q ≪ a.policy β o) :
    (klDiv q (a.policy β o)).toReal + Hm[q] + β * ∫ x, a.value o x ∂q =
      Real.log (∑ x, (EReal.exp
        (β * if a.Feasible o x then (a.value o x : EReal) else ⊥)).toReal) := by
  have hw := exp_score_ne_top a hβ o
  have key := toReal_klDiv_ofWeights_add_measureEntropy (q := q) (i := o)
    (w := fun o x ↦ EReal.exp (β * if a.Feasible o x then (a.value o x : EReal) else ⊥)) hw hq
  have hterm : ∑ x, q.real {x} * Real.log (EReal.exp
      (β * if a.Feasible o x then (a.value o x : EReal) else ⊥)).toReal =
      β * ∫ x, a.value o x ∂q := by
    rw [integral_fintype .of_finite, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rcases eq_or_ne (q {x}) 0 with h | h
    · simp [measureReal_def, h]
    · have hx : a.Feasible o x :=
        (a.policy_apply_singleton_ne_zero_iff hβ o x).1 fun h0 ↦ h (hq h0)
      simp only [hx, ↓reduceIte]
      rw [← EReal.coe_mul, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le,
        Real.log_exp, smul_eq_mul]
      ring
  have key' : (klDiv q (a.policy β o)).toReal + Hm[q] = _ := key
  rw [key', hterm]
  ring

/-- A distribution over the feasible actions falls short of the policy, in entropy plus `β` times
expected value, by its divergence from the policy. -/
theorem measureEntropy_add_integral_value (hβ : 0 < β) (hq : q ≪ a.policy β o) :
    Hm[q] + β * ∫ x, a.value o x ∂q =
      Hm[a.policy β o] + β * ∫ x, a.value o x ∂(a.policy β o) -
        (klDiv q (a.policy β o)).toReal := by
  classical
  have : IsProbabilityMeasure (a.policy β o) :=
    Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous (exp_score_ne_top a hβ o) hq
  have h1 := klDiv_policy_add hβ hq
  have h2 := klDiv_policy_add (q := a.policy β o) hβ Measure.AbsolutelyContinuous.rfl
  rw [klDiv_self, ENNReal.toReal_zero, zero_add] at h2
  linarith

/-- Among the distributions over its feasible actions, the policy has the greatest entropy plus
`β` times expected value. -/
theorem measureEntropy_add_integral_value_le (hβ : 0 < β) (hq : q ≪ a.policy β o) :
    Hm[q] + β * ∫ x, a.value o x ∂q ≤
      Hm[a.policy β o] + β * ∫ x, a.value o x ∂(a.policy β o) := by
  rw [measureEntropy_add_integral_value hβ hq]
  exact sub_le_self _ ENNReal.toReal_nonneg

/-- The policy is the only distribution over its feasible actions with its entropy plus `β` times
expected value. -/
theorem measureEntropy_add_integral_value_eq_iff (hβ : 0 < β) (hq : q ≪ a.policy β o) :
    Hm[q] + β * ∫ x, a.value o x ∂q =
        Hm[a.policy β o] + β * ∫ x, a.value o x ∂(a.policy β o) ↔ q = a.policy β o := by
  rw [measureEntropy_add_integral_value hβ hq, sub_eq_self,
    ENNReal.toReal_eq_zero_iff, or_iff_left (klDiv_ne_top hq .of_finite), klDiv_eq_zero_iff]

end Agent
