module

public import Linglib.Pragmatics.RSA.Basic

/-!
# Lexical uncertainty

In the lexical-uncertainty model of [bergen-levy-goodman-2016], speaker and listener share a
prior over lexica. The speaker uses one lexicon and addresses its literal listener, and the
pragmatic listener, unsure which, inverts the speaker of each lexicon. With the lexicon a
coordinate of the state, she is `RSA.listener` at the product of the prior over states and the
prior over lexica. The paper states her belief about the state as the listener of the speaker
averaged over lexica, and [the two presentations agree](##listener_prod_fst). A state is possible
after an utterance exactly when it has positive prior and some lexicon of positive prior has its
speaker produce the utterance there
([the union of the lexica's supports](##listener_prod_fst_apply_singleton_ne_zero_iff)).

Nothing requires the latent to be a lexicon: a threshold, a comparison class or a scope reading
that the speaker knows and the listener does not enters the same way.

## Main statements

* `RSA.listener_prod_fst`
* `RSA.listener_prod_fst_apply_singleton_ne_zero_iff`

## References

* [bergen-levy-goodman-2016]
* [franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RSA

variable {A B U : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace U]
  [Fintype A] [Fintype B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [Countable U] [MeasurableSingletonClass U]

/-- **Lexical uncertainty.** Against a product prior, the first marginal of the listener is the
listener of the speaker averaged over the second coordinate by its prior. -/
theorem listener_prod_fst (μ : Measure A) (ν : Measure B) (S : A × B → Measure U) :
    (listener (μ.prod ν) S).fst = listener μ fun a ↦ ∑ b, ν {b} • S (a, b) := by
  ext u : 1
  refine Measure.ext_of_singleton fun a ↦ ?_
  change (listener (μ.prod ν) S u).fst {a} = _
  simp_rw [Measure.fst_apply_singleton, listener_apply_singleton, div_eq_mul_inv, ← Finset.sum_mul,
    Fintype.sum_prod_type, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  congr 1
  · ring
  · exact congrArg _ <| Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

variable (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure B) [IsFiniteMeasure ν]
  (S : A × B → Measure U) [∀ p, IsFiniteMeasure (S p)] (u : U) (a : A)

theorem listener_prod_fst_real_singleton :
    (listener (μ.prod ν) S u).fst.real {a} =
      μ.real {a} * (∑ b, ν.real {b} * (S (a, b)).real {u}) /
        ∑ p, (μ.prod ν).real {p} * (S p).real {u} := by
  rw [listener_fst_real_singleton]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [Measure.prod_real_singleton, mul_assoc]

/-- Against a product prior, a state is possible after an utterance exactly when it has positive
prior and the speaker produces the utterance there at some value of positive prior of the second
coordinate. -/
theorem listener_prod_fst_apply_singleton_ne_zero_iff :
    (listener (μ.prod ν) S u).fst {a} ≠ 0 ↔ μ {a} ≠ 0 ∧ ∃ b, ν {b} ≠ 0 ∧ S (a, b) {u} ≠ 0 := by
  simp_rw [listener_fst_apply_singleton_ne_zero_iff, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff]
  exact ⟨fun ⟨b, ⟨ha, hb⟩, h⟩ ↦ ⟨ha, b, hb, h⟩, fun ⟨ha, b, hb, h⟩ ↦ ⟨b, ⟨ha, hb⟩, h⟩⟩

end RSA
