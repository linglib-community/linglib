module

public import Linglib.Core.InformationTheory.Entropy.Measure
public import Linglib.Core.InformationTheory.KullbackLeibler.Tilted
public import Linglib.Core.MeasureTheory.Measure.Tilted
public import Linglib.Core.Probability.Kernel.Softmax

/-!
# Entropy and normalized weights on a finite type

On a finite type, the divergence of a probability measure `q` from a family of weights normalized to
a probability measure, and the entropy of `q`, [add
up](##InformationTheory.toReal_klDiv_ofWeights_add_measureEntropy) to the logarithm of the total
weight less the expected log-weight under `q`; a row of the softmax kernel [is the
case](##InformationTheory.toReal_klDiv_softmax_add_measureEntropy) of weights `exp ∘ score`. For the
weights `exp ∘ f` the normalized measure is the counting measure tilted by `f`, and the identity
[reads](##InformationTheory.toReal_klDiv_count_tilted_add_measureEntropy) `KL(q ‖ count.tilted f) +
H(q) = log ∑ exp f - ∫ f ∂q`. So the expected value of `f` plus the entropy [is at
most](##InformationTheory.integral_add_measureEntropy_le_log_sum_exp) `log ∑ exp f`, with equality
[exactly at](##InformationTheory.integral_add_measureEntropy_eq_log_sum_exp_iff) the tilted measure:
this is the Gibbs variational principle with the counting measure as reference, where
`InformationTheory.integral_sub_toReal_klDiv_le_log_integral_exp` has a probability measure.

The maximum entropy principle is the case of equal expectations. A distribution `q` under which
`f` has the expected value it has under the tilted measure [falls
short](##InformationTheory.measureEntropy_add_toReal_klDiv_count_tilted) of the tilted measure's
entropy by its divergence from it, so the tilted measure [has the greatest
entropy](##InformationTheory.isGreatest_measureEntropy_count_tilted) among such distributions, and
[no other](##InformationTheory.measureEntropy_eq_measureEntropy_count_tilted_iff) has as much.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  {q : Measure S} [IsProbabilityMeasure q]

/-- The divergence from normalized weights and the entropy add up to the log of the total weight
less the expected log-weight. -/
theorem toReal_klDiv_ofWeights_add_measureEntropy {ι : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] {w : ι → S → ℝ≥0∞} {i : ι} (hw : ∀ s, w i s ≠ ∞)
    (hq : q ≪ Kernel.ofWeights w i) :
    (klDiv q (Kernel.ofWeights w i)).toReal + Hm[q] =
      log (∑ s, (w i s).toReal) - ∑ s, q.real {s} * log (w i s).toReal := by
  have := Kernel.isProbabilityMeasure_ofWeights_of_absolutelyContinuous hw hq
  have hterm (s : S) : q.real {s} * log ((Kernel.ofWeights w i).real {s}) =
      q.real {s} * log (w i s).toReal - q.real {s} * log (∑ s, (w i s).toReal) := by
    rcases eq_or_ne (q.real {s}) 0 with h | h
    · simp [h]
    · have hp : (Kernel.ofWeights w i).real {s} ≠ 0 := fun h0 ↦
        h ((measureReal_eq_zero_iff (measure_ne_top _ _)).2
          (hq ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0)))
      rw [Kernel.ofWeights_real_singleton w i hw] at hp ⊢
      rw [log_div (fun h0 ↦ hp (by rw [h0, zero_div])) fun h0 ↦ hp (by rw [h0, div_zero]), mul_sub]
  rw [toReal_klDiv_add_measureEntropy hq, Finset.sum_congr rfl fun s _ ↦ hterm s,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ,
    probReal_univ, one_mul, neg_sub]

section Softmax

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {score : α → S → EReal} {a : α}

/-- The divergence from a row of the softmax kernel and the entropy add up to the log of the
row's normalizer less the expected score. -/
theorem toReal_klDiv_softmax_add_measureEntropy (htop : ∀ s, score a s ≠ ⊤)
    (hq : q ≪ Kernel.softmax score a) :
    (klDiv q (Kernel.softmax score a)).toReal + Hm[q] =
      log (∑ s, (EReal.exp (score a s)).toReal) - ∫ s, (score a s).toReal ∂q := by
  rw [integral_fintype .of_finite]
  simpa only [Kernel.softmax, EReal.log_toReal_exp, smul_eq_mul] using
    toReal_klDiv_ofWeights_add_measureEntropy (w := fun a s ↦ EReal.exp (score a s))
      (fun s ↦ mt EReal.exp_eq_top_iff.1 (htop s)) hq

/-- A row of the softmax kernel is the Gibbs optimizer: no distribution on the points it gives
mass to has a greater expected score plus entropy than the log of its normalizer, which the row
itself attains. -/
theorem integral_toReal_add_measureEntropy_le_log_sum_exp (htop : ∀ s, score a s ≠ ⊤)
    (hq : q ≪ Kernel.softmax score a) :
    ∫ s, (score a s).toReal ∂q + Hm[q] ≤ log (∑ s, (EReal.exp (score a s)).toReal) := by
  linarith [toReal_klDiv_softmax_add_measureEntropy htop hq,
    ENNReal.toReal_nonneg (a := klDiv q (Kernel.softmax score a))]

end Softmax

variable (q) (f : S → ℝ)

/-- The expected value of `f` plus the entropy, as a sum over the atoms. -/
theorem integral_add_measureEntropy_eq_sum :
    ∫ s, f s ∂q + Hm[q] = ∑ s, q.real {s} * (f s - log (q.real {s})) := by
  rw [integral_fintype .of_finite, measureEntropy_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ ↦ by simp only [smul_eq_mul, negMulLog]; ring

/-- The divergence from a tilt of the counting measure and the entropy add up to
`log ∑ exp f - ∫ f ∂q`. -/
theorem toReal_klDiv_count_tilted_add_measureEntropy :
    (klDiv q (Measure.count.tilted f)).toReal + Hm[q] =
      log (∑ s, exp (f s)) - ∫ s, f s ∂q := by
  have := nonempty_of_isProbabilityMeasure q
  have : IsProbabilityMeasure (Measure.count.tilted f) := isProbabilityMeasure_tilted .of_finite
  rw [toReal_klDiv_add_measureEntropy (absolutelyContinuous_count_tilted q f),
    integral_fintype .of_finite]
  simp only [count_tilted_real_singleton, log_softmax, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ,
    probReal_univ, one_mul, neg_sub]

omit [IsProbabilityMeasure q] in
/-- The entropy of a tilt of the counting measure is `log ∑ exp f` less the expected value of
`f`. -/
theorem measureEntropy_count_tilted [Nonempty S] :
    Hm[Measure.count.tilted f] = log (∑ s, exp (f s)) - ∫ s, f s ∂(Measure.count.tilted f) := by
  have : IsProbabilityMeasure (Measure.count.tilted f) := isProbabilityMeasure_tilted .of_finite
  simpa using toReal_klDiv_count_tilted_add_measureEntropy (Measure.count.tilted f) f

/-- **Gibbs variational principle** on a finite type: the expected value of `f` plus the entropy
is at most `log ∑ exp f`. -/
theorem integral_add_measureEntropy_le_log_sum_exp :
    ∫ s, f s ∂q + Hm[q] ≤ log (∑ s, exp (f s)) := by
  linarith [toReal_klDiv_count_tilted_add_measureEntropy q f,
    ENNReal.toReal_nonneg (a := klDiv q (Measure.count.tilted f))]

/-- The expected value of `f` plus the entropy is `log ∑ exp f` exactly at the counting measure
tilted by `f`. -/
theorem integral_add_measureEntropy_eq_log_sum_exp_iff :
    ∫ s, f s ∂q + Hm[q] = log (∑ s, exp (f s)) ↔ q = Measure.count.tilted f := by
  have := nonempty_of_isProbabilityMeasure q
  have : IsProbabilityMeasure (Measure.count.tilted f) := isProbabilityMeasure_tilted .of_finite
  have hne := klDiv_ne_top (absolutelyContinuous_count_tilted q f) .of_finite
  rw [← klDiv_eq_zero_iff, ← (ENNReal.toReal_eq_zero_iff _).trans (or_iff_left hne)]
  constructor <;> intro h <;> linarith [toReal_klDiv_count_tilted_add_measureEntropy q f]

/-! ### The maximum entropy principle -/

variable {q f}

/-- A distribution under which `f` has the expected value it has under the tilted measure falls
short of the tilted measure's entropy by its divergence from it. -/
theorem measureEntropy_add_toReal_klDiv_count_tilted
    (h : ∫ s, f s ∂q = ∫ s, f s ∂Measure.count.tilted f) :
    Hm[q] + (klDiv q (Measure.count.tilted f)).toReal = Hm[Measure.count.tilted f] := by
  have := nonempty_of_isProbabilityMeasure q
  have : IsProbabilityMeasure (uniformOn (Set.univ : Set S)) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have : IsProbabilityMeasure (Measure.count.tilted f) := isProbabilityMeasure_tilted .of_finite
  have hadd := klDiv_eq_klDiv_tilted_add (μ := uniformOn Set.univ) (q := q) (f := f) .of_finite
    .of_finite .of_finite (by rwa [uniformOn_univ_tilted])
  rw [uniformOn_univ_tilted] at hadd
  have hne := klDiv_ne_top (absolutelyContinuous_count_tilted q f) .of_finite
  have hne' := klDiv_ne_top (absolutelyContinuous_uniformOn_univ (Measure.count.tilted f))
    .of_finite
  have hadd' := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hne hne'] at hadd'
  linarith [toReal_klDiv_uniformOn_add_measureEntropy q,
    toReal_klDiv_uniformOn_add_measureEntropy (Measure.count.tilted f)]

theorem measureEntropy_le_measureEntropy_count_tilted
    (h : ∫ s, f s ∂q = ∫ s, f s ∂Measure.count.tilted f) :
    Hm[q] ≤ Hm[Measure.count.tilted f] := by
  linarith [measureEntropy_add_toReal_klDiv_count_tilted h,
    ENNReal.toReal_nonneg (a := klDiv q (Measure.count.tilted f))]

/-- The tilted measure is the only distribution with its expected value of `f` and its
entropy. -/
theorem measureEntropy_eq_measureEntropy_count_tilted_iff
    (h : ∫ s, f s ∂q = ∫ s, f s ∂Measure.count.tilted f) :
    Hm[q] = Hm[Measure.count.tilted f] ↔ q = Measure.count.tilted f := by
  have := nonempty_of_isProbabilityMeasure q
  rw [← integral_add_measureEntropy_eq_log_sum_exp_iff]
  constructor <;> intro h' <;> linarith [measureEntropy_count_tilted f]

variable (f) in
/-- **Maximum entropy principle**: the counting measure tilted by `f` has the greatest entropy
among the distributions under which `f` has the same expected value. -/
theorem isGreatest_measureEntropy_count_tilted [Nonempty S] :
    IsGreatest (measureEntropy '' {q : Measure S | IsProbabilityMeasure q ∧
      ∫ s, f s ∂q = ∫ s, f s ∂Measure.count.tilted f}) (Hm[Measure.count.tilted f]) :=
  ⟨⟨_, ⟨isProbabilityMeasure_tilted .of_finite, rfl⟩, rfl⟩, by
    rintro _ ⟨q, ⟨hq, h⟩, rfl⟩
    exact measureEntropy_le_measureEntropy_count_tilted h⟩

end InformationTheory
