module

public import Linglib.Core.Probability.Kernel.OfDensity

/-!
# The replicator dynamic

A population is a finite measure `x` on types, and the fitness of a type `i` is its expected payoff
against a member of the population, `∫ j, U i j ∂x` for a payoff `U`. The replicator step
reweights the population by fitness and normalizes. It is Bayes' rule with fitness as likelihood,
the row of `Kernel.ofDensity x` at the density `f` (`SignalingGame.replicator_eq_ofDensity`), and
is evaluated through that API. The replicator–mutator step passes the result through a kernel `Q`
that sends a type to the type its offspring or learners take. Without mutation it is the replicator
step, and under equal fitness it is one step of the chain `Q`.

## References

* [huttegger-skyrms-tarres-wagner-2014]
* [brochhagen-franke-van-rooij-2018]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SignalingGame

variable {T : Type*} [MeasurableSpace T]

/-- The fitness of type `i` in the population `x`, its expected payoff `U i j` against a member
`j` of the population. -/
noncomputable def fitness (U : T → T → ℝ) (x : Measure T) (i : T) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ j, U i j ∂x)

/-- The replicator step, which reweights the population `x` by the fitness `f` and normalizes. -/
noncomputable def replicator (f : T → ℝ≥0∞) (x : Measure T) : Measure T :=
  (x.withDensity f)[|Set.univ]

/-- The replicator–mutator step: the replicator step followed by the mutation kernel `Q`. -/
noncomputable def replicatorMutator (Q : Kernel T T) (f : T → ℝ≥0∞) (x : Measure T) : Measure T :=
  Q ∘ₘ replicator f x

instance (f : T → ℝ≥0∞) (x : Measure T) : IsFiniteMeasure (replicator f x) :=
  inferInstanceAs (IsFiniteMeasure ((x.withDensity f)[|Set.univ]))

/-- Without mutation the replicator–mutator step is the replicator step. -/
theorem replicatorMutator_id (f : T → ℝ≥0∞) (x : Measure T) :
    replicatorMutator Kernel.id f x = replicator f x :=
  Measure.id_comp

/-- Under equal fitness the replicator–mutator step is one step of the mutation chain. -/
theorem replicatorMutator_const (Q : Kernel T T) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (x : Measure T) [IsProbabilityMeasure x] : replicatorMutator Q (fun _ ↦ c) x = Q ∘ₘ x := by
  rw [replicatorMutator, replicator, withDensity_const, cond_smul hc hc', cond_univ]

/-- The replicator step is Bayes' rule with fitness as likelihood. -/
theorem replicator_eq_ofDensity (f : T → ℝ≥0∞) (x : Measure T) :
    replicator f x = Kernel.ofDensity x (fun (_ : Unit) ↦ f) () := by
  rw [replicator, Kernel.ofDensity_apply]

variable [Countable T] [MeasurableSingletonClass T]

theorem replicator_real_singleton [Fintype T] (f : T → ℝ≥0∞) (hf : ∀ i, f i ≠ ⊤) (x : Measure T)
    [IsFiniteMeasure x] (i : T) :
    (replicator f x).real {i} = (f i).toReal * x.real {i} / ∑ k, (f k).toReal * x.real {k} := by
  rw [replicator_eq_ofDensity]
  exact Kernel.ofDensity_real_singleton x _ () hf i

end SignalingGame
