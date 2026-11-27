/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Distributions.Dirichlet
public import Linglib.Core.Probability.Exchangeable.Mixture

/-!
# The infinite Pólya urn

The whole sequence of draws of a Pólya urn with positive weights `θ` is exchangeable. Its law is
the mixture, under the Dirichlet distribution with parameters `θ`, of the laws of independent and
identically distributed sequences, and its directing random measure has that Dirichlet law.

## Main definitions

* `Convexity.StdSimplex.toProbabilityMeasure t`: a probability vector on a finite type, as a
  probability measure.
* `ProbabilityTheory.polyaUrnProcess hθ`: the law of the whole sequence of draws.

## Main results

* `ProbabilityTheory.polyaUrnProcess_map_restrict`: the first `n` draws have the law
  `polyaUrn θ n`.
* `ProbabilityTheory.polyaUrnProcess_eq_iid_comp`: the sequence is a Dirichlet mixture of
  independent and identically distributed sequences.
* `ProbabilityTheory.exchangeable_polyaUrnProcess`: the draws are exchangeable.
* `ProbabilityTheory.map_directingMeasure_polyaUrnProcess`: the directing random measure has the
  Dirichlet law.

## References

* [pitman-2006]
* [kallenberg-2005]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Convexity

namespace ProbabilityTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A probability vector on a finite type, as a probability measure. -/
noncomputable def _root_.Convexity.StdSimplex.toProbabilityMeasure (t : StdSimplex ℝ α) :
    ProbabilityMeasure α :=
  ⟨∑ a, ENNReal.ofReal (t.weights a) • Measure.dirac a,
    Measure.isProbabilityMeasure_finsetSum_ofReal_smul_dirac (fun a ↦ t.nonneg a)
      t.total_of_fintype⟩

omit [MeasurableSingletonClass α] in
/-- The probability measure of a probability vector depends measurably on the vector. -/
theorem measurable_toProbabilityMeasure :
    Measurable (StdSimplex.toProbabilityMeasure (α := α)) := by
  refine Measurable.subtype_mk (Measure.measurable_of_measurable_coe _ fun s _ ↦ ?_)
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  fun_prop

variable [DecidableEq α] [Nonempty α] {θ : α → ℝ}

/-- The law of the whole sequence of draws of the Pólya urn. -/
noncomputable def polyaUrnProcess (hθ : ∀ i, 0 < θ i) : Measure (ℕ → α) :=
  haveI := isMarkovKernel_polyaUrnRule hθ
  seqTrajectory (polyaUrnRule θ)

/-- The law of the whole sequence of draws of the Pólya urn is a probability measure. -/
instance (hθ : ∀ i, 0 < θ i) : IsProbabilityMeasure (polyaUrnProcess hθ) := by
  have := isMarkovKernel_polyaUrnRule hθ
  unfold polyaUrnProcess
  infer_instance

/-- The first `n` draws of the whole sequence have the law of `n` draws. -/
theorem polyaUrnProcess_map_restrict (hθ : ∀ i, 0 < θ i) (n : ℕ) :
    (polyaUrnProcess hθ).map (fun x (i : Fin n) ↦ x i) = polyaUrn θ n := by
  have := isMarkovKernel_polyaUrnRule hθ
  cases n with
  | zero =>
    rw [polyaUrn, seqLaw_zero,
      Subsingleton.elim (fun (x : ℕ → α) (i : Fin 0) ↦ x i) fun _ ↦ default, Measure.map_const,
      measure_univ, one_smul]
  | succ n => exact seqTrajectory_map_frestrictLe n

/-- The whole sequence of draws of the Pólya urn is a Dirichlet mixture of independent and
identically distributed sequences. -/
theorem polyaUrnProcess_eq_iid_comp (hθ : ∀ i, 0 < θ i) :
    polyaUrnProcess hθ =
      Kernel.iid ℕ α ∘ₘ (dirichlet θ).map StdSimplex.toProbabilityMeasure := by
  have := isProbabilityMeasure_dirichlet hθ
  refine ext_of_map_fin fun n ↦ ?_
  have hf : Measurable fun (x : ℕ → α) (i : Fin n) ↦ x i := by fun_prop
  rw [polyaUrnProcess_map_restrict, polyaUrn_eq_bind_dirichlet hθ, Measure.map_comp _ _ hf,
    Measure.bind_map measurable_toProbabilityMeasure.aemeasurable
      (Kernel.measurable _).aemeasurable]
  congr 1
  funext t
  rw [Kernel.map_apply _ hf, Kernel.iid_apply, infinitePi_map_fin]
  rfl

/-- The draws of the Pólya urn are exchangeable. -/
theorem exchangeable_polyaUrnProcess (hθ : ∀ i, 0 < θ i) :
    Exchangeable (fun i (x : ℕ → α) ↦ x i) (polyaUrnProcess hθ) :=
  exchangeable_of_map_eq_iid_comp aemeasurable_id
    (Measure.map_id.trans (polyaUrnProcess_eq_iid_comp hθ))

/-- The directing random measure of the Pólya urn has the Dirichlet law. -/
theorem map_directingMeasure_polyaUrnProcess (hθ : ∀ i, 0 < θ i) :
    (polyaUrnProcess hθ).map (directingMeasure (fun i (x : ℕ → α) ↦ x i) (polyaUrnProcess hθ)) =
      (dirichlet θ).map StdSimplex.toProbabilityMeasure := by
  have := isProbabilityMeasure_dirichlet hθ
  exact (eq_map_of_hasCondDistrib_iid (polyaUrnProcess_eq_iid_comp hθ) measurable_directingMeasure
    ((exchangeable_polyaUrnProcess hθ).contractable.hasCondDistrib_directingMeasure
      measurable_pi_apply)).symm

end ProbabilityTheory
