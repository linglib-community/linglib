/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Probability.Exchangeable
public import Linglib.Core.Probability.Kernel.IonescuTulcea.SeqLaw
public import Linglib.Core.Probability.PolyaUrn
public import Mathlib.MeasureTheory.Measure.Real

/-!
# The law of the Pólya urn

`polyaUrn θ n` is the law of the first `n` draws from the Pólya urn with weights `θ`: the
sequence drawn, by `seqLaw`, from the prediction rule `polyaUrnPredictive`. Each sequence has
probability `polyaUrnProb θ (countVec s)` (`polyaUrn_real_singleton`), which depends only on the
counts, so the sequence is exchangeable (`exchangeable_polyaUrn`).

## Main definitions

* `ProbabilityTheory.polyaUrnRule θ n`: the prediction rule as a kernel.
* `ProbabilityTheory.polyaUrn θ n`: the law of the first `n` draws.

## Main results

* `ProbabilityTheory.polyaUrn_real_singleton`: the probability of a sequence.
* `ProbabilityTheory.exchangeable_polyaUrn`: the drawn sequence is exchangeable.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  (θ : α → ℝ)

/-- The Pólya urn prediction rule as a kernel: after the draws `s`, colour `c` is drawn with
probability `polyaUrnPredictive θ (countVec s) c`. -/
noncomputable def polyaUrnRule (n : ℕ) : Kernel (Fin n → α) α :=
  Kernel.ofFunOfCountable fun s ↦
    Measure.ofRealWeights (polyaUrnPredictive θ (countVec s))

/-- The *Pólya urn*: the law of the first `n` draws from the urn with weights `θ`. -/
noncomputable def polyaUrn (n : ℕ) : Measure (Fin n → α) :=
  seqLaw (polyaUrnRule θ) n

theorem polyaUrnRule_apply_singleton {n : ℕ} (s : Fin n → α) (c : α) :
    polyaUrnRule θ n s {c} = ENNReal.ofReal (polyaUrnPredictive θ (countVec s) c) :=
  Measure.ofWeights_apply_singleton _ c

variable {θ} [Nonempty α] (hθ : ∀ i, 0 < θ i)
include hθ

theorem isMarkovKernel_polyaUrnRule (n : ℕ) : IsMarkovKernel (polyaUrnRule θ n) :=
  ⟨fun _ ↦ Measure.isProbabilityMeasure_sum_ofReal_smul_dirac
    (fun c ↦ polyaUrnPredictive_nonneg (fun i ↦ (hθ i).le) _ c) (sum_polyaUrnPredictive hθ _)⟩

theorem isProbabilityMeasure_polyaUrn (n : ℕ) : IsProbabilityMeasure (polyaUrn θ n) :=
  have := isMarkovKernel_polyaUrnRule hθ
  isProbabilityMeasure_seqLaw n

/-- The probability that the urn draws the sequence `s` is `polyaUrnProb θ (countVec s)`. -/
theorem polyaUrn_singleton : ∀ {n : ℕ} (s : Fin n → α),
    polyaUrn θ n {s} = ENNReal.ofReal (polyaUrnProb θ (countVec s))
  | 0, s => by simp [polyaUrn, Subsingleton.elim s default]
  | n + 1, s => by
    have := isMarkovKernel_polyaUrnRule hθ
    rw [polyaUrn, ← Fin.snoc_init_self s, seqLaw_succ_singleton_snoc, ← polyaUrn,
      polyaUrn_singleton, polyaUrnRule_apply_singleton,
      ← ENNReal.ofReal_mul (polyaUrnProb_pos hθ _).le, polyaUrnProb_countVec_snoc]

theorem polyaUrn_real_singleton {n : ℕ} (s : Fin n → α) :
    (polyaUrn θ n).real {s} = polyaUrnProb θ (countVec s) := by
  rw [measureReal_def, polyaUrn_singleton hθ, ENNReal.toReal_ofReal (polyaUrnProb_pos hθ _).le]

/-- The sequence drawn from a Pólya urn is exchangeable ([pitman-2006] Exercise 2.2.2). -/
theorem exchangeable_polyaUrn (n : ℕ) : Exchangeable (polyaUrn θ n) :=
  exchangeable_of_measure_singleton fun s σ ↦ by
    rw [polyaUrn_singleton hθ, polyaUrn_singleton hθ, countVec_comp_perm]

end ProbabilityTheory
