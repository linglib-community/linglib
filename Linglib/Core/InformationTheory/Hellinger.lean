/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Hellinger distance on a finite type

A measure on a finite type gives a vector of Euclidean space, the square roots of the masses of its
atoms. The Hellinger distance between two measures is the Euclidean distance between their vectors,
divided by `√2`. The inner product of the vectors is the Bhattacharyya coefficient
`∑ a, √(μ {a} ν {a})`, so the squared distance of two finite measures is the mean of their total
masses less that coefficient, and probability measures lie within distance one of each other, where
the Kullback–Leibler divergence may be infinite.

## Main definitions

* `MeasureTheory.Measure.sqrtMass μ`: the vector `a ↦ √(μ {a})` of `EuclideanSpace ℝ α`.
* `InformationTheory.hellingerDist μ ν`: the distance between `μ.sqrtMass` and `ν.sqrtMass`
  divided by `√2`.

## Main statements

* `hellingerDist_sq`: the squared distance is the mean total mass less the Bhattacharyya
  coefficient.
* `hellingerDist_le_one`: probability measures lie within distance one.
* `hellingerDist_dirac_left`: the distance from a Dirac mass.

## Implementation notes

As a distance on Euclidean space the Hellinger distance is symmetric and satisfies the triangle
inequality, the `L²` argument by which it is a metric. The factor `1/√2` bounds the distance
between probability measures by one; Polyanskiy and Wu omit it. Mathlib has no Hellinger
distance; in general it is an `f`-divergence of Radon–Nikodym derivatives, of which this is the
case of a finite type.

## References

* [polyanskiy-wu-2025]
-/

@[expose] public section

open Real Set
open scoped InnerProductSpace

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The square roots of the masses of a measure's atoms, as a vector of Euclidean space. -/
noncomputable def sqrtMass (μ : Measure α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 fun a ↦ √(μ.real {a})

@[simp]
theorem sqrtMass_apply (μ : Measure α) (a : α) : μ.sqrtMass a = √(μ.real {a}) := rfl

variable [Fintype α]

theorem inner_sqrtMass_nonneg (μ ν : Measure α) : 0 ≤ ⟪μ.sqrtMass, ν.sqrtMass⟫_ℝ :=
  Finset.sum_nonneg fun a _ ↦ mul_nonneg (sqrt_nonneg (ν.real {a})) (sqrt_nonneg (μ.real {a}))

variable [MeasurableSingletonClass α]

theorem norm_sqrtMass_sq (μ : Measure α) [IsFiniteMeasure μ] :
    ‖μ.sqrtMass‖ ^ 2 = μ.real univ := by
  simp [EuclideanSpace.real_norm_sq_eq, sq_sqrt measureReal_nonneg]

theorem inner_sqrtMass_dirac_left (a : α) (ν : Measure α) :
    ⟪(dirac a).sqrtMass, ν.sqrtMass⟫_ℝ = √(ν.real {a}) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb.symm]) (by simp)]
  simp

end MeasureTheory.Measure

namespace InformationTheory

open MeasureTheory Measure

variable {α : Type*} [MeasurableSpace α] [Fintype α] (μ ν : Measure α)

/-- The Hellinger distance `√(∑ a, (√(μ {a}) - √(ν {a})) ^ 2) / √2`, the Euclidean distance between
square-root mass vectors divided by `√2`. -/
noncomputable def hellingerDist : ℝ := dist μ.sqrtMass ν.sqrtMass / √2

theorem hellingerDist_nonneg : 0 ≤ hellingerDist μ ν := div_nonneg dist_nonneg (sqrt_nonneg 2)

variable [MeasurableSingletonClass α]

/-- The squared Hellinger distance of two finite measures is the mean of their total masses less
the Bhattacharyya coefficient. -/
theorem hellingerDist_sq [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDist μ ν ^ 2 = (μ.real univ + ν.real univ) / 2 - ⟪μ.sqrtMass, ν.sqrtMass⟫_ℝ := by
  rw [hellingerDist, div_pow, sq_sqrt zero_le_two, dist_eq_norm, norm_sub_sq_real,
    norm_sqrtMass_sq, norm_sqrtMass_sq]
  ring

/-- Probability measures, and the zero measure, lie within Hellinger distance one of each
other. -/
theorem hellingerDist_le_one [IsZeroOrProbabilityMeasure μ] [IsZeroOrProbabilityMeasure ν] :
    hellingerDist μ ν ≤ 1 := by
  refine (pow_le_one_iff_of_nonneg (hellingerDist_nonneg μ ν) two_ne_zero).1 ?_
  linarith [hellingerDist_sq μ ν, inner_sqrtMass_nonneg μ ν,
    measureReal_le_one (μ := μ) (s := univ), measureReal_le_one (μ := ν) (s := univ)]

/-- The Hellinger distance from a Dirac mass to a probability measure is fixed by the measure's
mass at the atom, and is one where that mass vanishes. -/
theorem hellingerDist_dirac_left [IsProbabilityMeasure ν] (a : α) :
    hellingerDist (dirac a) ν = √(1 - √(ν.real {a})) := by
  rw [← sqrt_sq (hellingerDist_nonneg _ ν), hellingerDist_sq, inner_sqrtMass_dirac_left, probReal_univ, probReal_univ]
  norm_num

end InformationTheory
