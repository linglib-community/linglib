/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Linglib.Core.Data.Part.Extensions

/-!
# The probability of a family of partial values

Under a product of probability measures, the set of total families extending a family of
partial values is a rectangle, and two families that settle disjoint sets of coordinates are
independent: the probability that both are extended is the product of the probabilities
(`MeasureTheory.Measure.pi_piExtensions_inter`). Their surprisals add.
-/

@[expose] public section

namespace MeasureTheory.Measure

open Part

variable {V : Type*} {α : V → Type*} [Fintype V] [∀ v, MeasurableSpace (α v)]
  (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)] {s t : ∀ v, Part (α v)}

/-- Families of partial values that settle disjoint sets of independent coordinates are
independent. -/
theorem pi_piExtensions_inter (h : ∀ v, s v = ⊥ ∨ t v = ⊥) :
    Measure.pi μ (piExtensions s ∩ piExtensions t) =
      Measure.pi μ (piExtensions s) * Measure.pi μ (piExtensions t) := by
  rw [piExtensions_eq_pi s, piExtensions_eq_pi t, ← Set.pi_inter_distrib, pi_pi, pi_pi, pi_pi,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rcases h v with hv | hv
  · rw [hv, extensions_bot, Set.univ_inter, measure_univ, one_mul]
  · rw [hv, extensions_bot, Set.inter_univ, measure_univ, mul_one]

end MeasureTheory.Measure
