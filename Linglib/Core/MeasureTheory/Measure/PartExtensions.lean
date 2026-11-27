/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Part
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The probability of a family of partial values

A family `s : ∀ v, Part (α v)` of partial values holds of the total families `x` that extend
it, those with `s ≤ fun v ↦ Part.some (x v)`. That set is a rectangle, so under a product of
probability measures two families that settle disjoint sets of coordinates are independent: the
probability that both are extended is the product of the probabilities
(`MeasureTheory.Measure.pi_setOf_le_some_inter`), and their surprisals add.
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {V : Type*} {α : V → Type*} [Fintype V] [∀ v, MeasurableSpace (α v)]
  (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)] {s t : ∀ v, Part (α v)}

/-- Families of partial values that settle disjoint sets of independent coordinates are
independent. -/
theorem pi_setOf_le_some_inter (h : ∀ v, s v = ⊥ ∨ t v = ⊥) :
    Measure.pi μ ({x | s ≤ fun v ↦ Part.some (x v)} ∩ {x | t ≤ fun v ↦ Part.some (x v)}) =
      Measure.pi μ {x | s ≤ fun v ↦ Part.some (x v)} *
        Measure.pi μ {x | t ≤ fun v ↦ Part.some (x v)} := by
  have hpi (r : ∀ v, Part (α v)) : {x : ∀ v, α v | r ≤ fun v ↦ Part.some (x v)} =
      Set.pi Set.univ fun v ↦ {a | r v ≤ Part.some a} :=
    Set.ext fun _ ↦ by simp only [Set.mem_ofPred_eq, Pi.le_def, Set.mem_univ_pi]
  rw [hpi s, hpi t, ← Set.pi_inter_distrib, pi_pi, pi_pi, pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hbot : {a : α v | (⊥ : Part (α v)) ≤ Part.some a} = Set.univ :=
    Set.eq_univ_of_forall fun a ↦ (bot_le : (⊥ : Part (α v)) ≤ Part.some a)
  rcases h v with hv | hv
  · rw [hv, hbot, Set.univ_inter, measure_univ, one_mul]
  · rw [hv, hbot, Set.inter_univ, measure_univ, mul_one]

end MeasureTheory.Measure
