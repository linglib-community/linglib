/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.KullbackLeibler.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Principles that determine reweighting

A choice rule takes a reference measure on a finite set of alternatives and a cost on them, and
returns a measure on the alternatives. Four principles are stated for such a rule:

* with no costs it returns the reference;
* it is consistent under relabelling and merging alternatives, and under restricting to a subset;
* independent choices, whose costs add, are made independently;
* a costlier alternative is not favoured beyond its reference mass.

A rule satisfying them is [one of a one-parameter family](##InformationTheory.IsChoiceRule.eq):
at an inverse temperature `α` it reweights the reference by `exp (-α * c)` and normalizes, and at
the two ends of the family it conditions the reference on the alternatives of finite cost, or on
those of least cost.

## TODO

* Prove `IsChoiceRule.eq`. Restriction and the zero-cost principle make the rule proportional to
  the reference on alternatives of equal cost; merging makes the odds of two cost levels linear in
  their reference masses; independence makes the odds a multiplicative function of the cost
  difference, which monotonicity makes an exponential or infinite.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace InformationTheory

/-- A choice rule returns, for a reference measure and a cost on a finite type, a measure on it. -/
abbrev ChoiceRule : Type (u + 1) :=
  ∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β],
    Measure β → (β → ℝ≥0∞) → Measure β

/-- The principles for a choice rule. -/
structure IsChoiceRule (R : ChoiceRule.{u}) : Prop where
  /-- From a probability reference the rule returns a probability measure. -/
  isProbabilityMeasure {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) : IsProbabilityMeasure (R β μ c)
  /-- With no costs the rule returns the reference. -/
  zero {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] : R β μ 0 = μ
  /-- Relabelling or merging alternatives, with the cost defined on the merged ones, commutes with
  the rule. -/
  map {β γ : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (f : β → γ) (μ : Measure β)
    [IsProbabilityMeasure μ] (c : γ → ℝ≥0∞) : (R β μ (c ∘ f)).map f = R γ (μ.map f) c
  /-- Restricting the reference to a set the rule gives positive mass restricts the rule. -/
  cond {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) (s : Set β) (hs : R β μ c s ≠ 0) :
    R β μ[|s] c = (R β μ c)[|s]
  /-- Independent choices whose costs add are made independently. -/
  prod {β γ : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (μ : Measure β) [IsProbabilityMeasure μ]
    (ν : Measure γ) [IsProbabilityMeasure ν] (c : β → ℝ≥0∞) (d : γ → ℝ≥0∞) :
    R (β × γ) (μ.prod ν) (fun p ↦ c p.1 + d p.2) = (R β μ c).prod (R γ ν d)
  /-- A costlier alternative is not favoured beyond its reference mass. -/
  mono {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) {x y : β} (h : c x ≤ c y) :
    R β μ c {y} * μ {x} ≤ R β μ c {x} * μ {y}

/-- A rule satisfying the principles reweights the reference by `exp (-α * c)` at some inverse
temperature `α` and normalizes, or conditions the reference on the alternatives of finite cost, or
conditions it on the alternatives of least cost. -/
theorem IsChoiceRule.eq {R : ChoiceRule.{u}} (hR : IsChoiceRule R) :
    (∃ α : ℝ, 0 ≤ α ∧ ∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞), (∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) →
        R β μ c = (μ.withDensity fun x ↦
          EReal.exp (-((ENNReal.ofReal α * c x : ℝ≥0∞) : EReal)))[|Set.univ]) ∨
    (∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞), (∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) →
        R β μ c = μ[|{x | c x ≠ ∞}]) ∨
    (∀ (β : Type u) [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞),
        R β μ c = μ[|{x | ∀ y, μ {y} ≠ 0 → c x ≤ c y}]) := by
  sorry

end InformationTheory
