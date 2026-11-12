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

A choice rule takes a reference measure on a finite set of alternatives and a cost on them, with
an infinite cost for an alternative that is excluded, and returns a measure on the alternatives.
Three principles are stated for such a rule, besides its returning a probability measure whenever
some alternative of positive reference mass is not excluded:

* consistency: relabelling or merging alternatives commutes with the rule, and so does restricting
  the reference to a subset;
* independence: two independent choices, whose costs add, are made independently;
* monotonicity: a costlier alternative is not favoured beyond its reference mass, so that
  alternatives of equal cost keep their reference odds.

Reweighting the reference by `exp (-α * c)` and normalizing [satisfies
them](##InformationTheory.isChoiceRule_reweight) at every inverse temperature `α`. A rule
satisfying them is [that reweighting at some `α`](##InformationTheory.IsChoiceRule.eq), or one of
the two ends of the family: it conditions the reference on the alternatives that are not excluded,
or on those of least cost. With costs that are zero or infinite, every member of the family at a
positive `α` conditions on the alternatives that are not excluded.

## Implementation notes

* Independence is what selects the exponential: reweighting by another decreasing function of the
  cost satisfies the other principles.
* A probability measure is required only where some alternative of positive reference mass has
  finite cost. Required everywhere, it would leave only the rule that returns the reference, since
  an independent choice among excluded alternatives erases the cost of the choice it is paired
  with.
* The temperature is one constant of the rule, the same for every set of alternatives.

## TODO

* Prove `isChoiceRule_reweight` and `IsChoiceRule.eq`. For the second: monotonicity in both
  directions makes the rule proportional to the reference on alternatives of equal cost; merging
  along an inclusion gives absolute continuity; independence with a one-point choice gives
  invariance under adding a constant to the cost; restriction to pairs, with merging, makes the
  odds of two cost levels their reference odds times a function of the two costs; independence
  makes that function multiplicative in the cost difference, and monotonicity bounds it by one, so
  it is an exponential or vanishes off zero; independence fixes its value at an infinite cost.
* The axiomatic derivations of minimum cross-entropy and of the Gibbs posterior state related
  principles for a rule that takes constraints or a loss; the correspondence is not recorded here.

## References

* [luce-1959]
* [mcfadden-1974]
* [franke-degen-2023]
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
  /-- The rule returns a probability measure when some alternative of positive reference mass has
  finite cost. -/
  isProbabilityMeasure {β : Type u} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞) (h : ∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) :
    IsProbabilityMeasure (R β μ c)
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

/-- Reweighting the reference by `exp (-α * c)` and normalizing satisfies the principles. -/
theorem isChoiceRule_reweight {α : ℝ} (hα : 0 ≤ α) :
    IsChoiceRule.{u} fun β _ _ _ μ c ↦ (μ.withDensity fun x ↦
      EReal.exp (-((ENNReal.ofReal α * c x : ℝ≥0∞) : EReal)))[|Set.univ] := by
  sorry

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
        (μ : Measure β) [IsProbabilityMeasure μ] (c : β → ℝ≥0∞), (∃ x, μ {x} ≠ 0 ∧ c x ≠ ∞) →
        R β μ c = μ[|{x | ∀ y, μ {y} ≠ 0 → c x ≤ c y}]) := by
  sorry

end InformationTheory
