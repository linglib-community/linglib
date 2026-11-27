/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable.Basic

/-!
# Contractable sequences of random variables

A sequence of random variables `X : ℕ → Ω → E` is *contractable* if every subsequence
`fun i ↦ X (f i)`, for `f` strictly increasing, has the same joint law as `X`. An exchangeable
sequence is contractable.

## Main definitions

* `ProbabilityTheory.Contractable X μ`: the sequence `X` is contractable under `μ`.

## References

* [kallenberg-2005]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section Contractable

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {μ : Measure Ω}
  {X : ℕ → Ω → E}

/-- A sequence of random variables `X : ℕ → Ω → E` is *contractable* if its joint law is
unchanged by passing to any subsequence. -/
structure Contractable (X : ℕ → Ω → E) (μ : Measure Ω := by volume_tac) : Prop where
  /-- The sequence is jointly almost everywhere measurable, so that its joint law is defined. -/
  protected aemeasurable : AEMeasurable (fun ω i ↦ X i ω) μ
  /-- Passing to a subsequence does not change the joint law. -/
  protected map_eq (f : ℕ → ℕ) (hf : StrictMono f) :
    μ.map (fun ω i ↦ X (f i) ω) = μ.map fun ω i ↦ X i ω

/-- Under a finite measure, an exchangeable sequence is contractable. -/
theorem Exchangeable.contractable [IsFiniteMeasure μ] (h : Exchangeable X μ) :
    Contractable X μ :=
  ⟨h.aemeasurable, fun _ hf ↦ h.map_precomp_eq hf.injective⟩

end Contractable

end ProbabilityTheory
