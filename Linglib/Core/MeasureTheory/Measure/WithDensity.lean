/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Densities and pushforwards

Reweighting a measure by a density that factors through a map and then pushing forward along the
map is reweighting the pushforward by the factor. `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/Measure/WithDensity.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

theorem map_withDensity_comp {f : β → ℝ≥0∞} {g : α → β} (hf : AEMeasurable f (μ.map g))
    (hg : AEMeasurable g μ) : (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f :=
  ext fun s hs ↦ by
    rw [map_apply_of_aemeasurable (hg.mono_ac (withDensity_absolutelyContinuous _ _)) hs,
      withDensity_apply₀ _ (hg.nullMeasurable hs), withDensity_apply _ hs,
      restrict_map_of_aemeasurable hg hs]
    exact (lintegral_map' (restrict_map_of_aemeasurable hg hs ▸ hf.restrict) hg.restrict).symm

end MeasureTheory.Measure
