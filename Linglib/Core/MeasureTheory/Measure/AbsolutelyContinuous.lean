/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Absolute continuity on a countable type

On a countable type with measurable singletons, absolute continuity is checked on atoms.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`.
-/

public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [Countable α] {μ ν : Measure α}

theorem absolutelyContinuous_of_forall_singleton (h : ∀ a, ν {a} = 0 → μ {a} = 0) : μ ≪ ν := by
  refine AbsolutelyContinuous.mk fun s _ hs => ?_
  rw [← Set.biUnion_of_singleton s, measure_biUnion_null_iff s.to_countable] at hs ⊢
  exact fun a ha => h a (hs a ha)

theorem absolutelyContinuous_iff_forall_singleton : μ ≪ ν ↔ ∀ a, ν {a} = 0 → μ {a} = 0 :=
  ⟨fun h _ ha => h ha, absolutelyContinuous_of_forall_singleton⟩

end MeasureTheory.Measure
