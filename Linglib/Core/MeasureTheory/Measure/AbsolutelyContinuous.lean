/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Absolute continuity on a countable type

On a countable type every set is a countable union of singletons, so `μ ≪ ν` is checked on
singletons: the `≪` counterpart of `MeasureTheory.Measure.ext_iff_singleton`. When `ν` charges
every singleton, `μ ≪ ν` needs no countability and follows from mathlib's `ae_eq_top`.
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`.
-/

public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [Countable α] {μ ν : Measure α}

theorem absolutelyContinuous_iff_forall_singleton : μ ≪ ν ↔ ∀ a, ν {a} = 0 → μ {a} = 0 :=
  ⟨fun h _ ha ↦ h ha, fun h s hs ↦ (measure_null_iff_singleton s.to_countable).2 fun a ha ↦
    h a ((measure_null_iff_singleton s.to_countable).1 hs a ha)⟩

alias ⟨_, absolutelyContinuous_of_forall_singleton⟩ := absolutelyContinuous_iff_forall_singleton

end MeasureTheory.Measure
