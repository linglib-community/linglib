/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# The domain action on functions is measurable

A monoid `M` acting on `ι` acts on the functions `ι → α` by precomposition, as the domain action
`Mᵈᵐᵃ` with `(DomMulAct.mk c • x) i = x (c • i)`. This action is measurable for the product
σ-algebra, so that the results on measures invariant under a measurable action apply to it.

`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Group/MeasurableEquiv.lean`.
-/

public section

/-- A monoid acting on `ι` acts measurably on `ι → α` by precomposition. -/
@[to_additive /-- An additive monoid acting on `ι` acts measurably on `ι → α` by
precomposition. -/]
instance {M ι α : Type*} [SMul M ι] [MeasurableSpace α] : MeasurableConstSMul Mᵈᵐᵃ (ι → α) :=
  ⟨fun _ ↦ Measurable.of_eval fun _ ↦ measurable_pi_apply _⟩
