/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Singletons in sums and sigma types of measurable spaces

A singleton in `α ⊕ β` is the image of a singleton under `Sum.inl` or `Sum.inr`, and the fibre of
a singleton `{⟨i, x⟩}` of `Σ i, X i` over `j` is `{x}` when `j = i` and empty otherwise, so both
types have measurable singletons when their components do. A sum of discrete spaces is discrete.
`[UPSTREAM]` candidates for the `Sum` and `Sigma` instances of
`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`.
-/

@[expose] public section

open Set

section Sum

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

instance Sum.instMeasurableSingletonClass [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] : MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton
    | .inl a => image_singleton ▸ (measurableSet_singleton a).inl_image
    | .inr b => image_singleton ▸ (measurableSet_singleton b).inr_image

instance Sum.instDiscreteMeasurableSpace [DiscreteMeasurableSpace α]
    [DiscreteMeasurableSpace β] : DiscreteMeasurableSpace (α ⊕ β) :=
  ⟨fun _ ↦ measurableSet_sum_iff.2 ⟨.of_discrete, .of_discrete⟩⟩

end Sum

section Sigma

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

instance Sigma.instMeasurableSingletonClass [∀ i, MeasurableSingletonClass (X i)] :
    MeasurableSingletonClass (Sigma X) where
  measurableSet_singleton := fun ⟨i, x⟩ ↦ MeasurableSpace.measurableSet_iInf.2 fun j ↦ by
    rw [MeasurableSpace.map_def]
    obtain rfl | h := eq_or_ne j i
    · convert measurableSet_singleton x using 1; ext; simp
    · convert MeasurableSet.empty using 1; ext; simp [h]

end Sigma
