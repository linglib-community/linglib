/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable spaces on `Option`, and singletons in sums and sigma types

`Option α` carries the image of the σ-algebra of `α` under `some`, the σ-algebra of the sum of
`α` and a point: a set is measurable when its preimage under `some` is, so a function out of
`Option α` is measurable when its composite with `some` is.

A singleton in `α ⊕ β` or `Option α` is the image of a singleton or `{none}`, and the fibre of a
singleton `{⟨i, x⟩}` of `Σ i, X i` over `j` is `{x}` when `j = i` and empty otherwise, so these
types have measurable singletons when their components do. Sums and options of discrete spaces are
discrete. `[UPSTREAM]` candidates for `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`.

## Implementation notes

`WithTop α` and `ℕ∞` are synonyms of `Option α` with σ-algebras of their own, the Borel and the
discrete one, which the instance here does not reach. Both agree with it, the first when `α` is
Borel, since `none` is closed in `WithTop α` and `some` is an open embedding.
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

section Option

variable {α γ : Type*} [MeasurableSpace α]

instance Option.instMeasurableSpace : MeasurableSpace (Option α) := ‹MeasurableSpace α›.map some

theorem measurableSet_option_iff {s : Set (Option α)} :
    MeasurableSet s ↔ MeasurableSet (some ⁻¹' s) :=
  Iff.rfl

@[fun_prop]
theorem measurable_some : Measurable (some : α → Option α) := fun _ ↦ id

theorem measurable_fun_option {_ : MeasurableSpace γ} {f : Option α → γ}
    (h : Measurable (f ∘ some)) : Measurable f :=
  fun _ hs ↦ h hs

@[simp] theorem measurableSet_some_image {s : Set α} :
    MeasurableSet (some '' s) ↔ MeasurableSet s := by
  simp [measurableSet_option_iff, (Option.some_injective α).preimage_image]

alias ⟨_, MeasurableSet.some_image⟩ := measurableSet_some_image

theorem measurableSet_range_some : MeasurableSet (range (some : α → Option α)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.some_image

instance Option.instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton
    | none => compl_range_some α ▸ measurableSet_range_some.compl
    | some a => image_singleton ▸ (measurableSet_singleton a).some_image

instance Option.instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ ↦ measurableSet_option_iff.2 .of_discrete⟩

end Option

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
