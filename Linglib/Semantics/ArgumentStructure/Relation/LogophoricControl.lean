/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.ArgumentStructure.Relation.Control
public import Linglib.Semantics.Attitudes.Acquaintance

/-!
# Logophoric control

A controlled relation reads its property at an argument. In Landau's two-tiered theory that is
one of two ways control is established, predication, found under predicates that introduce no
attitude. Under an attitude predicate the complement is read at a coordinate of the reported
context, its author or addressee, as the holder of the attitude represents it: a relation to a
property of centers is *logophoric* at a concept `c` of centers, `IsLogophoricAt R c`, when it
reads the property only through the centers whose value under `c` has it, which is a relation to
the proposition self-ascribed (`isLogophoricAt_iff`).

Self-ascription over a set of alternatives is logophoric (`isLogophoricAt_subset_deRe`), and it
is controlled at an argument when the concept takes that argument as its value throughout the
alternatives (`isControlledAt_subset_deRe`), so that the two readings come apart only where the
holder may mistake who the coordinate is.

## References

* [landau-2015]
* [landau-2024a]
* [lewis-1979-attitudes]
-/

@[expose] public section

namespace ArgumentStructure

variable {Ψ X : Type*}

section Logophoric

open Acquaintance

variable {α C : Type*} {R : (α → Set C) → X → Ψ} {c : C → α}

/-- A relation to a property of centers is logophoric at the concept `c` when it depends on the
property only through the centers whose value under `c` has it. -/
def IsLogophoricAt (R : (α → Set C) → X → Ψ) (c : C → α) : Prop :=
  ∀ ⦃P Q : α → Set C⦄ ⦃x : X⦄, deRe (Part.some ∘ c) P = deRe (Part.some ∘ c) Q → R P x = R Q x

/-- A relation is logophoric at `c` exactly when it is a relation to a proposition, taken at the
centers whose value under `c` has the property. -/
theorem isLogophoricAt_iff :
    IsLogophoricAt R c ↔ ∃ A : Set C → X → Ψ, ∀ P x, R P x = A (deRe (Part.some ∘ c) P) x :=
  ⟨fun h ↦ ⟨fun S x ↦ R (fun _ ↦ S) x, fun P _ ↦ h (Set.ext fun _ ↦ by simp)⟩,
    fun ⟨A, h⟩ P Q x hPQ ↦ by rw [h, h, hPQ]⟩

/-- Self-ascription, every alternative having the property of its own value under `c`, is
logophoric at `c`. -/
theorem isLogophoricAt_subset_deRe (A : X → Set C) (c : C → α) :
    IsLogophoricAt (fun P x ↦ A x ⊆ deRe (Part.some ∘ c) P) c :=
  fun _ _ x hPQ ↦ congrArg (A x ⊆ ·) hPQ

/-- Self-ascription is controlled at an argument when the concept takes that argument as its
value at every alternative: the reading at the coordinate and the reading at the argument agree
where the coordinate is not mistaken. -/
theorem isControlledAt_subset_deRe {A : X → Set C} {ctrl : X → α}
    (h : ∀ x, ∀ q ∈ A x, c q = ctrl x) :
    IsControlledAt (fun P x ↦ A x ⊆ deRe (Part.some ∘ c) P) ctrl := by
  refine isControlledAt_coe.2 fun P Q x hPQ ↦ ?_
  refine propext ⟨fun hA q hq ↦ ?_, fun hA q hq ↦ ?_⟩ <;>
    have := hA hq <;> simp only [mem_deRe_comp_some, h x q hq] at this ⊢
  exacts [hPQ ▸ this, hPQ ▸ this]

end Logophoric

end ArgumentStructure
