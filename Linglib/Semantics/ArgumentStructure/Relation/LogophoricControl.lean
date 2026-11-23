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

This file defines a second way in which a relation can read a property complement. It is the way
[landau-2015] proposes for attitude predicates.

A *center* is a point of evaluation that fixes an author and an addressee. We write `C` for the
type of centers. A property of centers is a function `P : α → Set C`. A *concept* is a function
`c : C → α`. It picks out an entity at each center, such as the author.

For a concept `c`, the set `deRe (Part.some ∘ c) P` contains the centers `q` such that
`q ∈ P (c q)`. We define `IsLogophoricAt R c` to say that `R P x` depends on `P` only through
this set.

We show that `R` is logophoric at `c` exactly when `R P x = A (deRe (Part.some ∘ c) P) x` for
some `A` (`isLogophoricAt_iff`). The relation `fun P x ↦ A x ⊆ deRe (Part.some ∘ c) P` is
logophoric at `c` (`isLogophoricAt_subset_deRe`). It is controlled at an argument `ctrl` when
`c q = ctrl x` for every `q ∈ A x` (`isControlledAt_subset_deRe`).

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

/-- A relation is logophoric at the concept `c` when it depends on the property `P` only
through the set of centers `q` with `q ∈ P (c q)`. -/
def IsLogophoricAt (R : (α → Set C) → X → Ψ) (c : C → α) : Prop :=
  ∀ ⦃P Q : α → Set C⦄ ⦃x : X⦄, deRe (Part.some ∘ c) P = deRe (Part.some ∘ c) Q → R P x = R Q x

/-- A relation is logophoric at `c` exactly when it is a relation to the set of centers `q`
with `q ∈ P (c q)`. -/
theorem isLogophoricAt_iff :
    IsLogophoricAt R c ↔ ∃ A : Set C → X → Ψ, ∀ P x, R P x = A (deRe (Part.some ∘ c) P) x :=
  ⟨fun h ↦ ⟨fun S x ↦ R (fun _ ↦ S) x, fun P _ ↦ h (Set.ext fun _ ↦ by simp)⟩,
    fun ⟨A, h⟩ P Q x hPQ ↦ by rw [h, h, hPQ]⟩

/-- The relation that holds when every center `q` in `A x` satisfies `q ∈ P (c q)` is
logophoric at `c`. -/
theorem isLogophoricAt_subset_deRe (A : X → Set C) (c : C → α) :
    IsLogophoricAt (fun P x ↦ A x ⊆ deRe (Part.some ∘ c) P) c :=
  fun _ _ x hPQ ↦ congrArg (A x ⊆ ·) hPQ

/-- That relation is controlled at the argument `ctrl` when `c q = ctrl x` for every center `q`
in `A x`. -/
theorem isControlledAt_subset_deRe {A : X → Set C} {ctrl : X → α}
    (h : ∀ x, ∀ q ∈ A x, c q = ctrl x) :
    IsControlledAt (fun P x ↦ A x ⊆ deRe (Part.some ∘ c) P) ctrl := by
  refine isControlledAt_coe.2 fun P Q x hPQ ↦ ?_
  refine propext ⟨fun hA q hq ↦ ?_, fun hA q hq ↦ ?_⟩ <;>
    have := hA hq <;> simp only [mem_deRe_comp_some, h x q hq] at this ⊢
  exacts [hPQ ▸ this, hPQ ▸ this]

end Logophoric

end ArgumentStructure
