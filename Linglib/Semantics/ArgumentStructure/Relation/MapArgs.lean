/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Maps of a relation's arguments

A verb denotes a relation `R : A → X → Ψ` of its arguments `X`, with `A` whatever else it takes
and `Ψ` the propositions. The arguments change along a map. For `σ : Y → X`, `comapArgs σ R` is
the relation of `y` that `R` is of `σ y`. For `σ : X → Y` and `Ψ` a complete lattice,
`mapArgs σ R a y` is the join of `R a x` over the `x` with `σ x = y`: the arguments that `σ`
forgets are quantified existentially, as passive does the subject of a verb and
detransitivization its object.

The two are adjoint (`gc_mapArgs_comapArgs`), so `mapArgs` preserves joins and entailments,
`mapArgs σ R` is `⊥` only if `R` is (`mapArgs_eq_bot`), and along a surjection
`mapArgs σ (comapArgs σ R) = R` (`mapArgs_comapArgs`).

## Implementation notes

`mapArgs` and `comapArgs` are to a relation's arguments what `Finsupp.mapDomain` and
`Finsupp.comapDomain` are to a finitely supported function's, with a join for the sum. For
propositions that are sets of worlds they are the image and preimage of the relation as a set of
pairs, adjoint by `Set.image_preimage`.

## References

* [chierchia-1984]
* [chierchia-1989]
-/

@[expose] public section

open Function

namespace ArgumentStructure

variable {A Ψ W X Y Z : Type*}

/-- The relation of the arguments `y` that `R` is of `σ y`, the arguments followed along a map as
across the diatheses of a verb. -/
def comapArgs (σ : Y → X) (R : A → X → Ψ) : A → Y → Ψ :=
  fun a y ↦ R a (σ y)

@[simp] theorem comapArgs_apply (σ : Y → X) (R : A → X → Ψ) (a : A) (y : Y) :
    comapArgs σ R a y = R a (σ y) :=
  rfl

variable [CompleteLattice Ψ] {R : A → X → Ψ} {σ : X → Y}

/-- The relation of the arguments `y` that holds when `R` does of some `x` with `σ x = y`: the
arguments `σ` forgets are quantified existentially. -/
def mapArgs (σ : X → Y) (R : A → X → Ψ) : A → Y → Ψ :=
  fun a y ↦ ⨆ x, ⨆ (_ : σ x = y), R a x

theorem gc_mapArgs_comapArgs (σ : X → Y) :
    GaloisConnection (mapArgs σ : (A → X → Ψ) → _) (comapArgs σ) :=
  fun R _ ↦ ⟨fun h a x ↦ (le_iSup₂ (f := fun x' (_ : σ x' = σ x) ↦ R a x') x rfl).trans (h a (σ x)),
    fun h a _ ↦ iSup₂_le fun x hx ↦ hx ▸ h a x⟩

theorem le_mapArgs (σ : X → Y) (R : A → X → Ψ) (a : A) (x : X) : R a x ≤ mapArgs σ R a (σ x) :=
  (gc_mapArgs_comapArgs σ).le_u_l R a x

@[simp] theorem mapArgs_id (R : A → X → Ψ) : mapArgs id R = R := by
  funext a y
  simp [mapArgs]

theorem mapArgs_comp (τ : Y → Z) (σ : X → Y) (R : A → X → Ψ) :
    mapArgs (τ ∘ σ) R = mapArgs τ (mapArgs σ R) :=
  show _ = (mapArgs τ ∘ mapArgs σ) R from (gc_mapArgs_comapArgs (τ ∘ σ)).l_unique
    ((gc_mapArgs_comapArgs σ).compose (gc_mapArgs_comapArgs τ)) fun _ ↦ rfl

@[simp] theorem mapArgs_eq_bot : mapArgs σ R = ⊥ ↔ R = ⊥ :=
  (gc_mapArgs_comapArgs σ).l_eq_bot.trans le_bot_iff

/-- Along a surjection, a relation is recovered from its substitution instance by closing the
arguments the surjection forgets. -/
theorem mapArgs_comapArgs (hσ : Surjective σ) (R : A → Y → Ψ) :
    mapArgs σ (comapArgs σ R) = R := by
  funext a y
  obtain ⟨x, rfl⟩ := hσ y
  exact le_antisymm (iSup₂_le fun x' hx' ↦ (congrArg (R a) hx').le)
    (le_mapArgs σ (comapArgs σ R) a x)

@[simp] theorem mem_mapArgs {R : A → X → Set W} {a : A} {y : Y} {w : W} :
    w ∈ mapArgs σ R a y ↔ ∃ x, σ x = y ∧ w ∈ R a x := by
  simp [mapArgs]

end ArgumentStructure
