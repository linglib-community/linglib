/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.ArgumentStructure.Relation.MapArgs
public import Linglib.Syntax.Voice.Apply

/-!
# The relation a diathesis denotes

A verb denotes a relation `R : A → (Fin n → E) → Ψ` of its `n` participants. A diathesis `d`
links each participant to a slot, or to no slot.

We define `d.denote R : A → (Slot → E) → Ψ` as `mapIndex d.links.get R`. So `d.denote R a y` is
the supremum of `R a x` over the tuples of participants `x` such that `x i = y s` whenever
participant `i` is at slot `s`. A participant at no slot is existentially quantified.

We show how `denote` interacts with `Diathesis.relink`. In general,
`mapIndex τ (d.denote R) ≤ (d.relink τ gr).denote R` (`Diathesis.denote_relink_le`). The two are
equal when no two participants of `d` share a slot that `τ` sends to `none`
(`Diathesis.denote_relink`).

## References

* [melcuk-1993]
* [chierchia-1984]
-/

@[expose] public section

open ArgumentStructure ArgumentFrame

namespace Diathesis

variable {A E Ψ : Type*} [CompleteLattice Ψ] {n : ℕ}

/-- The relation of the slots of a diathesis given by a relation `R` of its participants. -/
def denote (d : Diathesis n) (R : A → (Fin n → E) → Ψ) : A → (Slot → E) → Ψ :=
  mapIndex d.links.get R

theorem denote_relink_le (τ : Slot → Option Slot) (gr : ArgumentFrame) (d : Diathesis n)
    (R : A → (Fin n → E) → Ψ) : mapIndex τ (d.denote R) ≤ (d.relink τ gr).denote R := by
  have h : (d.relink τ gr).links.get = fun i ↦ (d.links.get i).bind τ :=
    funext (get_links_relink τ gr d)
  simpa only [denote, h] using mapIndex_mapIndex_le d.links.get τ R

theorem denote_relink (τ : Slot → Option Slot) (gr : ArgumentFrame) (d : Diathesis n)
    (h : ∀ i i' s, d.links.get i = some s → d.links.get i' = some s → τ s = none → i = i')
    (R : A → (Fin n → E) → Ψ) : (d.relink τ gr).denote R = mapIndex τ (d.denote R) := by
  have hl : (d.relink τ gr).links.get = fun i ↦ (d.links.get i).bind τ :=
    funext (get_links_relink τ gr d)
  funext a y
  have : Nonempty E := ⟨y .external⟩
  simp only [denote, hl, mapIndex_mapIndex d.links.get τ h R]

end Diathesis
