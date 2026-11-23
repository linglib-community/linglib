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

A verb denotes a relation `R` of its participants, and a diathesis links each participant to a
slot or leaves it out. The relation of the slots that `R` gives in a diathesis `d` is
`d.denote R = mapIndex d.links.get R`: a participant the diathesis leaves out is closed
existentially, and participants that share a slot are identified.

Relinking a diathesis and reading off its relation is pushing the relation along the relinking,
`(d.relink τ gr).denote R = mapIndex τ (d.denote R)`, when no two participants share a slot the
relinking drops (`Diathesis.denote_relink`); in general the second entails the first
(`Diathesis.denote_relink_le`). So a relinking that only permutes slots leaves the proposition
unchanged up to the order of its arguments, and one that suppresses a slot closes its participant
existentially.

## References

* [melcuk-1993]
* [bach-1979]
* [chierchia-1984]
-/

@[expose] public section

open ArgumentStructure ArgumentFrame

namespace Diathesis

variable {A E Ψ : Type*} [CompleteLattice Ψ] {n : ℕ}

/-- The relation of the slots that a relation of the participants gives in a diathesis. -/
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
