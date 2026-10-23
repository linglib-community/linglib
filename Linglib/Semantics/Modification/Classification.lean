module

public import Linglib.Semantics.Modification.Basic
public import Linglib.Semantics.Reference.Rigidity
public import Mathlib.Order.PropInstances
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Common
public import Linglib.Logic.Modal.Extensional

/-!
# Modifiers of intensional properties

An intensional property is a function from worlds to predicates of entities, and attributive
adjectives denote modifiers of intensional properties. At these modifiers Kamp's order-theoretic
classes (`Semantics/Modification/Basic.lean`) take their familiar pointwise form, an intersective
modifier is extensional, and a privative modifier that holds of something is not subsective. The
classification descends from Parsons and Kamp through Kamp and Partee; the labels are Partee's.

## Main definitions

* `Semantics.Property W E`: intensional properties, `W → E → Prop`.

## Main results

* `Semantics.Property.isIntersective_iff`, `isPrivative_iff`: the classes stated pointwise.
* `Semantics.Property.isExtensional_of_isIntersective`: intersective modifiers are extensional.
* `Semantics.Property.not_isSubsective_of_isPrivative`: a privative modifier that holds of something
  is not subsective.

## Implementation notes

Extensionality is independent of the classes; `Studies/Kamp1975.lean` gives the witnesses.
Whether adjectives uniformly denote `Modifier (Property W E)` is a theoretical claim
(`Studies/Elbourne2026.lean`).

## References

* [parsons-1970]
* [kamp-1975]
* [kamp-partee-1995]
-/

@[expose] public section

namespace Semantics

/-- An intensional property is a function from worlds to predicates over entities. -/
abbrev Property (W E : Type*) := W → E → Prop

namespace Property

open Modifier

variable {W E : Type*} {adj : Modifier (Property W E)}

@[simp] theorem intersective_apply (Q N : Property W E) (w : W) (x : E) :
    intersective Q N w x ↔ Q w x ∧ N w x :=
  Iff.rfl

/-- A modifier of intensional properties is intersective if and only if it conjoins every noun
with one fixed property, as *gray* does. -/
theorem isIntersective_iff :
    IsIntersective adj ↔
      ∃ (Q : Property W E), ∀ (N : Property W E) (w : W) (x : E),
        adj N w x ↔ (Q w x ∧ N w x) := by
  simp only [IsIntersective, funext_iff, Pi.inf_apply, inf_Prop_eq, eq_iff_iff]

/-- A modifier of intensional properties is privative if and only if nothing it yields from a
noun falls under the noun, as with *fake*. -/
theorem isPrivative_iff :
    IsPrivative adj ↔
      ∀ (N : Property W E) (w : W) (x : E), adj N w x → ¬ N w x := by
  simp only [IsPrivative, Pi.disjoint_iff, Prop.disjoint_iff, not_and]

/-- Intersective modifiers are extensional, since the meet with a fixed property reads the noun
only through its extension at each world. -/
theorem isExtensional_of_isIntersective (h : IsIntersective adj) :
    ModalLogic.IsExtensional adj := by
  obtain ⟨Q, hQ⟩ := h
  intro w N₁ N₂ hN
  simp only [hQ, Pi.inf_apply, hN]

/-- A privative modifier that holds of something is not subsective. -/
theorem not_isSubsective_of_isPrivative (hp : IsPrivative adj)
    (hne : ∃ N w x, adj N w x) : ¬ IsSubsective adj := by
  intro hs
  obtain ⟨N, w, x, hadj⟩ := hne
  exact isPrivative_iff.mp hp N w x hadj (hs N w x hadj)

end Property

end Semantics
