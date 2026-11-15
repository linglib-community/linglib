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
adjectives denote modifiers of intensional properties. At these modifiers the order-theoretic
classes of `Semantics/Modification/Basic.lean` take their familiar form: an intersective modifier
[conjoins every noun with one fixed property](##Modifier.isIntersective_iff_exists_forall) and is
[extensional](##Modifier.IsIntersective.isExtensional), nothing a privative modifier yields from
a noun [falls under the noun](##Modifier.isPrivative_iff_forall), and a privative modifier that
holds of something [is not subsective](##Modifier.IsPrivative.not_isSubsective), as
[*former*](##Modifier.former_isPrivative) is not over properties of times. The classification
descends from [parsons-1970] and [kamp-1975] through [kamp-partee-1995], whose labels these are.

## Implementation notes

Extensionality is independent of the classes; `Studies/Kamp1975.lean` gives the witnesses.
Whether adjectives uniformly denote `Modifier (W → E → Prop)` is a theoretical claim
(`Studies/Elbourne2026.lean`).

## References

* [parsons-1970]
* [kamp-1975]
* [kamp-partee-1995]
-/

public section

namespace Modifier

variable {W E : Type*} {adj : Modifier (W → E → Prop)}

/-- A modifier of intensional properties is intersective if and only if it conjoins every noun
with one fixed property, as *gray* does. -/
theorem isIntersective_iff_exists_forall :
    IsIntersective adj ↔
      ∃ Q : W → E → Prop, ∀ (N : W → E → Prop) (w : W) (x : E), adj N w x ↔ (Q w x ∧ N w x) := by
  simp only [IsIntersective, funext_iff, Pi.inf_apply, inf_Prop_eq, eq_iff_iff]

/-- A modifier of intensional properties is privative if and only if nothing it yields from a
noun falls under the noun, as with *fake*. -/
theorem isPrivative_iff_forall :
    IsPrivative adj ↔ ∀ (N : W → E → Prop) (w : W) (x : E), adj N w x → ¬ N w x := by
  simp only [IsPrivative, Pi.disjoint_iff, Prop.disjoint_iff, not_and]

/-- Intersective modifiers are extensional, since the meet with a fixed property reads the noun
only through its extension at each world. -/
theorem IsIntersective.isExtensional (h : IsIntersective adj) : IsExtensional adj :=
  h.elim fun Q hQ ↦ isExtensional_iff_exists_eq_piMap.2 ⟨fun w ↦ (Q w ⊓ ·), funext hQ⟩

/-- A privative modifier that holds of something is not subsective. -/
theorem IsPrivative.not_isSubsective (hp : IsPrivative adj) (hne : ∃ N w x, adj N w x) :
    ¬ IsSubsective adj :=
  fun hs ↦ hne.elim fun N ⟨w, x, h⟩ ↦ (congrFun₂ (hp.eq_bot hs N) w x).mp h

/-! ### *former* -/

section Former

variable {I : Type*}

/-- *former N* holds at `t` of what was an `N` at some earlier time and is not an `N` at `t`. -/
@[expose] def former [LT I] : Modifier (I → E → Prop) :=
  fun N t x ↦ (∃ t' < t, N t' x) ∧ ¬ N t x

@[simp] theorem former_apply [LT I] (N : I → E → Prop) (t : I) (x : E) :
    former N t x ↔ (∃ t' < t, N t' x) ∧ ¬ N t x :=
  Iff.rfl

theorem former_isPrivative [LT I] : IsPrivative (former : Modifier (I → E → Prop)) :=
  isPrivative_iff_forall.mpr fun _ _ _ h ↦ h.2

theorem former_not_isSubsective [Preorder I] {t' t : I} (h : t' < t) [Nonempty E] :
    ¬ IsSubsective (former : Modifier (I → E → Prop)) :=
  former_isPrivative.not_isSubsective
    ⟨fun s _ ↦ s = t', t, Classical.arbitrary E, ⟨t', h, rfl⟩, h.ne'⟩

end Former

end Modifier
