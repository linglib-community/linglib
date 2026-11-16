/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.ArgumentStructure.Control
public import Linglib.Fragments.English.Verbs.Inventory
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Chierchia (1989): Structured Meanings, Thematic Roles and Control

Chierchia takes the infinitive of a control structure to denote a property, and a thematic role
to be a partial function from an eventuality to one of its constituents. Control is then one
schema on the relations that take properties: if a relation holds of a property, it holds of the
proposition that the bearer of a designated role has it. The controller is a co-argument because a
role picks a constituent, and unique because a role is a function. On the strict form of the
schema the role must have a bearer, so an operation that deletes the controller [has no
value](##Chierchia1989.Strict.isSome), which is why *it was tried to win* is out; on the weak
form, which holds only when the bearer is present, passive leaves [someone or other as the
controller](##Chierchia1989.pas_le), the implicit control of *it was decided to leave*.

The English verbs bear the schema out as far as their entries record it. Every verb whose object
controls [has a passive](##Chierchia1989.passivizable_of_object_control), the object surviving as
subject, and a verb whose subject controls has a passive only if [it has a frame without a
controlled complement](##Chierchia1989.exists_uncontrolled_of_passivizable), the weaker hypothesis
Chierchia adopts for *teach* and *try*.

## Implementation notes

Propositions are the elements of any complete lattice, entailment its order. An eventuality's
constituents other than the property are a type `X`, and a relation has one frame taking a
property and one taking a proposition, which Chierchia writes as one polymorphic relation. Passive
is stated for eventualities that pair an agent with the rest.

## TODO

* The default hierarchy of roles that fills in the controller, theme before goal before agent,
  is not tested: the entries of the English control verbs record no entailment profiles for their
  participants, so no role label is derivable for them.
* The entries record whether a verb passivizes as one value for the verb, where the schema
  predicts it frame by frame: *promise* passivizes with a noun-phrase object and not with an
  infinitive. `exists_uncontrolled_of_passivizable` is the most the entries support.
* Purpose clauses and control by the theme of a ditransitive are not formalized.

## References

* [chierchia-1989]
-/

@[expose] public section

namespace Chierchia1989

open ArgumentStructure

/-! ### The control schema -/

section Schema

variable {E Φ X Y A : Type*} [CompleteLattice Φ]

/-- (3): the control schema for a relation with property frame `rP` and propositional frame `rS`,
and the role `θ`. Whenever the role has a bearer, the relation's holding of a property entails its
holding of the proposition that the bearer has the property. -/
def Weak (rP : (E → Φ) → X → Φ) (rS : Φ → X → Φ) (θ : X → Option E) : Prop :=
  ∀ P x, ∀ e ∈ θ x, rP P x ≤ rS (P e) x

/-- (6a): the strict schema, on which the role has a bearer in every eventuality of the
relation. -/
def Strict (rP : (E → Φ) → X → Φ) (rS : Φ → X → Φ) (θ : X → Option E) : Prop :=
  ∀ P x, ∃ e ∈ θ x, rP P x ≤ rS (P e) x

variable {rP : (E → Φ) → X → Φ} {rS : Φ → X → Φ} {θ : X → Option E}

theorem Strict.weak (h : Strict rP rS θ) : Weak rP rS θ := fun P x _ he ↦
  let ⟨_, he', hle⟩ := h P x
  Option.mem_unique he he' ▸ hle

/-- A relation satisfying the strict schema has the bearer of the controlling role among the
constituents of each of its eventualities. -/
theorem Strict.isSome (h : Strict rP rS θ) (x : X) : (θ x).isSome :=
  let ⟨_, he, _⟩ := h (fun _ ↦ ⊥) x
  Option.isSome_iff_exists.2 ⟨_, he⟩

-- (11a), (12)
theorem not_strict_of_eq_none {x : X} (hx : θ x = none) : ¬ Strict rP rS θ :=
  fun h ↦ by simpa [hx] using h.isSome x

/-- A relation that reads its property only at an argument, taken at that argument's role,
satisfies the strict schema. -/
theorem strict_of_eq {c : X → E} (h : ∀ P x, rP P x = rS (P (c x)) x) :
    Strict rP rS fun x ↦ some (c x) :=
  fun P x ↦ ⟨c x, rfl, (h P x).le⟩

/-- (5): the passive of a relation whose eventualities pair an agent with the rest holds when the
relation holds for some agent. -/
def pas (r : (E → Φ) → A × Y → Φ) : (E → Φ) → Y → Φ := fun P y ↦ ⨆ a, r P (a, y)

-- (4), (5)
/-- Under the weak schema with the agent as controller, the passive of a relation entails that
for some agent the relation holds of the proposition that the agent has the property. -/
theorem pas_le {rP : (E → Φ) → E × Y → Φ} {rS : Φ → E × Y → Φ}
    (h : Weak rP rS fun (a, _) ↦ some a) (P : E → Φ) (y : Y) :
    pas rP P y ≤ ⨆ a, rS (P a) (a, y) :=
  iSup_mono fun a ↦ h P (a, y) a rfl

end Schema

/-! ### The English verbs -/

open English.Verbs

-- (11b)
/-- A verb whose complement is controlled by its object has a passive. -/
theorem passivizable_of_object_control : ∀ v ∈ verbs, ∀ d ∈ v.valency.diatheses,
    d.controllerRole = some .P → v.passivizable = true := by
  decide +kernel

-- (14), (15)
/-- A verb that has a passive, and whose complements are controlled by its subject wherever they
are controlled, has a frame without a controlled complement. -/
theorem exists_uncontrolled_of_passivizable : ∀ v ∈ verbs, v.passivizable = true →
    (∀ d ∈ v.valency.diatheses, d.controllerRole ≠ some .P) →
    (∃ d ∈ v.valency.diatheses, d.controller.isSome) →
      ∃ d ∈ v.valency.diatheses, d.controllerSlot? = none := by
  decide +kernel

end Chierchia1989
