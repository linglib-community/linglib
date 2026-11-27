/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Chierchia1984
public import Linglib.Semantics.ArgumentStructure.Relation.MapArgs
public import Linglib.Syntax.Voice.Apply
public import Linglib.Languages.English.Verbs.Inventory
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Chierchia (1989): Structured Meanings, Thematic Roles and Control

This file formalizes the schema of control in [chierchia-1989].

As in [chierchia-1984], the infinitive of a control structure denotes a property. A relation that
takes a property has two frames. The frame `rP : (E → Φ) → X → Φ` takes a property, and the frame
`rS : Φ → X → Φ` takes a proposition. Here `X` is the type of the other constituents of an
eventuality and `Φ` is a complete lattice of propositions. A thematic role is a partial function
`θ : X →. E`.

We define two schemas.

* `Weak rP rS θ` says that `rP P x ≤ rS (P e) x` whenever `e` is the value of `θ x`.
* `Strict rP rS θ` says that for every `x`, the role `θ x` has a value `e` with
  `rP P x ≤ rS (P e) x`.

We show that the strict schema implies the weak one (`Strict.weak`), and that under the strict
schema `θ` is defined everywhere (`Strict.mem_dom`). So no operation can remove the controller
under the strict schema. Under the weak schema with the agent as controller, the passive
`mapArgs Prod.snd rP P y` entails that `rS (P a) (a, y)` holds for some agent `a`
(`mapArgs_snd_le`). A relation that obeys the Control Principle of [chierchia-1984] satisfies the
weak schema (`weak_of_controlPrinciple`).

For the English verbs, we show that the passive of a diathesis leaves its controller at an
expressed position exactly when the controller is the object
(`controller_expressed_passive_iff`).

## Implementation notes

* The source writes the two frames as one polymorphic relation.
* Passive is `mapArgs` along the second projection, for eventualities that pair an agent with the
  rest.

## TODO

* The source fills in the controller from a default hierarchy of roles: theme, then goal, then
  agent. This is not tested. The entries of the English control verbs record no entailment
  profiles, so no role label can be derived for them.
* Purpose clauses and control by the theme of a ditransitive are not formalized.

## References

* [chierchia-1989]
* [chierchia-1984]
-/

@[expose] public section

namespace Chierchia1989

open ArgumentStructure Chierchia1984

/-! ### The control schema -/

section Schema

variable {E Φ X Y A : Type*} [CompleteLattice Φ]

/-- (3): the control schema for a relation with property frame `rP` and propositional frame `rS`,
and the role `θ`. Whenever the role has a bearer, the relation's holding of a property entails its
holding of the proposition that the bearer has the property. -/
def Weak (rP : (E → Φ) → X → Φ) (rS : Φ → X → Φ) (θ : X →. E) : Prop :=
  ∀ P x, ∀ e ∈ θ x, rP P x ≤ rS (P e) x

/-- (6a): the strict schema, on which the role has a bearer in every eventuality of the
relation. -/
def Strict (rP : (E → Φ) → X → Φ) (rS : Φ → X → Φ) (θ : X →. E) : Prop :=
  ∀ P x, ∃ e ∈ θ x, rP P x ≤ rS (P e) x

variable {rP : (E → Φ) → X → Φ} {rS : Φ → X → Φ} {θ : X →. E}

theorem Strict.weak (h : Strict rP rS θ) : Weak rP rS θ := fun P x _ he ↦
  let ⟨_, he', hle⟩ := h P x
  Part.mem_unique he he' ▸ hle

/-- A relation satisfying the strict schema has the bearer of the controlling role among the
constituents of each of its eventualities. -/
theorem Strict.mem_dom (h : Strict rP rS θ) (x : X) : x ∈ θ.Dom :=
  let ⟨_, he, _⟩ := h (fun _ ↦ ⊥) x
  Part.dom_iff_mem.2 ⟨_, he⟩

-- (11a), (12)
theorem not_strict_of_notMem_dom {x : X} (hx : x ∉ θ.Dom) : ¬ Strict rP rS θ :=
  fun h ↦ hx (h.mem_dom x)

/-- A relation that reads its property only at an argument, taken at that argument's role,
satisfies the strict schema. -/
theorem strict_of_eq {c : X → E} (h : ∀ P x, rP P x = rS (P (c x)) x) :
    Strict rP rS (c : X →. E) :=
  fun P x ↦ ⟨c x, Part.mem_some _, (h P x).le⟩

-- (4), (5)
/-- Under the weak schema with the agent as controller, the passive of a relation entails that
for some agent the relation holds of the proposition that the agent has the property. -/
theorem mapArgs_snd_le {rP : (E → Φ) → E × Y → Φ} {rS : Φ → E × Y → Φ}
    (h : Weak rP rS (Prod.fst : E × Y → E)) (P : E → Φ) (y : Y) :
    mapArgs Prod.snd rP P y ≤ ⨆ a, rS (P a) (a, y) :=
  iSup₂_le fun x hx ↦
    hx ▸ (h P x x.1 (Part.mem_some _)).trans (le_iSup (fun a ↦ rS (P a) (a, x.2)) x.1)

-- [chierchia-1984]
theorem weak_of_controlPrinciple {W : Type*} {α : (E → Set W) → X → Set W} {θ : X →. E}
    {q : Modality.QuantificationalForce} {N : X → W → Filter W} (h : ControlPrinciple α θ q N) :
    Weak α (fun φ x ↦ q.claim (N x) φ) θ :=
  fun P _ _ he ↦ (h.eq_claim he P).le

end Schema

/-! ### The English verbs -/

open English.Verbs

-- (11), (14)
/-- The passive of a diathesis of an English verb leaves its controller at an expressed position
exactly when the controller is the object. -/
theorem controller_expressed_passive_iff : ∀ v ∈ verbs, ∀ d ∈ v.valency.diatheses,
    ∀ i ∈ d.controller,
      (∃ s ∈ ((Voice.passive d.toArgumentFrame).apply d).links.get i,
        ∃ p ∈ ((Voice.passive d.toArgumentFrame).apply d).get? s, p.IsExpressed) ↔
      d.controllerRole = some .P := by
  decide +kernel

end Chierchia1989
