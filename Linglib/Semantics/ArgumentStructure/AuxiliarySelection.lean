/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Perfect-auxiliary selection (be/have)

Many Romance and Germanic languages form the perfect with either *be* or *have*, and the choice
tracks split intransitivity. The binary account, Burzio's for Italian, has unaccusatives and
reflexives take *be* (Italian *è arrivato*, French *est arrivé*) and unergatives and transitives
*have* (Italian *ha mangiato*); German and Dutch reflexives take *have* (Sorace §1). Sorace
refines the intransitives into the Auxiliary Selection
Hierarchy, a chain of seven aspectual and thematic verb types along which the preference for
*be* falls: the verbs at the two ends choose their auxiliary categorically and in every language,
the verbs between them vary, and each language draws its cutoff between *be* and *have* at its
own point. The inflectional typology of auxiliary verb constructions lives in
`Syntax/Category/Auxiliary/Constructions.lean`.

## Main definitions

* `TransitivityClass` and its `selection`, `canonicalSelection` and `SelectsBe`: the binary
  account.
* `AuxiliarySelectionHierarchy`: the verb types of the Auxiliary Selection Hierarchy, a bounded
  linear order with the type most consistent in taking *be* at the bottom.
* `AuxiliarySelectionHierarchy.ofVerb`: the type of a verb entry, read off its aspect, its
  direction of motion and its subject's volition.

## References

* [burzio-1986]
* [sorace-2000]
* [levin-hovav-1995]
-/

@[expose] public section

namespace ArgumentStructure

/-- Transitivity class relevant to auxiliary selection. -/
inductive TransitivityClass where
  /-- The subject is the theme, as of *arrive*, *fall* and *die*. -/
  | unaccusative
  /-- The subject is an agent and there is no object, as with *run* and *laugh*. -/
  | unergative
  /-- The subject is an agent and the object a theme, as with *eat* and *build*. -/
  | transitive
  /-- A reflexive clitic, which selects *be* in Romance and *have* in
      German. -/
  | reflexive
  deriving DecidableEq, Repr, Fintype

namespace TransitivityClass

/-- In the binary account of auxiliary selection, given the auxiliary of reflexives,
unaccusatives select *be*, unergatives and transitives *have*, and reflexives are the locus of
variation, *be* in Romance and *have* in German ([burzio-1986] for the Italian
generalization). -/
def selection (refl : Verb.PerfectAuxiliary) : TransitivityClass → Verb.PerfectAuxiliary
  | unaccusative => .be
  | reflexive    => refl
  | unergative   => .have
  | transitive   => .have

/-- Canonical (Romance) auxiliary selection gives reflexives *be*. -/
def canonicalSelection : TransitivityClass → Verb.PerfectAuxiliary := selection .be

/-- Does this transitivity class canonically select *be*? -/
def SelectsBe (c : TransitivityClass) : Prop :=
  c.canonicalSelection = .be

instance : DecidablePred SelectsBe := fun c =>
  inferInstanceAs (Decidable (c.canonicalSelection = .be))

end TransitivityClass

/-- The Auxiliary Selection Hierarchy ([sorace-2000], Table 1) orders the aspectual and thematic
types of monadic intransitive verbs from the type most consistent in taking *be* to the type most
consistent in taking *have*. The transitions and states come first, by decreasing telicity,
then the processes, by increasing control. The two ends are the core types, whose verbs choose
their auxiliary categorically. -/
inductive AuxiliarySelectionHierarchy where
  /-- A telic change of location, as *arrive*, *come* and *fall* denote. -/
  | changeOfLocation
  /-- A change of state, mostly without a specified endpoint, as *rise*, *rot*, *become* and *die*
denote. -/
  | changeOfState
  /-- The continuation of a pre-existing state, as *stay*, *remain*, *last* and *survive* denote. -/
  | continuationOfState
  /-- The existence of a state, as *be*, *exist*, *belong* and *seem* denote. -/
  | existenceOfState
  /-- A process without volition, as *tremble*, *cough*, verbs of emission and weather verbs
denote. -/
  | uncontrolledProcess
  /-- A controlled process of motion, whose agent undergoes an undirected displacement, as *run*,
      *swim* and *walk* denote. -/
  | motionalProcess
  /-- A controlled process without motion, which leaves its agent unaffected, as *work*, *play*
      and *talk* denote. -/
  | nonmotionalProcess
  deriving DecidableEq, Repr, Fintype

namespace AuxiliarySelectionHierarchy

/-- The types are ordered as they are listed. -/
instance : LinearOrder AuxiliarySelectionHierarchy :=
  LinearOrder.lift' AuxiliarySelectionHierarchy.ctorIdx (by decide)

instance : BoundedOrder AuxiliarySelectionHierarchy where
  bot := changeOfLocation
  bot_le := by decide
  top := nonmotionalProcess
  le_top := by decide

@[simp] theorem bot_eq_changeOfLocation : (⊥ : AuxiliarySelectionHierarchy) = changeOfLocation :=
  rfl

/-! ### The type of a verb entry -/

/-- The type of a monadic verb, read off its entry ([sorace-2000] §§3–4). A state is the
continuation of a state when the entry is phasal continuation, as *remain* is, and the existence of
one otherwise. A telic verb is a change of location when it lexicalizes a direction of motion and a
change of state otherwise. An atelic dynamic verb is a change of state when it measures change
along a scale, as *rise* does; a motional process when it displaces its theme; and otherwise a
nonmotional or an uncontrolled process, as its subject is volitional or not. `none` when the entry
lacks the Vendler class, or a process lacks the subject profile. -/
def ofVerb (v : Verb) : Option AuxiliarySelectionHierarchy := do
  let c ← v.vendlerClass
  if c.dynamicity = .stative then
    pure (if v.phasal = some .continuation then continuationOfState else existenceOfState)
  else if c.telicity = .telic then
    pure (if v.direction.any (· != .place) then changeOfLocation else changeOfState)
  else if v.scaleDimension.isSome then pure changeOfState
  else if v.direction.isSome then pure motionalProcess
  else (v.slotProfile? .external).map fun θ ↦
    if .volition ∈ θ then nonmotionalProcess else uncontrolledProcess

/-- A bounded directional phrase makes a dynamic verb that selects one a change of location, the
bottom of the hierarchy: the directed motion use in which verbs of manner of motion take *be*
([sorace-2000] §4.3, [levin-hovav-1995] p. 185). -/
theorem ofVerb_withPath_eq_bot {v : Verb} {p : Adposition.SpatialReading} (hv : v.TakesSpatial)
    (hb : p.IsBounded) {c : Aspect.VendlerClass} (hc : v.vendlerClass = some c)
    (hdyn : c.dynamicity = .dynamic) : ofVerb (v.withPath p) = some ⊥ := by
  simp [ofVerb, hv, hb.direction_ne_place, hb, hc, hdyn, Aspect.VendlerClass.telicity_telicize hdyn]

end AuxiliarySelectionHierarchy

end ArgumentStructure
