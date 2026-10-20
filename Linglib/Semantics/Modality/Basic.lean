module

public import Linglib.Pragmatics.SocialMeaning.Register
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Modal force and flavor

This file defines the vocabulary of modal typology. A modal force is a quantificational
strength, necessity, weak necessity or possibility, ordered by strength; a modal flavor is a
source of modality, epistemic, deontic, bouletic or circumstantial, after Kratzer; and a modal
item pairs a form with the force-flavor pairs it can express, the representation of a modal's
meaning in Imel, Guo and Steinert-Threlkeld's analysis of modal typology. Condoravdi's temporal
perspective and orientation locate a modal claim in time.

## Main definitions

* `Modality.ModalForce`, with the strength order `possibility < weakNecessity < necessity`,
  the classical dual `ModalForce.dual`, the concord class `ModalForce.IsUniversal`, and the
  classical force `ModalForce.classical`, which reads weak necessity as necessity.
* `Modality.ModalFlavor` and the pair type `Modality.ForceFlavor`.
* `Modality.ModalItem`, with its domain and variation predicates and its classical reading
  `ModalItem.classical`.
* `Modality.TemporalPerspective`, `Modality.TemporalOrientation`.

## References

* [kratzer-1981]
* [von-fintel-iatridou-2008]
* [rubinstein-2014]
* [agha-jeretic-2022]
* [agha-jeretic-2026]
* [imel-guo-steinert-threlkeld-2026]
* [zeijlstra-2007]
* [nauze-2008]
* [matthewson-2016]
* [condoravdi-2002]
-/

@[expose] public section

namespace Modality

/-! ### Modal force -/

/-- A modal force is a quantificational strength. Weak necessity, *ought* and *should*, lies
between necessity and possibility ([von-fintel-iatridou-2008]); whether it quantifies
universally over a narrower domain ([von-fintel-iatridou-2008]), compares alternatives
([rubinstein-2014]) or predicates of a plurality of worlds ([agha-jeretic-2022]) is open
([agha-jeretic-2026]). -/
inductive ModalForce where
  | necessity
  | weakNecessity
  | possibility
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace ModalForce

/-- The strength of a force, possibility the weakest. -/
def rank : ModalForce → ℕ
  | possibility => 0
  | weakNecessity => 1
  | necessity => 2

/-- Forces are ordered by strength: a necessity claim entails the weak necessity claim, which
entails the possibility claim. -/
instance : LinearOrder ModalForce := LinearOrder.lift' rank (by decide)

instance : BoundedOrder ModalForce where
  top := necessity
  le_top := by decide
  bot := possibility
  bot_le := by decide

/-- The classical dual exchanges necessity and possibility. Weak necessity has no settled
possibility counterpart ([agha-jeretic-2026] §2.4) and is sent to possibility. -/
def dual : ModalForce → ModalForce
  | necessity => possibility
  | weakNecessity => possibility
  | possibility => necessity

/-- Necessity and weak necessity quantify universally, the concord class that separates them
from possibility ([zeijlstra-2007]). -/
def IsUniversal (f : ModalForce) : Prop := f ≠ possibility

instance : DecidablePred IsUniversal := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The classical force of a force, on the two-point scale of necessity and possibility along
which [nauze-2008] and [matthewson-2016] compare modal systems: weak necessity quantifies
universally ([von-fintel-iatridou-2008]) and counts as necessity. -/
def classical : ModalForce → ModalForce
  | possibility => possibility
  | _ => necessity

variable {f : ModalForce}

/-- The classical dual is blind to the weak–strong distinction. -/
@[simp]
theorem dual_classical : f.classical.dual = f.dual := by cases f <;> rfl

/-- The double dual of a force is its classical force: dualizing twice closes weak necessity
up to necessity. -/
theorem dual_dual : f.dual.dual = f.classical := by cases f <;> rfl

@[simp]
theorem classical_eq_necessity_iff : f.classical = necessity ↔ f.IsUniversal := by
  cases f <;> decide

end ModalForce

/-! ### Modal flavor -/

/-- A modal flavor is the source of a modal claim: an epistemic or a circumstantial modal base,
or a circumstantial base ordered by what the law requires or what someone wants
([kratzer-1981]); teleological modality, ordered by goals, counts as circumstantial. -/
inductive ModalFlavor where
  | epistemic
  | deontic
  | bouletic
  | circumstantial
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A force-flavor pair is one point of the modal semantic space of
[imel-guo-steinert-threlkeld-2026], which has two forces and three flavors; weak necessity
([agha-jeretic-2026]) and bouletic flavor ([kratzer-1981]) extend the space to twelve points. -/
abbrev ForceFlavor := ModalForce × ModalFlavor

/-- The force of a force-flavor pair. -/
abbrev ForceFlavor.force : ForceFlavor → ModalForce := Prod.fst

/-- The flavor of a force-flavor pair. -/
abbrev ForceFlavor.flavor : ForceFlavor → ModalFlavor := Prod.snd

/-! ### Modal items -/

/-- A modal item is the shared core of an expression carrying modal meaning, which
`ModalAuxiliary` extends and which a modal adverb's entry instantiates directly. -/
structure ModalItem where
  form : String
  /-- The force-flavor pairs the item can express, in an upward-entailing context, or, for an
  item confined to non-affirmative contexts, as English auxiliary *need* and *dare* are, in the
  contexts that admit it. -/
  meaning : Finset ForceFlavor
  register : SocialMeaning.Register := .neutral
  deriving DecidableEq

namespace ModalItem

/-- A modal item is epistemic when every pair it expresses is. -/
def Epistemic (m : ModalItem) : Prop := ∀ ff ∈ m.meaning, ff.flavor = .epistemic

/-- A modal item is circumstantial, in the broad sense covering the priority flavours, when no
pair it expresses is epistemic. -/
def Circumstantial (m : ModalItem) : Prop := ∀ ff ∈ m.meaning, ff.flavor ≠ .epistemic

/-- The forces a modal item expresses. -/
def forces (m : ModalItem) : Finset ModalForce := m.meaning.image Prod.fst

/-- The flavours a modal item expresses. -/
def flavors (m : ModalItem) : Finset ModalFlavor := m.meaning.image Prod.snd

/-- The forces a modal item expresses under a flavour. -/
def forcesOf (m : ModalItem) (fl : ModalFlavor) : Finset ModalForce :=
  (m.meaning.filter (·.flavor = fl)).image Prod.fst

/-- A modal item varies in force when it expresses two forces. -/
def VariesForce (m : ModalItem) : Prop := 2 ≤ m.forces.card

/-- A modal item varies in flavour when it expresses two flavours. -/
def VariesFlavor (m : ModalItem) : Prop := 2 ≤ m.flavors.card

instance : DecidablePred Epistemic := fun _ ↦ inferInstanceAs (Decidable (∀ _ ∈ _, _ = _))

instance : DecidablePred Circumstantial := fun _ ↦ inferInstanceAs (Decidable (∀ _ ∈ _, _ ≠ _))

instance : DecidablePred VariesForce := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

instance : DecidablePred VariesFlavor := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

/-- A modal item on the classical force scale, its weak necessity read as necessity. -/
def classical (m : ModalItem) : ModalItem :=
  { m with meaning := m.meaning.image (Prod.map ModalForce.classical id) }

@[simp]
theorem forces_classical (m : ModalItem) :
    m.classical.forces = m.forces.image ModalForce.classical := by
  simp only [classical, forces, Finset.image_image, Prod.map_fst']

@[simp]
theorem flavors_classical (m : ModalItem) : m.classical.flavors = m.flavors := by
  simp only [classical, flavors, Finset.image_image, Prod.map_snd', Function.id_comp]

end ModalItem

/-! ### Modal-temporal axes

The two temporal axes of modal interpretation ([condoravdi-2002] §2): the perspective is the
time at which the modal base and ordering source are evaluated, the orientation the relation
between the perspective time and the prejacent's time. [condoravdi-2002] uses only the future
and past orientations. -/

/-- The time at which a modal base and ordering source are evaluated. -/
inductive TemporalPerspective where
  /-- Evaluation at the utterance time. -/
  | present
  /-- Evaluation at a prior time, as under a perfect. -/
  | past
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The relation between the perspective time and the prejacent's instantiation time. -/
inductive TemporalOrientation where
  /-- The prejacent is instantiated before the perspective time. -/
  | past
  /-- The prejacent coincides with the perspective time. -/
  | present
  /-- The prejacent is instantiated at or after the perspective time. -/
  | future
  deriving DecidableEq, Repr, Inhabited, Fintype

end Modality
