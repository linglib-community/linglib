module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Pragmatics.SocialMeaning.Register

/-!
# Modal items

A modal item pairs a form with the force-flavor pairs it can express, the representation of a
modal's meaning in Imel, Guo and Steinert-Threlkeld's analysis of modal typology, and records the
register of the form. A modal auxiliary's entry extends it and a modal adverb's instantiates it
directly. Two items form a Horn scale when they differ in quantificational force and share a flavor.

## Main definitions

* `Modality.ModalItem`, with its domain and variation predicates, its classical reading
  `ModalItem.quantificationalMeaning`, and the Horn scales it forms, `ModalItem.Scalemates`,
  with the forces of its scalemates, `ModalItem.scalemateForces`.

## References

* [imel-guo-steinert-threlkeld-2026]
* [deal-2011]
* [grano-2026]
-/

@[expose] public section

namespace Modality

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

/-- The meaning of a modal item by quantificational force, its weak necessity quantifying
universally: the two-way scale of necessity and possibility along which [nauze-2008] and
[matthewson-2016] compare modal systems. -/
def quantificationalMeaning (m : ModalItem) : Finset (QuantificationalForce × ModalFlavor) :=
  m.meaning.image (Prod.map ModalForce.quantificational id)

/-- The quantificational forces a modal item expresses. -/
def quantificationalForces (m : ModalItem) : Finset QuantificationalForce :=
  m.forces.image ModalForce.quantificational

@[simp]
theorem image_fst_quantificationalMeaning (m : ModalItem) :
    m.quantificationalMeaning.image Prod.fst = m.quantificationalForces := by
  simp only [quantificationalMeaning, quantificationalForces, forces, Finset.image_image,
    Prod.map_fst']

@[simp]
theorem image_snd_quantificationalMeaning (m : ModalItem) :
    m.quantificationalMeaning.image Prod.snd = m.flavors := by
  simp only [quantificationalMeaning, flavors, Finset.image_image, Prod.map_snd',
    Function.id_comp]

/-- A modal item varies in quantificational force when it expresses both. -/
def VariesQuantificationalForce (m : ModalItem) : Prop := 2 ≤ m.quantificationalForces.card

instance : DecidablePred VariesQuantificationalForce :=
  fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

/-- Two modals are scalemates, forming a Horn scale, when their lexical quantificational forces
`lex` differ and they share a flavour: only quantifiers over the same domain form a scale
([deal-2011] §2.1). A modal with a weaker scalemate leaves the weaker force to it
([grano-2026] §4.5). -/
def Scalemates (lex : ModalItem → QuantificationalForce) (m m' : ModalItem) : Prop :=
  lex m ≠ lex m' ∧ ∃ fl ∈ m.flavors, fl ∈ m'.flavors

/-- A modal has a scalemate in an inventory. -/
def HasScalemate (lex : ModalItem → QuantificationalForce) (L : List ModalItem)
    (m : ModalItem) : Prop :=
  ∃ m' ∈ L, Scalemates lex m m'

/-- The lexical forces of a modal's scalemates in an inventory, the forces of the alternatives
to its use. -/
def scalemateForces (lex : ModalItem → QuantificationalForce) (L : List ModalItem)
    (m : ModalItem) : Set QuantificationalForce :=
  {q | ∃ m' ∈ L, Scalemates lex m m' ∧ lex m' = q}

theorem scalemateForces_nonempty {lex : ModalItem → QuantificationalForce} {L : List ModalItem}
    {m : ModalItem} : (scalemateForces lex L m).Nonempty ↔ HasScalemate lex L m :=
  ⟨fun ⟨_, m', hm, hs, _⟩ ↦ ⟨m', hm, hs⟩, fun ⟨m', hm, hs⟩ ↦ ⟨lex m', m', hm, hs, rfl⟩⟩

instance (lex : ModalItem → QuantificationalForce) (m m' : ModalItem) :
    Decidable (Scalemates lex m m') :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _))

instance (lex : ModalItem → QuantificationalForce) (L : List ModalItem) (m : ModalItem) :
    Decidable (HasScalemate lex L m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (lex : ModalItem → QuantificationalForce) (L : List ModalItem) (m : ModalItem) :
    DecidablePred (· ∈ scalemateForces lex L m) := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _ ∧ _))

end ModalItem

end Modality
