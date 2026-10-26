module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Pragmatics.SocialMeaning.Register

/-!
# Modal items

A modal item pairs a form with the force-flavor pairs it can express, the representation of a
modal's meaning in Imel, Guo and Steinert-Threlkeld's analysis of modal typology, and records the
register of the form. A modal auxiliary's entry extends it and a modal adverb's instantiates it
directly. Two items form a Horn scale when they differ in force and share a flavor.

## Main definitions

* `Modality.ModalItem`, with its domain and variation predicates, its classical reading
  `ModalItem.classical`, and the Horn scales it forms, `ModalItem.Scalemates`.

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

/-- Two modals are scalemates, forming a Horn scale, when their lexical forces `lex` differ on the
classical scale and they share a flavour: only quantifiers over the same domain form a scale
([deal-2011] §2.1). A modal with a weaker scalemate leaves the weaker force to it
([grano-2026] §4.5). -/
def Scalemates (lex : ModalItem → ModalForce) (m m' : ModalItem) : Prop :=
  (lex m).classical ≠ (lex m').classical ∧ ∃ fl ∈ m.flavors, fl ∈ m'.flavors

/-- A modal has a scalemate in an inventory. -/
def HasScalemate (lex : ModalItem → ModalForce) (L : List ModalItem) (m : ModalItem) : Prop :=
  ∃ m' ∈ L, Scalemates lex m m'

instance (lex : ModalItem → ModalForce) (m m' : ModalItem) : Decidable (Scalemates lex m m') :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _))

instance (lex : ModalItem → ModalForce) (L : List ModalItem) (m : ModalItem) :
    Decidable (HasScalemate lex L m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

end ModalItem

end Modality
