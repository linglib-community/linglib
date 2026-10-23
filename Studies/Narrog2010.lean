module

public import Linglib.Semantics.Modality.Basic

/-!
# Narrog (2010): (Inter)subjectification in the Domain of Modality and Mood

This file formalizes the use [narrog-2010] makes of the eight most frequent changes of modal
meaning in the sample of [bybee-perkins-pagliuca-1994]. The chapter places the uses of modal
markers on a map with two dimensions. Volitivity separates the modalities in which an element
of will is present, deontic and boulomaic modality, from those in which it is absent, epistemic,
evidential, and dynamic modality (`ModalFlavor.IsVolitive`). Speaker orientation runs from
event-oriented uses up through modality proper to mood and illocutionary force modulation, and
the chapter's claim is that a change never decreases it, whatever the change does to volitivity.
The tabulated meanings are force-flavor pairs, the future, and two directive moods (`Meaning`),
which fixes the volitivity of source and target and tells modality proper from mood. On that
basis change is attested within and across the two sides of volitivity in every combination
(`volitivity_independent`), each change from non-volitive to volitive meaning is more frequent
than each deontic-to-epistemic one (`toNonVolitive_lt_toVolitive`), so the deontic-to-epistemic
shift is one change among several and not the representative one, and no change leads out of
mood (`source_not_isMood`). The changes into mood, future and possibility markers becoming
imperatives and admonitives and obligation markers becoming imperatives, reach the top of the
map and so conform wherever the source use lay. A change from probability to an event-oriented
obligation is what the chapter names as a counterexample and finds undocumented.

The chapter's second half asks why strong obligation is rarely grammaticalized: must-type
markers were found in sixty of two hundred languages, and the Japanese strong-necessity
construction occurs with no second-person subject in the corpus counts the chapter cites.
Imperatives are in principle always performative and used under full authority, while obligation
markers either report obligations or impose them without such authority, which is
face-threatening, so that direct reference to obligation is habitually avoided in many cultures
and obligation markers are less often available as sources of epistemic ones. That argument and
its counts are not formalized.

## Implementation notes

The chapter argues that the five tabulated changes within modality proper also increase speaker
orientation, the deontic-to-epistemic ones included, but it assigns no positions to their
meanings, and orientation is a property of a use and not of a meaning label, so no orientation
is assigned to a meaning here. The scale itself is `Narrog2012.SpeechActOrientation`, in the
later book's terms, and that study checks these changes against it. Strong obligation and
certainty are read as necessity, weak obligation and probability as weak necessity, and root
possibility and ability as circumstantial possibility; a label that does not mention strength is
read as the strong force. `ModalFlavor` files teleological modality under the circumstantial
flavor, which `IsVolitive` treats as non-volitive.

## References

* [narrog-2010]
* [bybee-perkins-pagliuca-1994]
-/

@[expose] public section

namespace Narrog2010

open Modality

/-- A flavor is volitive when an element of will is present in it, as in obligation,
permission, and wish, and non-volitive otherwise, as in epistemic assessment and ability. -/
def _root_.Modality.ModalFlavor.IsVolitive (f : ModalFlavor) : Prop :=
  f = .deontic ∨ f = .bouletic

instance : DecidablePred ModalFlavor.IsVolitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A meaning between which the tabulated changes run. A modal meaning is the set of
force-flavor pairs its label covers, as in `ModalItem.meaning`. -/
inductive Meaning where
  | modal (m : Finset ForceFlavor)
  /-- Future or prediction. -/
  | future
  | imperative
  | admonitive
  deriving DecidableEq

namespace Meaning

/-- Root possibility, which the table also lists with ability. -/
abbrev rootPossibility : Meaning := modal {(.possibility, .circumstantial)}
/-- Root or epistemic possibility. -/
abbrev possibility : Meaning :=
  modal {(.possibility, .circumstantial), (.possibility, .epistemic)}
abbrev permission : Meaning := modal {(.possibility, .deontic)}
abbrev obligation : Meaning := modal {(.necessity, .deontic)}
abbrev weakObligation : Meaning := modal {(.weakNecessity, .deontic)}
abbrev epistemicPossibility : Meaning := modal {(.possibility, .epistemic)}
abbrev probability : Meaning := modal {(.weakNecessity, .epistemic)}
abbrev certainty : Meaning := modal {(.necessity, .epistemic)}

/-- A modal meaning is volitive when all its flavors are, and the directive moods are. -/
def IsVolitive : Meaning → Prop
  | modal m => ∀ ff ∈ m, ff.flavor.IsVolitive
  | future => False
  | imperative | admonitive => True

/-- A modal meaning is non-volitive when none of its flavors is volitive, and the future is. -/
def IsNonVolitive : Meaning → Prop
  | modal m => ∀ ff ∈ m, ¬ ff.flavor.IsVolitive
  | future => True
  | imperative | admonitive => False

/-- The imperative and the admonitive mark speech acts and belong to mood, which lies at the
speech act-oriented end of the map; the other meanings belong to modality proper. -/
def IsMood : Meaning → Prop
  | imperative | admonitive => True
  | _ => False

instance : DecidablePred IsVolitive := fun m ↦ by cases m <;> unfold IsVolitive <;> infer_instance
instance : DecidablePred IsNonVolitive :=
  fun m ↦ by cases m <;> unfold IsNonVolitive <;> infer_instance
instance : DecidablePred IsMood := fun m ↦ by cases m <;> unfold IsMood <;> infer_instance

end Meaning

/-- A change of modal meaning, with the number of grams of the sample of
[bybee-perkins-pagliuca-1994] that show it, one gram per language. -/
structure Change where
  source : Meaning
  target : Meaning
  grams : ℕ

open Meaning in
/-- The eight most frequent changes of modal meaning in the sample of
[bybee-perkins-pagliuca-1994], as the chapter tabulates them. -/
def commonChanges : List Change :=
  [⟨future, imperative, 13⟩, ⟨rootPossibility, permission, 9⟩, ⟨possibility, admonitive, 5⟩,
   ⟨obligation, imperative, 4⟩, ⟨rootPossibility, epistemicPossibility, 4⟩,
   ⟨obligation, certainty, 3⟩, ⟨weakObligation, probability, 2⟩, ⟨future, probability, 2⟩]

theorem volitivity_independent :
    (∃ c ∈ commonChanges, c.source.IsVolitive ∧ c.target.IsVolitive) ∧
    (∃ c ∈ commonChanges, c.source.IsVolitive ∧ c.target.IsNonVolitive) ∧
    (∃ c ∈ commonChanges, c.source.IsNonVolitive ∧ c.target.IsVolitive) ∧
    (∃ c ∈ commonChanges, c.source.IsNonVolitive ∧ c.target.IsNonVolitive) := by
  decide

theorem toNonVolitive_lt_toVolitive :
    ∀ c ∈ commonChanges, ∀ d ∈ commonChanges,
      c.source.IsNonVolitive → c.target.IsVolitive →
      d.source.IsVolitive → d.target.IsNonVolitive → d.grams < c.grams := by
  decide

theorem source_not_isMood : ∀ c ∈ commonChanges, ¬ c.source.IsMood := by decide

theorem isMood_of_both_volitivities :
    (∃ c ∈ commonChanges, c.source.IsVolitive ∧ c.target.IsMood) ∧
    (∃ c ∈ commonChanges, c.source.IsNonVolitive ∧ c.target.IsMood) := by
  decide

end Narrog2010
