module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Data.Statistics.Narrog2010

/-!
# Narrog (2010): (Inter)subjectification in the Domain of Modality and Mood

[narrog-2010] places the uses of modal markers on a map with two dimensions. Volitivity separates
the modalities in which an element of will is present, deontic and boulomaic modality, from those
in which it is absent, epistemic, evidential and dynamic modality. Speaker orientation runs from
event-oriented uses up through modality proper to mood and illocutionary force modulation, and
the hypothesis is that a change of meaning never decreases it, whatever the change does to
volitivity.

We define volitivity on modal flavors (`Modality.ModalFlavor.IsVolitive`) and on the meanings
between which changes run (`Meaning`): a set of force-flavor pairs, the future, or one of two
directive moods, which lie in the area of mood (`Meaning.IsMood`). The chapter's table of the
eight most frequent changes in the sample of [bybee-perkins-pagliuca-1994] is
`Narrog2010.changes`, and `Label.meaning` gives the meaning of each of its labels. On the table,
change is attested within and across the two sides of volitivity in every combination
(`volitivity_independent`), each change from a non-volitive to a volitive meaning has more grams
than any other change (`grams_lt_of_toVolitive`), and no change leads out of mood
(`isMood_target_of_isMood_source`). The grams of the table sum to the totals the chapter gives
for all changes, for changes out of situational possibility and for changes out of obligation
(`sum_grams`, `sum_grams_of_source`).

## Implementation notes

The chapter argues that the five tabulated changes within modality proper also increase speaker
orientation, the deontic-to-epistemic ones included, but it assigns no positions to their
meanings, and orientation is a property of a use and not of a meaning label, so no orientation
is assigned to a meaning here. The scale itself is `Narrog2012.SpeechActOrientation`, in the
later book's terms, and that study checks these changes against it.

Strong obligation and certainty are read as necessity, weak obligation and probability as weak
necessity, obligation without a strength as either, and root possibility and ability as
circumstantial possibility. `ModalFlavor` files teleological modality under the circumstantial
flavor, which `IsVolitive` treats as non-volitive.

## TODO

The chapter's counts of obligation and possibility markers in a sample of two hundred languages,
and of grammatical person with necessity constructions in Japanese and English corpora, are not
encoded.

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

/-- A meaning between which changes run. A modal meaning is the set of force-flavor pairs it
covers, as in `ModalItem.meaning`. -/
inductive Meaning where
  | modal (m : Finset ForceFlavor)
  /-- Future or prediction. -/
  | future
  | imperative
  | admonitive
  deriving DecidableEq

namespace Meaning

/-- The force-flavor pairs a meaning covers, none outside modality proper. -/
def forceFlavors : Meaning → Finset ForceFlavor
  | modal m => m
  | _ => ∅

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

/-- The meaning a label of the table stands for. -/
def Label.meaning : Label → Meaning
  | .futurePrediction => .future
  | .rootPossibility | .abilityRootPossibility => .modal {(.possibility, .circumstantial)}
  | .rootEpistemicPossibility =>
    .modal {(.possibility, .circumstantial), (.possibility, .epistemic)}
  | .permission => .modal {(.possibility, .deontic)}
  | .obligation => .modal {(.necessity, .deontic), (.weakNecessity, .deontic)}
  | .strongObligation => .modal {(.necessity, .deontic)}
  | .weakObligation => .modal {(.weakNecessity, .deontic)}
  | .epistemicPossibility => .modal {(.possibility, .epistemic)}
  | .probability => .modal {(.weakNecessity, .epistemic)}
  | .certainty => .modal {(.necessity, .epistemic)}
  | .imperative => .imperative
  | .admonitive => .admonitive

/-- Change within each side of volitivity and across the two sides in each direction is
attested. -/
theorem volitivity_independent :
    (∃ c ∈ changes, c.source.meaning.IsVolitive ∧ c.target.meaning.IsVolitive) ∧
    (∃ c ∈ changes, c.source.meaning.IsVolitive ∧ c.target.meaning.IsNonVolitive) ∧
    (∃ c ∈ changes, c.source.meaning.IsNonVolitive ∧ c.target.meaning.IsVolitive) ∧
    (∃ c ∈ changes, c.source.meaning.IsNonVolitive ∧ c.target.meaning.IsNonVolitive) := by
  decide

/-- A change from a non-volitive to a volitive meaning has more grams than any other change. -/
theorem grams_lt_of_toVolitive :
    ∀ c ∈ changes, ∀ d ∈ changes,
      c.source.meaning.IsNonVolitive → c.target.meaning.IsVolitive →
      ¬ (d.source.meaning.IsNonVolitive ∧ d.target.meaning.IsVolitive) → d.grams < c.grams := by
  decide

/-- No change leads out of mood. -/
theorem isMood_target_of_isMood_source :
    ∀ c ∈ changes, c.source.meaning.IsMood → c.target.meaning.IsMood := by
  decide

theorem isMood_of_both_volitivities :
    (∃ c ∈ changes, c.source.meaning.IsVolitive ∧ c.target.meaning.IsMood) ∧
    (∃ c ∈ changes, c.source.meaning.IsNonVolitive ∧ c.target.meaning.IsMood) := by
  decide

theorem sum_grams : (changes.map (·.grams)).sum = listedChanges := by decide

/-- Situational possibility is the source of twice as many changes as obligation: the grams whose
source covers circumstantial possibility and those whose source covers a deontic necessity sum to
the chapter's two totals. -/
theorem sum_grams_of_source :
    ((changes.filter fun c ↦
      (.possibility, .circumstantial) ∈ c.source.meaning.forceFlavors).map (·.grams)).sum =
        possibilitySourceChanges ∧
    ((changes.filter fun c ↦ ∃ ff ∈ c.source.meaning.forceFlavors,
      ff.force ≠ .possibility ∧ ff.flavor = .deontic).map (·.grams)).sum =
        obligationSourceChanges := by
  decide

end Narrog2010
