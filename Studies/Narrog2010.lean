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

We define the points of the map (`Point`): a force-flavor pair, the future, or one of two
directive moods. A point has a side of volitivity (`Point.IsVolitive`), which for a force-flavor
pair is that of its flavor (`Modality.ModalFlavor.IsVolitive`), and lies in modality proper or in
mood (`Point.IsMood`). A meaning is a finite set of points, and `Label.meaning` gives the meaning
of each label of the chapter's table of the eight most frequent changes in the sample of
[bybee-perkins-pagliuca-1994], `Narrog2010.changes`. On the table, change is attested from each
side of volitivity to each side (`volitivity_independent`), each change from a non-volitive to a
volitive meaning has more grams than any other change (`grams_lt_of_toVolitive`), and no change
leads out of mood (`isMood_target_of_isMood_source`). The grams of the table sum to the totals
the chapter gives for all changes, for changes out of situational possibility and for changes
out of obligation (`sum_grams`, `sum_grams_of_source`).

## Implementation notes

A meaning is a set of points and not a point, so that a label covering two flavors, or a gram
with a modal and a mood use, is one meaning; a property of a meaning is then a statement about
all its points. The chapter argues that the five tabulated changes within modality proper also
increase speaker orientation, the deontic-to-epistemic ones included, but it assigns no positions
to their meanings, and orientation is a property of a use and not of a meaning label, so no
orientation is assigned to a point here. The scale itself is `Narrog2012.SpeechActOrientation`,
in the later book's terms, and that study checks these changes against it.

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

/-- A point of the map. -/
inductive Point where
  | modal (ff : ForceFlavor)
  /-- Future or prediction. -/
  | future
  | imperative
  | admonitive
  deriving DecidableEq

namespace Point

/-- A force-flavor pair is volitive when its flavor is, the directive moods are, and the future
is not. -/
def IsVolitive : Point → Prop
  | modal ff => ff.flavor.IsVolitive
  | future => False
  | imperative | admonitive => True

/-- The imperative and the admonitive mark speech acts and belong to mood, which lies at the
speech act-oriented end of the map; the other points belong to modality proper. -/
def IsMood : Point → Prop
  | imperative | admonitive => True
  | _ => False

instance : DecidablePred IsVolitive := fun p ↦ by cases p <;> unfold IsVolitive <;> infer_instance
instance : DecidablePred IsMood := fun p ↦ by cases p <;> unfold IsMood <;> infer_instance

end Point

/-- The meaning a label of the table stands for, as the points it covers. -/
def Label.meaning : Label → Finset Point
  | .futurePrediction => {.future}
  | .rootPossibility | .abilityRootPossibility => {.modal (.possibility, .circumstantial)}
  | .rootEpistemicPossibility =>
    {.modal (.possibility, .circumstantial), .modal (.possibility, .epistemic)}
  | .permission => {.modal (.possibility, .deontic)}
  | .obligation => {.modal (.necessity, .deontic), .modal (.weakNecessity, .deontic)}
  | .strongObligation => {.modal (.necessity, .deontic)}
  | .weakObligation => {.modal (.weakNecessity, .deontic)}
  | .epistemicPossibility => {.modal (.possibility, .epistemic)}
  | .probability => {.modal (.weakNecessity, .epistemic)}
  | .certainty => {.modal (.necessity, .epistemic)}
  | .imperative => {.imperative}
  | .admonitive => {.admonitive}

/-- Change from each side of volitivity to each side is attested: for any two sides `v` and `w`,
some change has all its source on side `v` and all its target on side `w`. -/
theorem volitivity_independent (v w : Prop) :
    ∃ c ∈ changes, (∀ p ∈ c.source.meaning, p.IsVolitive ↔ v) ∧
      ∀ p ∈ c.target.meaning, p.IsVolitive ↔ w := by
  by_cases hv : v <;> by_cases hw : w <;> simp only [hv, hw, iff_true, iff_false] <;> decide

/-- A change from a non-volitive to a volitive meaning has more grams than any other change. -/
theorem grams_lt_of_toVolitive :
    ∀ c ∈ changes, ∀ d ∈ changes,
      (∀ p ∈ c.source.meaning, ¬ p.IsVolitive) → (∀ p ∈ c.target.meaning, p.IsVolitive) →
      ¬ ((∀ p ∈ d.source.meaning, ¬ p.IsVolitive) ∧ ∀ p ∈ d.target.meaning, p.IsVolitive) →
      d.grams < c.grams := by
  decide

/-- No change leads out of mood. -/
theorem isMood_target_of_isMood_source :
    ∀ c ∈ changes, (∀ p ∈ c.source.meaning, p.IsMood) → ∀ p ∈ c.target.meaning, p.IsMood := by
  decide

-- Changes #1, #3 and #4 lead into mood, from both sides of volitivity.
theorem isMood_of_both_volitivities (v : Prop) :
    ∃ c ∈ changes, (∀ p ∈ c.source.meaning, p.IsVolitive ↔ v) ∧
      ∀ p ∈ c.target.meaning, p.IsMood := by
  by_cases hv : v <;> simp only [hv, iff_true, iff_false] <;> decide

theorem sum_grams : (changes.map (·.grams)).sum = listedChanges := by decide

/-- Situational possibility is the source of twice as many changes as obligation: the grams whose
source covers circumstantial possibility and those whose source covers a deontic necessity sum to
the chapter's two totals. -/
theorem sum_grams_of_source :
    ((changes.filter fun c ↦
      .modal (.possibility, .circumstantial) ∈ c.source.meaning).map (·.grams)).sum =
        possibilitySourceChanges ∧
    ((changes.filter fun c ↦ .modal (.necessity, .deontic) ∈ c.source.meaning ∨
      .modal (.weakNecessity, .deontic) ∈ c.source.meaning).map (·.grams)).sum =
        obligationSourceChanges := by
  decide

end Narrog2010
