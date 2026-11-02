module

public import Linglib.Discourse.Accessibility
public import Linglib.Discourse.Centering.Basic
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Data.Examples.Ariel2001
public import Linglib.Data.Examples.Readers
public import Studies.GundelHedbergZacharski1993
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Ariel (2001): Accessibility theory: an overview

Referring expressions are accessibility markers: each class on the Accessibility Marking Scale
codes a degree of accessibility of the mental representation the addressee is to retrieve, from a
modified full name, coding the least, to a zero. A form codes less accessibility the more
informative, rigid and unattenuated it is, and these criteria jointly [order every pair they rank
as the scale does, except against a short definite description](##lt_of_criteria_lt);
[attenuation alone never runs against the scale](##attenuation_mono). The rival theories fall
short of it: the Givenness Hierarchy [gives four of its forms one
status](##givennessStatus_eq_activated), and Centering's Rule 1 [holds whenever every center is
lexical](##pronominalizationConstraint_of_lexical), so it does not predict the repeated-name
penalty, and [fails where the discourse topic is pronominal beside a lexical backward-looking
center](##not_pronominalizationConstraint_accused).

## Implementation notes

* `criteria` compares the substrate's `informativity`, `rigidity` and `attenuation` jointly, in
  the product order. The exceptions are [the partial names and the modified demonstrative
  phrases](##criteria_lt_and_shortDefDescription_lt_iff), which the criteria rank below a short
  definite description and the scale above it. The chapter grants that some aspects of the scale
  are grammatically stipulated and notes a conflict between demonstratives, which code the higher
  accessibility, and definite descriptions, which are the shorter; the partial names are
  exceptions only because `informativity` credits a name with as much lexical information as a
  description's noun, a comparison the chapter does not make.
* The criteria tie proximate and distal demonstratives, which the scale [ranks
  apart](##distal_lt_proximate) on distributional evidence.
* `givennessKind` sends a class of the scale to the kind of form Gundel et al. list in their
  Table 1; names, clitics and verbal agreement have none.
* Rows record their markers by the scale's labels as printed, read through `markerTable`.
* In (12) the roles follow Centering's ranking for English; the first clause's forms are as
  printed and the second's are those its row records.

## References

* [ariel-2001]
* [ariel-1990]
* [gundel-hedberg-zacharski-1993]
* [grosz-joshi-weinstein-1995]
-/

@[expose] public section

namespace Ariel2001

open Discourse AccessibilityLevel

/-! ### The criteria -/

/-- The criteria a form meets, ordered so that the lower of two forms is at least as informative,
as rigid and as unattenuated as the higher. -/
def criteria (l : AccessibilityLevel) : (Finset Information)ᵒᵈ × Rigidityᵒᵈ × Attenuation :=
  (OrderDual.toDual l.informativity, OrderDual.toDual l.rigidity, l.attenuation)

/-- The more informative, rigid and unattenuated a form, the lower the accessibility it codes:
where the criteria jointly rank one form below another, the scale does too, unless the higher is
a short definite description. -/
theorem lt_of_criteria_lt {a b : AccessibilityLevel} (h : criteria a < criteria b)
    (hb : b ≠ shortDefDescription) : a < b := by
  revert a b
  simp only [lt_iff_le_not_ge]
  decide

-- p. 54; n. 32
theorem criteria_lt_and_shortDefDescription_lt_iff (a : AccessibilityLevel) :
    criteria a < criteria shortDefDescription ∧ shortDefDescription < a ↔
      a ∈ [lastName, firstName, distalDemMod, proxDemMod] := by
  revert a
  simp only [lt_iff_le_not_ge]
  decide

/-- Attenuation alone never runs against the scale. -/
theorem attenuation_mono : Monotone attenuation := by
  unfold Monotone
  decide

theorem not_antitone_informativity : ¬ Antitone informativity :=
  fun h ↦ absurd (h (show lastName ≤ distalDemMod by decide)) (by decide)

theorem not_antitone_rigidity : ¬ Antitone rigidity :=
  fun h ↦ absurd (h (show shortDefDescription ≤ lastName by decide)) (by decide)

-- p. 51; Kirsner's Dutch demonstratives run the other way, p. 66
theorem distal_lt_proximate (a b : AccessibilityLevel) (h : criteria a = criteria b)
    (ha : a.deixis = some Person.first.participantSetsᶜ)
    (hb : b.deixis = some Person.first.participantSets) : a < b := by
  revert a b
  decide

/-! ### The rows -/

/-- The scale's labels as printed. -/
def markerTable : List (String × AccessibilityLevel) :=
  [("full name+modifier", fullNameMod), ("full name", fullName),
   ("long definite description", longDefDescription),
   ("short definite description", shortDefDescription), ("last name", lastName),
   ("first name", firstName), ("distal demonstrative+modifier", distalDemMod),
   ("proximate demonstrative+modifier", proxDemMod), ("distal demonstrative+NP", distalDemNP),
   ("proximate demonstrative+NP", proxDemNP), ("distal demonstrative (-NP)", distalDem),
   ("proximate demonstrative (-NP)", proxDem), ("stressed pronoun+gesture", stressedPronGesture),
   ("stressed pronoun", stressedPron), ("unstressed pronoun", unstressedPron),
   ("cliticized pronoun", cliticizedPron), ("verbal person inflections", verbalAgreement),
   ("zero", zero)]

/-- The marker a row records under `key`. -/
def marker (r : Datum) (key : String) : Option AccessibilityLevel := r.parse? key markerTable

/-- The markers a row lists, in order. -/
def markers (r : Datum) : List AccessibilityLevel :=
  (r.features "marker").filterMap (List.lookup · markerTable)

/-- A row codes the referent under `hi` by a higher accessibility marker than the one under
`lo`. -/
def Outmarks (r : Datum) (hi lo : String) : Prop := ∃ h ∈ marker r hi, ∃ l ∈ marker r lo, l < h

instance (r : Datum) (hi lo : String) : Decidable (Outmarks r hi lo) :=
  inferInstanceAs (Decidable (∃ h ∈ marker r hi, ∃ l ∈ marker r lo, l < h))

-- p. 34
theorem maya_outmarks_rachel : Outmarks Examples.maya_rachel "maya" "rachel" := by
  decide +kernel

-- (3), (4)
theorem perspective_outmarks :
    ∀ r ∈ [Examples.ex_3, Examples.ex_4], ∃ p ∈ r.feature? "perspective",
      ∀ o ∈ ["victim", "rapists"], o ≠ p → Outmarks r p o := by
  decide +kernel

-- (8)
theorem headline_outmarks :
    (∀ p ∈ (markers Examples.ex_8a).zip (markers Examples.ex_8b), p.2 < p.1) ∧
      (markers Examples.ex_8a).length = 4 ∧ (markers Examples.ex_8b).length = 4 := by
  decide +kernel

/-! ### Competing theories -/

section Givenness

open GundelHedbergZacharski1993

/-- The kind of form in Table 1 of [gundel-hedberg-zacharski-1993] that a class of the scale is,
where they list one. -/
def givennessKind : AccessibilityLevel → Option Form.Kind
  | zero => some .zero
  | unstressedPron => some .pronoun
  | stressedPronGesture | stressedPron => some .stressedPronoun
  | proxDem => some (.demonstrative .proximal)
  | distalDem => some (.demonstrative .distal)
  | proxDemMod | proxDemNP => some (.demonstrativeN .proximal)
  | distalDemMod | distalDemNP => some (.demonstrativeN .distal)
  | longDefDescription | shortDefDescription => some .definiteN
  | _ => none

/-- The status Gundel et al. code an English form of the scale for. -/
def givennessStatus (l : AccessibilityLevel) : Option GivennessStatus :=
  (givennessKind l).bind (required .english)

/-- The Givenness Hierarchy codes *this N*, *that*, *this* and stressed *IT* for one status,
activated, though the scale ranks them apart. -/
theorem givennessStatus_eq_activated :
    [proxDemNP, distalDem, proxDem, stressedPron].Pairwise (· < ·) ∧
      ∀ l ∈ [proxDemNP, distalDem, proxDem, stressedPron], givennessStatus l = some .activated := by
  decide

-- p. 64
theorem uniquelyIdentifiable_le_of_givennessStatus (s : GivennessStatus)
    (h : ∀ r ∈ givennessStatus unstressedPron, r ≤ s) : .uniquelyIdentifiable ≤ s :=
  le_trans (by decide) (h .inFocus rfl)

-- p. 64
theorem required_zero_eq_pronoun :
    ∀ l : Language, ∀ s ∈ required l .zero, ∀ s' ∈ required l .pronoun, s = s' := by
  decide

end Givenness

open Centering

/-- Rule 1 holds of an utterance whose centers are all lexical, whichever non-lexical forms count
as pronouns, so it does not rule out a repeated name. -/
theorem pronominalizationConstraint_of_lexical {E R : Type*} [DecidableEq E] [LinearOrder R]
    {P : Set AccessibilityLevel} (hP : ∀ l ∈ P, ¬ l.lexical)
    (prev cur : Utterance E R AccessibilityLevel) (h : ∀ r ∈ cur.realizations, r.form.lexical) :
    PronominalizationConstraint P prev cur :=
  pronominalizationConstraint_of_forall_not fun _ ⟨r, hr, _, hp⟩ ↦ hP _ hp (h r hr)

/-- The referents of (12): officer Feil, the discourse topic, and the officer in charge of him. -/
inductive Referent
  | feil
  | officer
  deriving DecidableEq, Repr

/-- *the officer in charge of him demanded from him to have a haircut* -/
def demanded : Utterance Referent GrammaticalRole AccessibilityLevel :=
  ⟨[⟨.officer, .subject, longDefDescription⟩, ⟨.feil, .other, unstressedPron⟩]⟩

/-- *The officer accused him*, with the markers a row records for the subject and the topic. -/
def accused (r : Datum) : Option (Utterance Referent GrammaticalRole AccessibilityLevel) := do
  pure ⟨[⟨.officer, .subject, ← marker r "subjectMarker"⟩,
    ⟨.feil, .object, ← marker r "topicMarker"⟩]⟩

/-- In (12) the officer, subject of two consecutive clauses, is the backward-looking center of the
second, yet only the discourse topic is pronominal there: Rule 1 fails for any R1-pronouns that
include the pronouns and exclude the lexical forms. -/
theorem not_pronominalizationConstraint_accused {P : Set AccessibilityLevel}
    (hpron : ∀ l, l.head = .pronoun → l ∈ P) (hlex : ∀ l ∈ P, ¬ l.lexical) :
    ∃ u ∈ accused Examples.ex_12, cb demanded u = some .officer ∧
      ¬ PronominalizationConstraint P demanded u := by
  refine ⟨⟨[⟨.officer, .subject, shortDefDescription⟩, ⟨.feil, .object, unstressedPron⟩]⟩,
    by decide +kernel, by decide, fun h ↦ ?_⟩
  obtain ⟨r, hr, he, hP⟩ := h ⟨.feil, by decide, _, .tail _ (.head _), rfl, hpron _ rfl⟩ .officer
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hlex _ hP trivial
  · cases he

end Ariel2001
