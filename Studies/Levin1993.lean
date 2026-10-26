module

public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Adpositions
public import Linglib.Data.Examples.Levin1993

/-!
# Levin (1993): English Verb Classes and Alternations

This file formalizes Levin's diagnostic: a verb's participation in diathesis
alternations follows from its meaning, so verbs fall into semantically coherent classes that
share an alternation profile (`ArgumentStructure.LevinClass.Participates`). The book's
opening quadruple *break*, *cut*, *hit*, *touch* takes four distinct profiles across the
causative/inchoative, middle, conative, and body-part possessor ascension alternations, one
class each (`quadruple_profiles_distinct`). The Introduction explains the profiles by four
components of verb meaning, "motion, contact, change of state, and causation"
(`MeaningComponent`), to which each of the four alternations is sensitive (`sensitivity`): the
body-part possessor ascension alternation needs contact and the conative contact and motion, the
middle causation of a change of state, and the causative/inchoative a pure change of state, one
whose meaning does not specify how the change comes about. Only the last condition is lost when a
meaning involves more components (`isUpperSet_sensitivity`,
`not_isUpperSet_sensitivity_causativeInchoative`), and the components of the Introduction's
characterizations of the four verbs meet the conditions exactly where the class pages of Part II
attest the alternations (`quadruple_mem_sensitivity_of_participates`,
`quadruple_prediction_matches`). Every
categorical alternation judgment among the book's examples in `Data/Examples/Levin1993.json`
agrees with the profile of the verb's class (`participation_matches_profile`). The
alternations that pair two argument frames are frame-pair schemas (`schema?`), which relate two
diatheses of a verb when the verb's participants move as the schema says; the induced action
alternation differs from the causative/inchoative one in the directional phrase of its transitive
and in its volitional causee (`Shows`, `run_shatter`), and every English fragment verb Levin lists
has a class whose page it realizes (`shows_class_alternations`).

## Implementation notes

Rows record the verb's class by the book's section number and the alternation by name;
`classOf` and `alternationOf` read them into the substrate's enumerations. A row's
participation in its alternation is its judgment: an acceptable row attests the alternation, a
starred row denies it, and a marginal row is categorical in neither direction.

The Introduction's conditions are necessary ones: a verb shows the body-part possessor ascension
alternation "only if its meaning involves the notion of contact" (p. 8), and the
causative/inchoative "is found only with verbs of pure change of state" (p. 10). Each is an
interval of sets of components, and an alternation for which the Introduction states no
condition has the whole lattice. A pure change of state may carry a cause, as *break* does "when
transitive" (p. 9), so the causative/inchoative's interval runs from the change of state to the
change of state with its cause.

A causee's entailments are the entry's own, or else a change of state where Levin classes the verb
with her verbs of change of state, the classes of chapter 45 (`causeeProfile?`); the verbs of change
of position the causative/inchoative also covers are not mapped. Where neither is recorded the
causee meets no condition, so a verb shows the causative/inchoative or the induced action
alternation only where Levin's condition is verified.

## Errata

* Part One lists the verbs of modes of being involving motion among those showing the *swarm*
  alternation (p. 54), and their class page stars the locative alternation with *The fort
  fluttered with many flags* (p. 251). `LevinClass.Participates` reads the class pages.

## References

* [levin-1993]
-/

@[expose] public section

namespace Levin1993

open ArgumentStructure

/-- The alternation named by a row's tag. -/
def alternationOfString : String → Option DiathesisAlternation
  | "causativeInchoative" => some .causativeInchoative
  | "inducedAction" => some .inducedAction
  | "middle" => some .middle
  | "conative" => some .conative
  | "substanceSource" => some .substanceSource
  | "unspecifiedObject" => some .unspecifiedObject
  | "understoodBodyPartObject" => some .understoodBodyPartObject
  | "understoodReflexiveObject" => some .understoodReflexiveObject
  | "understoodReciprocalObject" => some .understoodReciprocalObject
  | "dative" => some .dative
  | "benefactive" => some .benefactive
  | "locative" => some .locative
  | "bodyPartPossessorAscension" => some .bodyPartPossessorAscension
  | "swarm" => some .swarm
  | "materialProduct" => some .materialProduct
  | "totalTransformation" => some .totalTransformation
  | "instrumentSubject" => some .instrumentSubject
  | "verbalPassive" => some .verbalPassive
  | "prepositionalPassive" => some .prepositionalPassive
  | "thereInsertion" => some .thereInsertion
  | "locativeInversion" => some .locativeInversion
  | "cognateObject" => some .cognateObject
  | "wayConstruction" => some .wayConstruction
  | "resultative" => some .resultative
  | "directionalPhrase" => some .directionalPhrase
  | _ => none

/-- The class recorded on a row, by the book's section number. -/
def classOf (e : Datum) : Option LevinClass :=
  (e.feature? "levin_class").bind LevinClass.ofNumberString?

/-- The alternation recorded on a row. -/
def alternationOf (e : Datum) : Option DiathesisAlternation :=
  (e.feature? "alternation").bind alternationOfString

theorem participation_matches_profile :
    ∀ e ∈ Examples.all, ∀ c ∈ classOf e, ∀ a ∈ alternationOf e, e.judgment ≠ .marginal →
      c.Tests a → (c.Participates a ↔ e.judgment = .acceptable) := by
  decide +kernel

/-! ### The Introduction's quadruple

*break*, *cut*, *hit* and *touch* are told apart by the four diagnostic alternations (p. 7), and
the Introduction explains the difference by the components of their meanings (pp. 7–10). -/

/-- A component of verb meaning to which diathesis alternations are sensitive, among "the notions
of motion, contact, change of state, and causation" (p. 10). -/
inductive MeaningComponent where
  | motion
  | contact
  | changeOfState
  | causation
  deriving DecidableEq, Fintype, Repr

open MeaningComponent

/-- The sets of meaning components of the verbs that can show an alternation (p. 10):
body-part possessor ascension "is sensitive to the notion of contact", the conative "to both
contact and motion", the middle "is found with verbs whose meaning involves causing a change of
state", and the causative/inchoative "is found only with verbs of pure change of state". -/
def sensitivity : DiathesisAlternation → NonemptyInterval (Finset MeaningComponent)
  | .bodyPartPossessorAscension => ⟨({contact}, ⊤), le_top⟩
  | .conative => ⟨({contact, motion}, ⊤), le_top⟩
  | .middle => ⟨({changeOfState, causation}, ⊤), le_top⟩
  | .causativeInchoative => ⟨({changeOfState}, {changeOfState, causation}), by decide⟩
  | _ => ⊤

/-- Every alternation but the causative/inchoative is upward closed in meaning components (p. 10).
-/
theorem isUpperSet_sensitivity {a : DiathesisAlternation} (ha : a ≠ .causativeInchoative) :
    IsUpperSet (sensitivity a : Set (Finset MeaningComponent)) := by
  have : (sensitivity a).snd = ⊤ := by cases a <;> first | exact absurd rfl ha | rfl
  rw [NonemptyInterval.coe_def, this, Set.Icc_top]
  exact isUpperSet_Ici _

/-- The causative/inchoative is not open to a verb that adds a means, such as contact, to a pure
change of state (pp. 9–10). -/
theorem not_isUpperSet_sensitivity_causativeInchoative :
    ¬ IsUpperSet (sensitivity .causativeInchoative : Set (Finset MeaningComponent)) := fun h ↦
  absurd (SetLike.mem_coe.1 <| h (a := {changeOfState}) (b := {changeOfState, contact})
    (by decide) (SetLike.mem_coe.2 (by decide))) (by decide)

/-- The four diagnostic alternations of the Introduction. -/
def diagnosticAlternations : List DiathesisAlternation :=
  [.causativeInchoative, .middle, .conative, .bodyPartPossessorAscension]

theorem quadruple_profiles_distinct :
    ([LevinClass.break_, .cut, .hit, .touch].map fun c ↦
      diagnosticAlternations.map fun a ↦ decide (c.Participates a)).Pairwise (· ≠ ·) := by
  decide +kernel

/-- The quadruple's classes with the meaning components of the Introduction's
characterizations (p. 10): "*touch* is a pure verb of contact, *hit* is a verb of contact by
motion, *cut* is a verb of causing a change of state by moving something into contact with the
entity that changes state, and *break* is a pure verb of change of state", with the notion of cause
it has "when transitive" (p. 9), since *cut* and *break* are "both verbs of causing a change of
state" (p. 9). -/
def quadruple : List (LevinClass × Finset MeaningComponent) :=
  [(.break_, {changeOfState, causation}), (.cut, {changeOfState, causation, contact, motion}),
    (.hit, {contact, motion}), (.touch, {contact})]

theorem quadruple_mem_sensitivity_of_participates :
    ∀ p ∈ quadruple, ∀ a : DiathesisAlternation, p.1.Participates a → p.2 ∈ sensitivity a := by
  decide +kernel

theorem quadruple_prediction_matches :
    ∀ p ∈ quadruple, ∀ a ∈ diagnosticAlternations, (p.2 ∈ sensitivity a ↔ p.1.Participates a) := by
  decide +kernel

/-! ### Frame-pair schemas of the alternations

The alternations of Part One as voices, pairs of English argument frames with the slots each
participant occupies in them, the preposition fixed where the alternation's definition fixes it:
*to* for the dative, *for* for the benefactive, *at* for the conative, *with* for the *with* variant
of the locative and swarm alternations and for the instrument, *from* for the substance/source
alternation, *out of* and *into* for the material/product and total transformation alternations,
*on* for body-part possessor ascension. The locative variants of the locative and swarm alternations
fix only that the phrase is spatial. The middle, the passives, the postverbal-subject alternations
and the constructions of chapter 7 are not pairs of frames and have no schema. -/

open Voice English.Adpositions ArgumentFrame.Slot in
/-- The frame-pair schema of an alternation, where it has one. -/
def schema? : DiathesisAlternation → Option Voice
  | .causativeInchoative => some anticausative
  | .inducedAction =>
    some (of .spatialPP .np_spatialPP [some (complement 0), some (complement 1), some external])
  | .conative => some (of .np (.pp (some at_)) [some external, some (complement 0)])
  | .substanceSource =>
    some (of (.pp (some from_) (some .abl)) .np [some (complement 0), some external])
  | .unspecifiedObject => some (leaveImplicit .np 0 (some .indef))
  | .understoodBodyPartObject => some (leaveImplicit .np 0 (some .bodyPart))
  | .understoodReflexiveObject => some reflexive
  | .understoodReciprocalObject => some reciprocal
  | .dative => some (toDoubleObject (.np_pp (some to_) (some .dat)))
  | .benefactive => some (toDoubleObject (.np_pp (some for_) (some .ben)))
  | .locative => some <|
      of .np_spatialPP (.np_pp (some with_))
        [some external, some (complement 1), some (complement 0)]
  | .bodyPartPossessorAscension => some <|
      of .np (.np_pp (some on) (some .sup))
        [some external, some (complement 1), some (complement 0)]
  | .swarm => some (of .spatialPP (.pp (some with_)) [some (complement 0), some external])
  | .materialProduct => some <|
      of (.np_pp (some out)) (.np_pp (some into) (some .transl))
        [some external, some (complement 1), some (complement 0)]
  | .totalTransformation => some <|
      of (.np_pp (some into) (some .transl))
        ⟨some .nominal,
          [.nominal, .adposition (some from_), .adposition (some into) (some .transl)]⟩
        [some external, some (complement 0), some (complement 2), some (complement 1)]
  | .instrumentSubject => some
      (of (.np_pp (some with_) (some .inst)) .np [none, some (complement 0), some external])
  | _ => none
where
  /-- The dative and benefactive alternations, in which the phrase of `fr` becomes the first
  object. -/
  toDoubleObject (fr : ArgumentFrame) : Voice :=
    of fr .np_np [some external, some (complement 1), some (complement 0)]

/-! ### The causee

The causative/inchoative and induced action alternations both relate a transitive whose object is
the subject of an intransitive. In the induced action alternation the transitive "must be
accompanied by a directional phrase" (p. 31), and Levin also tells the two apart by that
participant, the causee: the induced action alternation "differs from the causative/inchoative
alternation in that the causee is typically an animate volitional entity" (p. 31), and the verbs of
the causative/inchoative alternation are "verbs of change of state or change of position"
(p. 30). -/

/-- A causee of two diatheses is a participant that is the object of one and the subject without
an object of the other. -/
def IsCausee {n : ℕ} (c d : Diathesis n) (i : Fin n) : Prop :=
  c.participantRole i = some .P ∧ d.participantRole i = some .S ∨
    c.participantRole i = some .S ∧ d.participantRole i = some .P

instance {n : ℕ} (c d : Diathesis n) (i : Fin n) : Decidable (IsCausee c d i) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Levin's condition on the causee's entailments asks for a volitional causee in the induced action
alternation, and in the causative/inchoative alternation for one that is not volitional and changes
state or position. -/
def CauseeCondition : DiathesisAlternation → EntailmentProfile → Prop
  | .causativeInchoative, θ => .volition ∉ θ ∧ (.changeOfState ∈ θ ∨ .movement ∈ θ)
  | .inducedAction, θ => .volition ∈ θ
  | _, _ => True

instance (a : DiathesisAlternation) (θ : EntailmentProfile) : Decidable (CauseeCondition a θ) := by
  cases a <;> unfold CauseeCondition <;> infer_instance

/-- The classes of chapter 45, the verbs of change of state. -/
def changeOfStateClasses : Finset LevinClass :=
  {.break_, .bend, .cooking, .otherChangeOfState, .entitySpecificChangeOfState,
    .calibratableChangeOfState}

theorem mem_changeOfStateClasses_iff (c : LevinClass) :
    c ∈ changeOfStateClasses ↔ "45.".toList <+: c.numberString.toList := by
  revert c
  decide +kernel

/-- The entailments of a causee, the entry's own or else a change of state when Levin classes the
verb with the verbs of change of state. -/
def causeeProfile? (v : Verb) (i : Fin v.valency.arity) : Option EntailmentProfile :=
  v.valency.profiles.get i <|>
    if Disjoint v.levinClasses changeOfStateClasses then none else some {.changeOfState}

/-- A verb shows an alternation when the alternation's schema relates two of its diatheses and the
profile of each causee meets the alternation's condition. -/
def Shows (v : Verb) (a : DiathesisAlternation) : Prop :=
  ∃ σ ∈ schema? a, ∃ c ∈ v.valency.diatheses, ∃ d ∈ v.valency.diatheses, σ.Relates c d ∧
    ∀ i, IsCausee c d i → ∃ θ ∈ causeeProfile? v i, CauseeCondition a θ

instance (v : Verb) (a : DiathesisAlternation) : Decidable (Shows v a) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, ∃ _ ∈ _, _ ∧ ∀ _, _ → _))

/-- The alternations with a frame-pair schema. -/
def schematized : List DiathesisAlternation :=
  [.causativeInchoative, .inducedAction, .conative, .substanceSource, .unspecifiedObject,
    .understoodBodyPartObject, .understoodReflexiveObject, .understoodReciprocalObject, .dative,
    .benefactive, .locative, .bodyPartPossessorAscension, .swarm, .materialProduct,
    .totalTransformation, .instrumentSubject]

theorem isSome_schema?_iff (a : DiathesisAlternation) : (schema? a).isSome ↔ a ∈ schematized := by
  cases a <;> decide

theorem shows_class_alternations :
    ∀ v ∈ English.Verbs.verbs, v.levinClasses.Nonempty → ∃ c ∈ v.levinClasses,
      ∀ a ∈ schematized, ∀ p ∈ c.properties, p.heading = .alternation a.number →
        (p.diacritic = .none → p.scope = .all → Shows v.toVerb a) ∧
          (p.diacritic = .star → ¬ Shows v.toVerb a) := by
  decide +kernel

open English.Verbs in
theorem run_shatter :
    (Shows run.toVerb .inducedAction ∧ ¬ Shows run.toVerb .causativeInchoative) ∧
      Shows shatter.toVerb .causativeInchoative ∧ ¬ Shows shatter.toVerb .inducedAction := by
  decide

end Levin1993
