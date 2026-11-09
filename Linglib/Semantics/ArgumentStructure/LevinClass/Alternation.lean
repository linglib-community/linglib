module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Diathesis alternations

The alternations and constructions of [levin-1993] Part One, one constructor per numbered
section, with the section number (`DiathesisAlternation.number`) and Levin's title
(`DiathesisAlternation.name`); a section that groups subsections, such as the causative
alternations or the locative alternation, is a constructor too, since the class pages of
Part II name it. The chapter of Part One that presents an alternation is its family
(`DiathesisAlternation.family`).

## References

* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure

/-- The chapter of [levin-1993] Part One that presents an alternation. -/
inductive AlternationFamily where
  /-- Chapter 1, transitivity alternations. -/
  | transitivity
  /-- Chapter 2, alternations involving arguments within the VP. -/
  | vpInternal
  /-- Chapter 3, oblique subject alternations. -/
  | obliqueSubject
  /-- Chapter 4, reflexive diathesis alternations. -/
  | reflexive
  /-- Chapter 5, passive. -/
  | passive
  /-- Chapter 6, alternations involving postverbal subjects. -/
  | postverbalSubject
  /-- Chapter 7, other constructions. -/
  | otherConstructions
  /-- Chapter 8, verbs requiring special diatheses. -/
  | specialDiathesis
  deriving DecidableEq, Repr

/-- The numbered sections of [levin-1993] Part One. -/
inductive DiathesisAlternation where
  /-- §1.1, Object of Transitive = Subject of Intransitive Alternations. -/
  | objectOfTransitiveSubjectOfIntransitive
  /-- §1.1.1, Middle Alternation. -/
  | middle
  /-- §1.1.2, Causative Alternations. -/
  | causative
  /-- §1.1.2.1, Causative/Inchoative Alternation. -/
  | causativeInchoative
  /-- §1.1.2.2, Induced Action Alternation. -/
  | inducedAction
  /-- §1.1.2.3, Other Instances of Causative Alternations. -/
  | otherCausative
  /-- §1.1.3, Substance/Source Alternation. -/
  | substanceSource
  /-- §1.2, Unexpressed Object Alternations. -/
  | unexpressedObject
  /-- §1.2.1, Unspecified Object Alternation. -/
  | unspecifiedObject
  /-- §1.2.2, Understood Body-Part Object Alternation. -/
  | understoodBodyPartObject
  /-- §1.2.3, Understood Reflexive Object Alternation. -/
  | understoodReflexiveObject
  /-- §1.2.4, Understood Reciprocal Object Alternation. -/
  | understoodReciprocalObject
  /-- §1.2.5, PRO-arb Object Alternation. -/
  | proArbObject
  /-- §1.2.6, Characteristic Property Alternations. -/
  | characteristicProperty
  /-- §1.2.6.1, Characteristic Property of Agent Alternation. -/
  | characteristicPropertyOfAgent
  /-- §1.2.6.2, Characteristic Property of Instrument Alternation. -/
  | characteristicPropertyOfInstrument
  /-- §1.2.7, Way Object Alternation. -/
  | wayObject
  /-- §1.2.8, Instructional Imperative. -/
  | instructionalImperative
  /-- §1.3, Conative Alternation. -/
  | conative
  /-- §1.4, Preposition Drop Alternations. -/
  | prepositionDrop
  /-- §1.4.1, Locative Preposition Drop Alternation. -/
  | locativePrepositionDrop
  /-- §1.4.2, With Preposition Drop Alternation. -/
  | withPrepositionDrop
  /-- §2.1, Dative Alternation. -/
  | dative
  /-- §2.2, Benefactive Alternation. -/
  | benefactive
  /-- §2.3, Locative Alternation. -/
  | locative
  /-- §2.3.1, Spray/Load Alternation. -/
  | sprayLoad
  /-- §2.3.2, Clear Alternation (transitive). -/
  | clearTransitive
  /-- §2.3.3, Wipe Alternation. -/
  | wipe
  /-- §2.3.4, Swarm Alternation. -/
  | swarm
  /-- §2.3.5, Clear Alternation (intransitive). -/
  | clearIntransitive
  /-- §2.4, Creation and Transformation Alternations. -/
  | creationAndTransformation
  /-- §2.4.1, Material/Product Alternation (transitive). -/
  | materialProduct
  /-- §2.4.2, Material/Product Alternation (intransitive). -/
  | materialProductIntransitive
  /-- §2.4.3, Total Transformation Alternation (transitive). -/
  | totalTransformation
  /-- §2.4.4, Total Transformation Alternation (intransitive). -/
  | totalTransformationIntransitive
  /-- §2.5, Reciprocal Alternations. -/
  | reciprocal
  /-- §2.5.1, Simple Reciprocal Alternation (transitive). -/
  | simpleReciprocal
  /-- §2.5.2, Together Reciprocal Alternation (transitive). -/
  | togetherReciprocal
  /-- §2.5.3, Apart Reciprocal Alternation (transitive). -/
  | apartReciprocal
  /-- §2.5.4, Simple Reciprocal Alternation (intransitive). -/
  | simpleReciprocalIntransitive
  /-- §2.5.5, Together Reciprocal Alternation (intransitive). -/
  | togetherReciprocalIntransitive
  /-- §2.5.6, Apart Reciprocal Alternation (intransitive). -/
  | apartReciprocalIntransitive
  /-- §2.6, Fulfilling Alternation. -/
  | fulfilling
  /-- §2.7, Image Impression Alternation. -/
  | imageImpression
  /-- §2.8, With/Against Alternation. -/
  | withAgainst
  /-- §2.9, Through/With Alternation. -/
  | throughWith
  /-- §2.10, Blame Alternation. -/
  | blame
  /-- §2.11, Search Alternations. -/
  | search
  /-- §2.12, Body-Part Possessor Ascension Alternation. -/
  | bodyPartPossessorAscension
  /-- §2.13, Possessor-Attribute Factoring Alternations. -/
  | possessorAttributeFactoring
  /-- §2.13.1, Possessor Object. -/
  | possessorObject
  /-- §2.13.2, Attribute Object. -/
  | attributeObject
  /-- §2.13.3, Possessor and Attribute Alternation. -/
  | possessorAndAttribute
  /-- §2.13.4, Possessor Subject (transitive). -/
  | possessorSubject
  /-- §2.13.5, Possessor Subject (intransitive). -/
  | possessorSubjectIntransitive
  /-- §2.14, As Alternation. -/
  | as
  /-- §3.1, Time Subject Alternation. -/
  | timeSubject
  /-- §3.2, Natural Force Subject Alternation. -/
  | naturalForceSubject
  /-- §3.3, Instrument Subject Alternation. -/
  | instrumentSubject
  /-- §3.4, Abstract Cause Subject Alternation. -/
  | abstractCauseSubject
  /-- §3.5, Locatum Subject Alternation. -/
  | locatumSubject
  /-- §3.6, Location Subject Alternation. -/
  | locationSubject
  /-- §3.7, Container Subject Alternation. -/
  | containerSubject
  /-- §3.8, Raw Material Subject Alternation. -/
  | rawMaterialSubject
  /-- §3.9, Sum of Money Subject Alternation. -/
  | sumOfMoneySubject
  /-- §3.10, Source Subject Alternation. -/
  | sourceSubject
  /-- §4.1, Virtual Reflexive Alternation. -/
  | virtualReflexive
  /-- §4.2, Reflexive of Appearance Alternation. -/
  | reflexiveOfAppearance
  /-- §5.1, Verbal Passive. -/
  | verbalPassive
  /-- §5.2, Prepositional Passive. -/
  | prepositionalPassive
  /-- §5.3, Adjectival Passive (transitive verbs). -/
  | adjectivalPassive
  /-- §5.4, Adjectival Perfect Participles (intransitive verbs). -/
  | adjectivalPerfectParticiple
  /-- §6.1, There-Insertion. -/
  | thereInsertion
  /-- §6.2, Locative Inversion. -/
  | locativeInversion
  /-- §7.1, Cognate Object Construction. -/
  | cognateObject
  /-- §7.2, Cognate Prepositional Phrase Construction. -/
  | cognatePrepositionalPhrase
  /-- §7.3, Reaction Object Construction. -/
  | reactionObject
  /-- §7.4, X’s Way Construction. -/
  | wayConstruction
  /-- §7.5, Resultative Construction. -/
  | resultative
  /-- §7.6, Unintentional Interpretation of Object. -/
  | unintentionalInterpretation
  /-- §7.6.1, Unintentional Interpretation with Reflexive Object. -/
  | unintentionalInterpretationReflexive
  /-- §7.6.2, Unintentional Interpretation with Body-Part Object. -/
  | unintentionalInterpretationBodyPart
  /-- §7.7, Bound Nonreflexive Anaphor as Prepositional Object. -/
  | boundNonreflexiveAnaphor
  /-- §7.8, Directional Phrases with Nondirected Motion Verbs. -/
  | directionalPhrase
  /-- §8.1, Obligatory Passive. -/
  | obligatoryPassive
  deriving DecidableEq, Repr, Fintype

namespace DiathesisAlternation

/-- The section number in Part One. -/
def number : DiathesisAlternation → List ℕ
  | .objectOfTransitiveSubjectOfIntransitive => [1, 1]
  | .middle => [1, 1, 1]
  | .causative => [1, 1, 2]
  | .causativeInchoative => [1, 1, 2, 1]
  | .inducedAction => [1, 1, 2, 2]
  | .otherCausative => [1, 1, 2, 3]
  | .substanceSource => [1, 1, 3]
  | .unexpressedObject => [1, 2]
  | .unspecifiedObject => [1, 2, 1]
  | .understoodBodyPartObject => [1, 2, 2]
  | .understoodReflexiveObject => [1, 2, 3]
  | .understoodReciprocalObject => [1, 2, 4]
  | .proArbObject => [1, 2, 5]
  | .characteristicProperty => [1, 2, 6]
  | .characteristicPropertyOfAgent => [1, 2, 6, 1]
  | .characteristicPropertyOfInstrument => [1, 2, 6, 2]
  | .wayObject => [1, 2, 7]
  | .instructionalImperative => [1, 2, 8]
  | .conative => [1, 3]
  | .prepositionDrop => [1, 4]
  | .locativePrepositionDrop => [1, 4, 1]
  | .withPrepositionDrop => [1, 4, 2]
  | .dative => [2, 1]
  | .benefactive => [2, 2]
  | .locative => [2, 3]
  | .sprayLoad => [2, 3, 1]
  | .clearTransitive => [2, 3, 2]
  | .wipe => [2, 3, 3]
  | .swarm => [2, 3, 4]
  | .clearIntransitive => [2, 3, 5]
  | .creationAndTransformation => [2, 4]
  | .materialProduct => [2, 4, 1]
  | .materialProductIntransitive => [2, 4, 2]
  | .totalTransformation => [2, 4, 3]
  | .totalTransformationIntransitive => [2, 4, 4]
  | .reciprocal => [2, 5]
  | .simpleReciprocal => [2, 5, 1]
  | .togetherReciprocal => [2, 5, 2]
  | .apartReciprocal => [2, 5, 3]
  | .simpleReciprocalIntransitive => [2, 5, 4]
  | .togetherReciprocalIntransitive => [2, 5, 5]
  | .apartReciprocalIntransitive => [2, 5, 6]
  | .fulfilling => [2, 6]
  | .imageImpression => [2, 7]
  | .withAgainst => [2, 8]
  | .throughWith => [2, 9]
  | .blame => [2, 10]
  | .search => [2, 11]
  | .bodyPartPossessorAscension => [2, 12]
  | .possessorAttributeFactoring => [2, 13]
  | .possessorObject => [2, 13, 1]
  | .attributeObject => [2, 13, 2]
  | .possessorAndAttribute => [2, 13, 3]
  | .possessorSubject => [2, 13, 4]
  | .possessorSubjectIntransitive => [2, 13, 5]
  | .as => [2, 14]
  | .timeSubject => [3, 1]
  | .naturalForceSubject => [3, 2]
  | .instrumentSubject => [3, 3]
  | .abstractCauseSubject => [3, 4]
  | .locatumSubject => [3, 5]
  | .locationSubject => [3, 6]
  | .containerSubject => [3, 7]
  | .rawMaterialSubject => [3, 8]
  | .sumOfMoneySubject => [3, 9]
  | .sourceSubject => [3, 10]
  | .virtualReflexive => [4, 1]
  | .reflexiveOfAppearance => [4, 2]
  | .verbalPassive => [5, 1]
  | .prepositionalPassive => [5, 2]
  | .adjectivalPassive => [5, 3]
  | .adjectivalPerfectParticiple => [5, 4]
  | .thereInsertion => [6, 1]
  | .locativeInversion => [6, 2]
  | .cognateObject => [7, 1]
  | .cognatePrepositionalPhrase => [7, 2]
  | .reactionObject => [7, 3]
  | .wayConstruction => [7, 4]
  | .resultative => [7, 5]
  | .unintentionalInterpretation => [7, 6]
  | .unintentionalInterpretationReflexive => [7, 6, 1]
  | .unintentionalInterpretationBodyPart => [7, 6, 2]
  | .boundNonreflexiveAnaphor => [7, 7]
  | .directionalPhrase => [7, 8]
  | .obligatoryPassive => [8, 1]

/-- The alternation numbered `n` in Part One, if there is one. -/
def ofNumber? (n : List ℕ) : Option DiathesisAlternation :=
  DiathesisAlternation.enumList.find? (·.number = n)

/-- The section title in Part One. -/
def name : DiathesisAlternation → String
  | .objectOfTransitiveSubjectOfIntransitive =>
    "Object of Transitive = Subject of Intransitive Alternations"
  | .middle => "Middle Alternation"
  | .causative => "Causative Alternations"
  | .causativeInchoative => "Causative/Inchoative Alternation"
  | .inducedAction => "Induced Action Alternation"
  | .otherCausative => "Other Instances of Causative Alternations"
  | .substanceSource => "Substance/Source Alternation"
  | .unexpressedObject => "Unexpressed Object Alternations"
  | .unspecifiedObject => "Unspecified Object Alternation"
  | .understoodBodyPartObject => "Understood Body-Part Object Alternation"
  | .understoodReflexiveObject => "Understood Reflexive Object Alternation"
  | .understoodReciprocalObject => "Understood Reciprocal Object Alternation"
  | .proArbObject => "PRO-arb Object Alternation"
  | .characteristicProperty => "Characteristic Property Alternations"
  | .characteristicPropertyOfAgent => "Characteristic Property of Agent Alternation"
  | .characteristicPropertyOfInstrument => "Characteristic Property of Instrument Alternation"
  | .wayObject => "Way Object Alternation"
  | .instructionalImperative => "Instructional Imperative"
  | .conative => "Conative Alternation"
  | .prepositionDrop => "Preposition Drop Alternations"
  | .locativePrepositionDrop => "Locative Preposition Drop Alternation"
  | .withPrepositionDrop => "With Preposition Drop Alternation"
  | .dative => "Dative Alternation"
  | .benefactive => "Benefactive Alternation"
  | .locative => "Locative Alternation"
  | .sprayLoad => "Spray/Load Alternation"
  | .clearTransitive => "Clear Alternation (transitive)"
  | .wipe => "Wipe Alternation"
  | .swarm => "Swarm Alternation"
  | .clearIntransitive => "Clear Alternation (intransitive)"
  | .creationAndTransformation => "Creation and Transformation Alternations"
  | .materialProduct => "Material/Product Alternation (transitive)"
  | .materialProductIntransitive => "Material/Product Alternation (intransitive)"
  | .totalTransformation => "Total Transformation Alternation (transitive)"
  | .totalTransformationIntransitive => "Total Transformation Alternation (intransitive)"
  | .reciprocal => "Reciprocal Alternations"
  | .simpleReciprocal => "Simple Reciprocal Alternation (transitive)"
  | .togetherReciprocal => "Together Reciprocal Alternation (transitive)"
  | .apartReciprocal => "Apart Reciprocal Alternation (transitive)"
  | .simpleReciprocalIntransitive => "Simple Reciprocal Alternation (intransitive)"
  | .togetherReciprocalIntransitive => "Together Reciprocal Alternation (intransitive)"
  | .apartReciprocalIntransitive => "Apart Reciprocal Alternation (intransitive)"
  | .fulfilling => "Fulfilling Alternation"
  | .imageImpression => "Image Impression Alternation"
  | .withAgainst => "With/Against Alternation"
  | .throughWith => "Through/With Alternation"
  | .blame => "Blame Alternation"
  | .search => "Search Alternations"
  | .bodyPartPossessorAscension => "Body-Part Possessor Ascension Alternation"
  | .possessorAttributeFactoring => "Possessor-Attribute Factoring Alternations"
  | .possessorObject => "Possessor Object"
  | .attributeObject => "Attribute Object"
  | .possessorAndAttribute => "Possessor and Attribute Alternation"
  | .possessorSubject => "Possessor Subject (transitive)"
  | .possessorSubjectIntransitive => "Possessor Subject (intransitive)"
  | .as => "As Alternation"
  | .timeSubject => "Time Subject Alternation"
  | .naturalForceSubject => "Natural Force Subject Alternation"
  | .instrumentSubject => "Instrument Subject Alternation"
  | .abstractCauseSubject => "Abstract Cause Subject Alternation"
  | .locatumSubject => "Locatum Subject Alternation"
  | .locationSubject => "Location Subject Alternation"
  | .containerSubject => "Container Subject Alternation"
  | .rawMaterialSubject => "Raw Material Subject Alternation"
  | .sumOfMoneySubject => "Sum of Money Subject Alternation"
  | .sourceSubject => "Source Subject Alternation"
  | .virtualReflexive => "Virtual Reflexive Alternation"
  | .reflexiveOfAppearance => "Reflexive of Appearance Alternation"
  | .verbalPassive => "Verbal Passive"
  | .prepositionalPassive => "Prepositional Passive"
  | .adjectivalPassive => "Adjectival Passive (transitive verbs)"
  | .adjectivalPerfectParticiple => "Adjectival Perfect Participles (intransitive verbs)"
  | .thereInsertion => "There-Insertion"
  | .locativeInversion => "Locative Inversion"
  | .cognateObject => "Cognate Object Construction"
  | .cognatePrepositionalPhrase => "Cognate Prepositional Phrase Construction"
  | .reactionObject => "Reaction Object Construction"
  | .wayConstruction => "X’s Way Construction"
  | .resultative => "Resultative Construction"
  | .unintentionalInterpretation => "Unintentional Interpretation of Object"
  | .unintentionalInterpretationReflexive => "Unintentional Interpretation with Reflexive Object"
  | .unintentionalInterpretationBodyPart => "Unintentional Interpretation with Body-Part Object"
  | .boundNonreflexiveAnaphor => "Bound Nonreflexive Anaphor as Prepositional Object"
  | .directionalPhrase => "Directional Phrases with Nondirected Motion Verbs"
  | .obligatoryPassive => "Obligatory Passive"

/-- The chapter of Part One. -/
def chapter (a : DiathesisAlternation) : ℕ := a.number.headD 0

/-- The family by chapter. -/
def family (a : DiathesisAlternation) : AlternationFamily :=
  match a.chapter with
  | 1 => .transitivity | 2 => .vpInternal | 3 => .obliqueSubject | 4 => .reflexive
  | 5 => .passive | 6 => .postverbalSubject | 7 => .otherConstructions | _ => .specialDiathesis

end DiathesisAlternation

end ArgumentStructure
