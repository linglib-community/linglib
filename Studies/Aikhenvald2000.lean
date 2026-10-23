module

public import Linglib.Fragments.Mandarin.Nouns
public import Studies.Downing1996
public import Mathlib.Data.Finset.Image

/-!
# A typology of noun categorization devices

Aikhenvald's typology individuates classifier types by their morphosyntactic locus and
scope, the definitional parameters (A)–(G) of the book's first chapter, and then reads the
contingent parameters — interaction with other categories, preferred semantics, evolution,
acquisition — as correlates of the types so established. The types are focal points on a
continuum rather than discrete classes, and most generalizations are tendencies with listed
exceptions. Here the book's parameters are functions on a sample of seven languages
(`Language`), the French and Italian gender systems, the Xhosa, Shona and Swahili noun-class
systems, and the Mandarin and Japanese numeral-classifier systems, coded as the book describes
them, with the kind of each device derived from its locus and the constituent it characterizes
rather than stored and the realizations of the classifier languages read off their fragments'
entries; the book's summary claims are checked on that sample, and none is a universal.
Western Armenian, whose numerals combine with bare nouns, is not classified as a classifier
language by the book and is left to `BaleKhanjian2014`.

## Main results

* `nounClass_agreement_obligatory`, `nounClass_bound`: a noun class system is defined by agreement
  outside the noun, is closed and obligatory, and is never expressed by free lexemes.
* `free_numeralClassifier_no_agreement`: free-form numeral classifiers do not agree.
* `numeralClassifier_obligatory`: in both classifier languages no noun that takes a classifier is
  counted without one, read off the fragments.
* `classifier_assignment_semantic`: every kind other than noun class assigns classifiers on
  semantic grounds.
* `numeralClassifier_general`: both numeral-classifier systems have a general classifier, every
  Mandarin noun that takes a classifier taking *gè* and the category of Japanese *-tsu* having no
  parameter in Downing's inventory.
* `animacy_basic`, `numeralClassifier_shape`, `colour_never`: animacy, humanness or sex is basic
  to noun classes and numeral classifiers, shape is typical of numeral classifiers, and colour is
  never a basis for categorization.
* `numeralClassifier_no_obligatory_number`: numeral-classifier languages lack compulsory number,
  Greenberg's association, which the book records with its Dravidian, Nivkh, Algonquian, Tucano,
  Arawak and Ejagham exceptions.

## References

* [aikhenvald-2000]
* [greenberg-1972]
* [li-thompson-1981]
* [downing-1996]
-/

@[expose] public section

namespace Aikhenvald2000

open Classifier

/-- The sample has two gender systems, three Bantu noun-class systems and two
numeral-classifier systems. -/
inductive Language where
  | french | italian | xhosa | shona | swahili | mandarin | japanese
  deriving DecidableEq, Fintype

namespace Language

/-- The locus of coding (the book's (A)) is the head-modifier NP for the gender and noun-class
systems and the numeral NP for the numeral classifiers. -/
def locus : Language → Scope
  | mandarin | japanese => .numeralNP
  | french | italian | xhosa | shona | swahili => .headModifierNP

/-- Every device of the sample characterizes the head noun (the book's (B)). -/
def constituent (_ : Language) : Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
def device (l : Language) : Option Device := Device.ofScope l.locus l.constituent

/-- The scopes the device operates in (the book's (B)). Mandarin uses the same classifiers with
numerals and with demonstratives (the book's Table 9.1), and agreement in gender and class
reaches the predicate. -/
def scopes : Language → Finset Scope
  | mandarin => {.numeralNP, .attributiveNP}
  | japanese => {.numeralNP}
  | french | italian | xhosa | shona | swahili => {.headModifierNP, .predicateArgument}

/-- The assignment is wholly semantic (the book's (C)), as it is for the numeral classifiers.
Gender and noun class assignment has a semantic core, but that core is never the whole of it. -/
def SemanticAssignment : Language → Prop
  | mandarin | japanese => True
  | french | italian | xhosa | shona | swahili => False

/-- The surface realizations (the book's (D)) are read off the fragments' entries for the
classifier languages, Mandarin's independent forms and Japanese's suffixes on the numeral; gender
is inflection on the agreeing words and Bantu class a prefix. -/
def realizations : Language → Finset Realization
  | mandarin => Mandarin.Classifiers.classifiers.image Classifier.realization
  | japanese => Japanese.Classifiers.classifiers.image Classifier.realization
  | french | italian => {.morph (.bound .after .affix)}
  | xhosa | shona | swahili => {.morph (.bound .before .affix)}

/-- The device participates in agreement (the book's (E)). -/
def Agreement : Language → Prop
  | mandarin | japanese => False
  | french | italian | xhosa | shona | swahili => True

/-- The device is obligatory (the book's (G)). For the numeral classifiers this is read off the
fragments, where no noun that takes a classifier is counted without one. Gender and noun class
are obligatory as the book describes them. -/
def Obligatory : Language → Prop
  | mandarin => ∀ n ∈ Mandarin.Nouns.nouns, n.classifiers.Nonempty → ¬ n.IsBareCount
  | japanese => ∀ n ∈ Japanese.Nouns.nouns, n.classifiers.Nonempty → ¬ n.IsBareCount
  | french | italian | xhosa | shona | swahili => True

/-- The system has a functionally unmarked member or a general classifier (the book's (F)). For
the numeral classifiers this is read off the earlier descriptions, as a Mandarin classifier every
counted noun can take and a classifier of Downing's inventory whose category has no parameter.
The masculine gender and a default class are the unmarked members of the other systems. -/
def HasUnmarkedMember : Language → Prop
  | mandarin => ∃ c ∈ Mandarin.Classifiers.classifiers,
      ∀ n ∈ Mandarin.Nouns.nouns, n.classifiers.Nonempty → n.Takes c
  | japanese => ∃ r : Downing1996.Row, r.params = []
  | french | italian | xhosa | shona | swahili => True

/-- The preferred semantic parameters (the book's (I)). Sex and animacy for the Romance genders,
humanness and animacy for the Bantu classes; for Mandarin, the animacy of *zhī* and the shape by
which *tiáo* extended from 'small branch' to long things in general, shape being the preferred
parameter of numeral classifiers; for Japanese, the parameters of the categories of Downing's
inventory. -/
def semantics : Language → Finset Parameter
  | french | italian => {.sex, .animacy}
  | xhosa | shona | swahili => {.humanness, .animacy}
  | mandarin => {.animacy, .shape}
  | japanese => (Finset.univ : Finset Downing1996.Row).biUnion (·.params.toFinset)

/-- The language marks number obligatorily. -/
def ObligatoryNumber : Language → Prop
  | mandarin | japanese => False
  | french | italian | xhosa | shona | swahili => True

instance : DecidablePred SemanticAssignment := fun l ↦ by
  cases l <;> unfold SemanticAssignment <;> infer_instance

instance : DecidablePred Agreement := fun l ↦ by cases l <;> unfold Agreement <;> infer_instance

instance : DecidablePred Obligatory := fun l ↦ by
  cases l <;> unfold Obligatory <;> infer_instance

instance : DecidablePred ObligatoryNumber := fun l ↦ by
  cases l <;> unfold ObligatoryNumber <;> infer_instance

end Language

open Language

/-! ### Definitional properties -/

/-- A noun class system is defined by agreement outside the noun and is a closed obligatory
grammatical system. -/
theorem nounClass_agreement_obligatory :
    ∀ l : Language, l.device = some .nounClass → l.Agreement ∧ l.Obligatory := by
  decide

/-- Noun classes are realized with affixes or clitics, never with free lexemes. -/
theorem nounClass_bound :
    ∀ l : Language, l.device = some .nounClass → .morph .free ∉ l.realizations := by
  decide

/-- Numeral classifiers expressed as free morphemes do not participate in agreement. -/
theorem free_numeralClassifier_no_agreement :
    ∀ l : Language, l.device = some .numeralClassifier → .morph .free ∈ l.realizations →
      ¬ l.Agreement := by
  decide

/-- The numeral classifiers of the sample are obligatory, since no noun of the Mandarin or
Japanese fragment that takes a classifier is counted without one, though Mandarin *tiān* 'day',
which takes none, is counted directly. -/
theorem numeralClassifier_obligatory :
    (∀ l : Language, l.device = some .numeralClassifier → l.Obligatory) ∧
      Mandarin.Nouns.tian.IsBareCount := by
  decide

/-- Every kind of device other than noun class is assigned on purely semantic grounds; noun
class assignment may be only partially semantic. -/
theorem classifier_assignment_semantic :
    ∀ l : Language, l.device ≠ some .nounClass → l.SemanticAssignment := by
  decide

/-- Both numeral-classifier systems have a general classifier that can replace the specific
ones, the analogue of a functionally unmarked noun class. In Mandarin it is *gè*, which every noun
that takes a classifier can take, and in Japanese *-tsu*. -/
theorem numeralClassifier_general :
    ∀ l : Language, l.device = some .numeralClassifier → l.HasUnmarkedMember
  | .mandarin, _ =>
    ⟨Mandarin.Classifiers.ge, by simp [Mandarin.Classifiers.classifiers],
      fun _ _ h ↦ Mandarin.Nouns.Noun.takes_ge h⟩
  | .japanese, _ => ⟨.tsu, rfl⟩

/-! ### Preferred semantics -/

/-- Animacy, humanness or sex is basic to noun classes and numeral classifiers. -/
theorem animacy_basic :
    ∀ l : Language, l.device = some .nounClass ∨ l.device = some .numeralClassifier →
      ∃ p ∈ l.semantics, p = .animacy ∨ p = .humanness ∨ p = .sex := by
  decide

/-- Physical properties such as shape are typical of numeral classifiers. -/
theorem numeralClassifier_shape :
    ∀ l : Language, l.device = some .numeralClassifier → .shape ∈ l.semantics := by
  decide

/-- Colour is never a basis for noun categorization. -/
theorem colour_never : ∀ l : Language, .colour ∉ l.semantics := by decide

/-! ### Classifiers and number -/

/-- Numeral-classifier languages usually lack compulsory number marking. -/
theorem numeralClassifier_no_obligatory_number :
    ∀ l : Language, l.device = some .numeralClassifier → ¬ l.ObligatoryNumber := by
  decide

end Aikhenvald2000
