module

public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Romance.French.Nouns
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.Romance.Italian.Nouns
public import Linglib.Fragments.Shona.Nouns
public import Linglib.Fragments.Swahili.Nouns
public import Linglib.Fragments.Xhosa.Nouns
public import Studies.Corbett1991
public import Studies.Downing1996
public import Mathlib.Data.Finset.Image

/-!
# Aikhenvald (2000): Classifiers: A Typology of Noun Categorization Devices

The book sorts noun categorization devices into kinds by the morphosyntactic locus of their
morphemes and the constituent they characterize, `Classifier.Device.ofScope`, and then gives the
properties in which the kinds differ. This file states the properties its concluding chapter
tabulates as functions of the kind and checks them on the systems the fragments hold, the
numeral classifiers of Mandarin and Japanese, the noun classes of Swahili, Xhosa and Shona and
the genders of French and Italian.

* Assignment. A noun class may be assigned only partly on semantic grounds, though every noun
  class system has a semantic core of sex, humanness or animacy, and every noun belongs to a
  class; every other kind is assigned semantically and need not cover every noun
  (`FullySemantic`, `ClassifiesEveryNoun`).
* Realization. Noun classes and verbal classifiers are never free lexemes (`AdmitsFree`), and
  each kind admits some of the further devices of apophony, suppletion, stress, reduplication,
  noun incorporation and repeaters (`Admits`).
* Agreement. Noun classes and deictic, possessor and verbal classifiers take part in agreement,
  numeral and possessed classifiers only when bound, and relational and noun classifiers never
  (`agreement`).
* Markedness. A general classifier is the analogue of a functionally unmarked noun class.
* Semantics. Each kind prefers some semantic parameters (`Typical`), and colour is the basis of
  no kind.

## Implementation notes

The tables leave out possessor classifiers, about which the book makes no generalization;
`Admits` and `Typical` place no condition on them. Physical properties are the parameters of
`Classifier.Parameter.Class.physical`, which include the direction, arrangement and quanta the
book's table of preferred semantics lists apart. A realization the book admits rarely or only in
multiple classifier systems is admitted. The agreement of locative classifiers, which the
summary of agreement does not mention, is left open.

## TODO

The association of numeral classifiers with the absence of obligatory plural marking, the
interactions with other grammatical categories, and the origins and acquisition of classifiers
are not formalized.

## References

* [aikhenvald-2000]
* [corbett-1991]
* [downing-1996]
-/

@[expose] public section

namespace Aikhenvald2000

open Classifier Morphology

/-! ### Properties of the kinds of device -/

/-- The assignment of the device is wholly semantic, as it is for every kind but noun class. -/
def FullySemantic (d : Device) : Prop := d ≠ .nounClass

/-- Every noun belongs to a class of the device, as with noun class alone. -/
def ClassifiesEveryNoun (d : Device) : Prop := d = .nounClass

/-- The device can be expressed with free lexemes, as noun classes and verbal classifiers
cannot. -/
def AdmitsFree (d : Device) : Prop := d ≠ .nounClass ∧ d ≠ .verbalClassifier

instance : DecidablePred FullySemantic := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred ClassifiesEveryNoun := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred AdmitsFree := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The device admits the realization: a free lexeme where the kind can be free, a prefix or
proclitic for every kind but locative classifiers, a suffix or enclitic for every kind, and the
further devices each for the kinds the book's table of realizations marks. -/
def Admits (d : Device) : Realization → Prop
  | .morph k =>
    d = .possessorClassifier ∨
      (k.position? = none → AdmitsFree d) ∧ (k.position? = some .before → d ≠ .locativeClassifier)
  | .apophony | .stress => d = .possessorClassifier ∨ d = .nounClass
  | .suppletion =>
    d = .possessorClassifier ∨ d = .numeralClassifier ∨ d = .verbalClassifier ∨
      d = .locativeClassifier ∨ d = .deicticClassifier
  | .reduplication => d = .possessorClassifier ∨ d = .numeralClassifier
  | .nounIncorporation => d = .possessorClassifier ∨ d = .verbalClassifier
  | .repeater =>
    d = .possessorClassifier ∨ d = .nounClass ∨ d = .numeralClassifier ∨
      d = .possessedClassifier ∨ d = .nounClassifier ∨ d = .deicticClassifier

instance : ∀ d r, Decidable (Admits d r) := fun d r ↦ by
  cases r <;> unfold Admits <;> infer_instance

/-- When a kind of device takes part in agreement. -/
inductive AgreementRole where
  | always
  /-- Only when expressed with bound morphemes. -/
  | whenBound
  | never
  deriving DecidableEq, Repr, Fintype

/-- The part of a kind of device in agreement, where the book states it. -/
def agreement : Device → Option AgreementRole
  | .nounClass | .deicticClassifier | .possessorClassifier | .verbalClassifier => some .always
  | .numeralClassifier | .possessedClassifier => some .whenBound
  | .relationalClassifier | .nounClassifier => some .never
  | .locativeClassifier => none

/-- The parameter is animacy, humanness or sex. -/
def IsAnimacy (p : Parameter) : Prop := p = .animacy ∨ p = .humanness ∨ p = .sex

/-- The parameter is a physical property. -/
def IsPhysical (p : Parameter) : Prop := p.toClass = some .physical

instance : DecidablePred IsAnimacy := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))
instance : DecidablePred IsPhysical := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The semantic parameters typical of a kind of device. -/
def Typical : Device → Parameter → Prop
  | .nounClass, p => IsAnimacy p ∨ IsPhysical p ∨ p = .nature ∨ p = .function
  | .numeralClassifier, p =>
    IsAnimacy p ∨ p = .socialStatus ∨ p = .kinship ∨ IsPhysical p ∨ p = .nature ∨ p = .function
  | .nounClassifier, p => p = .socialStatus ∨ p = .function ∨ p = .nature
  | .verbalClassifier, p => IsPhysical p ∨ p = .nature ∨ p = .function ∨ IsAnimacy p
  | .relationalClassifier, p => p = .function ∨ p = .nature
  | .possessedClassifier, p => IsPhysical p ∨ p = .nature ∨ IsAnimacy p ∨ p = .function
  | .locativeClassifier, p => IsPhysical p ∨ p = .nature ∨ IsAnimacy p
  | .deicticClassifier, p => IsPhysical p ∨ p = .nature
  | .possessorClassifier, p => p ≠ .colour

instance : ∀ d p, Decidable (Typical d p) := fun d p ↦ by
  cases d <;> unfold Typical <;> infer_instance

theorem typical_animacy_not_colour {d : Device}
    (hd : d = .nounClass ∨ d = .numeralClassifier) :
    Typical d .animacy ∧ ∀ d' : Device, ¬ Typical d' .colour := by
  rcases hd with rfl | rfl <;> decide

theorem admitsFree_of_agreement {d : Device} {a : AgreementRole} (h : agreement d = some a)
    (ha : a ≠ .always) : AdmitsFree d := by
  decide +revert

/-! ### The systems of the fragments -/

/-- The classifiers of Mandarin and Japanese are realizations numeral classifiers admit, free
lexemes in Mandarin; the class prefixes of Swahili, Xhosa and Shona and the feminine suffix of
French are realizations noun classes admit, and none is free. -/
theorem realization_admitted :
    (∀ c ∈ Mandarin.Classifiers.classifiers,
      Admits .numeralClassifier c.realization ∧ c.kind = .free) ∧
    (∀ c ∈ Japanese.Classifiers.classifiers, Admits .numeralClassifier c.realization) ∧
    (∀ cl m, Swahili.subjPrefix cl = some m →
      Admits .nounClass (.morph m.kind) ∧ m.kind ≠ .free) ∧
    (∀ cl m, Xhosa.subjPrefix cl = some m → Admits .nounClass (.morph m.kind) ∧ m.kind ≠ .free) ∧
    (∀ cl m, Shona.subjPrefix cl = some m → Admits .nounClass (.morph m.kind) ∧ m.kind ≠ .free) ∧
    Admits .nounClass (.morph French.Gender.feminineSuffix.kind) ∧
      French.Gender.feminineSuffix.kind ≠ .free := by
  decide

theorem romance_agreement :
    Function.Injective French.Gender.indefiniteArticle ∧
      ∀ r, Function.Injective fun g ↦ Italian.Determiners.questo (r, g) := by
  decide

/-- The gender of sexed referents: the masculine for males and the feminine for females. -/
def frenchSex : ReferentGender → French.Gender.Value
  | .male => .masculine
  | .female => .feminine

/-- The gender of sexed referents: the masculine for males and the feminine for females. -/
def italianSex : ReferentGender → Italian.Gender.Value
  | .male => .masculine
  | .female => .feminine

/-- Every French or Italian noun of the fragments that fixes the sex of its referents has the
gender of that sex, the semantic core of the two systems, and nouns that fix none are found in
both genders. -/
theorem romance_semantic_core :
    (∀ n ∈ French.Nouns.nouns, n.referentGender.isSome → n.toGenderedNoun.IsNatural frenchSex) ∧
    (∀ g, ∃ n ∈ French.Nouns.nouns, n.referentGender = none ∧ n.gender = g) ∧
    (∀ n ∈ Italian.Nouns.nouns, n.referentGender.isSome →
      n.toGenderedNoun.IsNatural italianSex) ∧
    ∀ g, ∃ n ∈ Italian.Nouns.nouns, n.referentGender = none ∧ n.gender = g := by
  decide

theorem semantic_core :
    (∀ n ∈ Swahili.allNouns, n.gender = .genderA →
      (Corbett1991.Swahili.system.semantic (Corbett1991.Swahili.sem n)).isSome) ∧
      ∀ n ∈ Shona.Nouns.all, n.gender = .genderA → n.animacy ≠ .inanimate := by
  decide

/-- Animacy does not settle the gender of a Swahili, Xhosa or Shona noun: two nouns alike in
animacy differ in gender, and in Xhosa the gender of classes 1 and 2 has inanimate nouns too. -/
theorem partially_semantic :
    (∃ n ∈ Swahili.allNouns, ∃ n' ∈ Swahili.allNouns,
      n.animacy = n'.animacy ∧ n.gender ≠ n'.gender) ∧
    (∃ n ∈ Xhosa.Nouns.all, ∃ n' ∈ Xhosa.Nouns.all,
      n.animacy = n'.animacy ∧ n.gender ≠ n'.gender) ∧
    (∃ n ∈ Shona.Nouns.all, ∃ n' ∈ Shona.Nouns.all,
      n.animacy = n'.animacy ∧ n.gender ≠ n'.gender) ∧
    ∃ n ∈ Xhosa.Nouns.all, n.gender = .genderA ∧ n.animacy = .inanimate := by
  decide

/-- Mandarin *gè* counts every noun that takes a classifier, and Japanese *-tsu* is the one
classifier of Downing's inventory with no semantic parameter: each system has a general
classifier. -/
theorem general_classifier :
    (∀ n ∈ Mandarin.Nouns.nouns, n.classifiers.Nonempty → n.Takes Mandarin.Classifiers.ge) ∧
      ∀ p ∈ Downing1996.coding, p.2 = [] ↔ p.1 = Japanese.Classifiers.tsu :=
  ⟨fun _ _ h ↦ Mandarin.Nouns.Noun.takes_ge h, Downing1996.coding_eq_nil_iff⟩

theorem mandarin_bare_count :
    ¬ ClassifiesEveryNoun .numeralClassifier ∧
      ∃ n ∈ Mandarin.Nouns.nouns, n.classifiers = ∅ ∧ n.IsBareCount := by
  decide

/-- Every semantic parameter of Downing's inventory of Japanese classifiers is typical of numeral
classifiers, but for the speech register of *-mei*. -/
theorem typical_japanese :
    ∀ p ∈ Downing1996.coding, ∀ q ∈ p.2, Typical .numeralClassifier q ∨ q = .register := by
  decide

end Aikhenvald2000
