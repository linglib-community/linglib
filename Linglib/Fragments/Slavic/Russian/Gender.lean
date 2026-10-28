module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Russian noun gender

This file defines the three controller genders of Russian, masculine, feminine and neuter, and
nouns with their gender, the gender they restrict their referents to where they do, and their
declension class. Gender is partly fixed by the referent and partly by the declension (Corbett):
*djadja* 'uncle' declines like most feminines and is masculine by its referents, and the
soft-sign nouns are feminine as a rule (Wade §63) but for *put'* 'way', of which "Despite
feminine endings in the genitive, dative and prepositional singular, путь is qualified by masculine
adjectives" (§66). The declension classes are Corbett's as Kramer reports them: *zakon*,
*škola*, *kost'* and *vino* are her examples of the correlation of class and gender (18), the
neuter *znamja* 'banner' (Wade §64) and the masculine *put'* of its exceptions (19), and the
kinship and animal nouns stand for the semantic core (17). *Vrač* 'doctor' is masculine but takes
feminine agreement on a predicate when the referent is female, *Врач обязана помочь больному* 'The
doctor is obliged to help the patient' (Wade §313); the file records its declensional
gender, and the hybrid agreement is in `Studies/Kramer2020.lean`.

Each gender divides into an animate and an inanimate subgender, by which the accusative of a
masculine singular or a plural takes the form of the genitive or of the nominative (Wade §47). The
agreement evidence that the genders are distinct, the endings of the adjectives and of the past
tense, is in `Fragments/Slavic/Russian/Agreement.lean`.

## References

* [wade-2020]
* [corbett-1991]
* [kramer-2020]
-/

@[expose] public section

namespace Russian.Gender

/-! ### Genders and declension classes -/

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- Sex-differentiable nouns denoting males are masculine and those denoting females
feminine ([corbett-1991] §3.1.1, p. 34). -/
def Value.ofReferentGender : ReferentGender → Value
  | .male => .masc
  | .female => .fem

/-- The declension classes, with which gender correlates without either fixing the other. -/
inductive DeclClass where
  /-- The class of *zakon* 'law', typically masculine. -/
  | I
  /-- The class of *škola* 'school', typically feminine. -/
  | II
  /-- The class of *kost'* 'bone', typically feminine, with *put'* and *znamja* the exceptions. -/
  | III
  /-- The remaining patterns, typically neuter. -/
  | IV
  deriving DecidableEq, Repr

/-- A Russian noun with its controller gender, the gender it restricts its referents to where
it does, and its declension class. -/
structure Noun extends GenderedNoun Value where
  /-- The declension class, left out for a noun whose gender its referents fix. -/
  declClass : Option DeclClass := none
  deriving DecidableEq, Repr

/-! ### Nouns whose referents fix their gender -/

/-- *otec* 'father'. -/
def otec : Noun :=
  { form := "otec", gloss := "father", gender := .masc, referentGender := some .male }

/-- *mat'* 'mother'. -/
def mat' : Noun :=
  { form := "mat'", gloss := "mother", gender := .fem, referentGender := some .female }

/-- *brat* 'brother'. -/
def brat : Noun :=
  { form := "brat", gloss := "brother", gender := .masc, referentGender := some .male }

/-- *sestra* 'sister'. -/
def sestra : Noun :=
  { form := "sestra", gloss := "sister", gender := .fem, referentGender := some .female }

/-- *byk* 'bull'. -/
def byk : Noun :=
  { form := "byk", gloss := "bull", gender := .masc, referentGender := some .male }

/-- *korova* 'cow'. -/
def korova : Noun :=
  { form := "korova", gloss := "cow", gender := .fem, referentGender := some .female }

/-- *djadja* 'uncle', of the declension of most feminines and masculine by its referents. -/
def djadja : Noun :=
  { form := "djadja", gloss := "uncle", gender := .masc, referentGender := some .male
  , declClass := some .II }

/-! ### Nouns whose declension goes with their gender -/

/-- *zakon* 'law'. -/
def zakon : Noun := { form := "zakon", gloss := "law", gender := .masc, declClass := some .I }

/-- *škola* 'school'. -/
def škola : Noun := { form := "škola", gloss := "school", gender := .fem, declClass := some .II }

/-- *kost'* 'bone', a soft-sign feminine ([wade-2020] §63). -/
def kost' : Noun := { form := "kost'", gloss := "bone", gender := .fem, declClass := some .III }

/-- *vino* 'wine'. -/
def vino : Noun := { form := "vino", gloss := "wine", gender := .neut, declClass := some .IV }

/-- *znamja* 'banner', of the class of *kost'* but neuter, one of the neuters in *-mja*
([wade-2020] §64). -/
def znamja : Noun :=
  { form := "znamja", gloss := "banner", gender := .neut, declClass := some .III }

/-- *put'* 'way', of the class of *kost'* but masculine ([wade-2020] §66). -/
def put' : Noun := { form := "put'", gloss := "way", gender := .masc, declClass := some .III }

/-- *vrač* 'doctor', masculine and of the class of *zakon*, which takes feminine agreement on a
predicate when the referent is female ([wade-2020] §313). -/
def vrač : Noun := { form := "vrač", gloss := "doctor", gender := .masc, declClass := some .I }

/-! ### The entries -/

/-- The nouns whose referents fix their gender. -/
def semanticCoreNouns : List Noun :=
  [otec, mat', brat, sestra, byk, korova, djadja]

/-- The nouns whose gender goes with their declension, *znamja* and *put'* the exceptions. -/
def remainderNouns : List Noun :=
  [zakon, škola, kost', vino, znamja, put']

/-- The entries. -/
def allNouns : List Noun :=
  semanticCoreNouns ++ remainderNouns ++ [vrač]

theorem declClass_ne_gender :
    znamja.declClass = kost'.declClass ∧ znamja.gender ≠ kost'.gender := ⟨rfl, by decide⟩

/-! ### Subgenders and number -/

/-- Each gender has an animate and an inanimate subgender. Human beings and animals, among others,
are animate, and with an animate controller the accusative of a masculine singular or a plural
takes the genitive's form, with an inanimate one the nominative's ([wade-2020] §47). -/
inductive Animacy where
  | animate
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- Russian distinguishes the singular and the plural. -/
def numberSystem : Number.System := .singularPlural

end Russian.Gender
