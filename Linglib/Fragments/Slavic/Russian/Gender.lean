module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Russian noun gender

This file defines the three controller genders of Russian, masculine, feminine and neuter, and
nouns with their gender, the gender of their referents where they have one, and their declension
class. Gender is partly fixed by the referent and partly by the declension ([corbett-1991]):
*djadja* 'uncle' declines like most feminines and is masculine by its referents, and the
soft-sign nouns are feminine as a rule ([wade-2020] §63) but for *put'* 'way', of which "Despite
feminine endings in the genitive, dative and prepositional singular, путь is qualified by masculine
adjectives" (§66). The declension classes are Corbett's as [kramer-2020] reports them: *zakon*,
*škola*, *kost'* and *vino* are her examples of the correlation of class and gender (18), the
neuter *znamja* 'banner' (Wade §64) and the masculine *put'* of its exceptions (19), and the
kinship and animal nouns stand for the semantic core (17). *Vrač* 'doctor' is masculine but takes
feminine agreement on a predicate when the referent is female, *Врач обязана помочь больному* 'The
doctor is obliged to help the patient' ([wade-2020] §313); the file records its declensional
gender, and the hybrid agreement is in `Studies/Kramer2020.lean`.

The past-tense concord of the verb and the nominative endings of the adjective are the agreement
evidence that the three genders are distinct ([corbett-1991]).

## References

* [wade-2020]
* [corbett-1991]
* [corbett-1998]
* [kramer-2020]
-/

@[expose] public section

namespace Russian.Gender

open Number.System (singularPlural)

/-! ### Genders and declension classes -/

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine
  | .neut => .neuter

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

/-- A Russian noun with its controller gender, the gender of its referents where they have one,
and its declension class. -/
structure Noun extends GenderedNoun Value where
  /-- The declension class, left out for a noun whose gender its referents fix. -/
  declClass : Option DeclClass := none
  deriving DecidableEq, Repr

/-! ### Nouns whose referents fix their gender -/

/-- *otec* 'father'. -/
def otec : Noun :=
  { form := "otec", gloss := "father", gender := .masc, naturalGender := some .masculine }

/-- *mat'* 'mother'. -/
def mat' : Noun :=
  { form := "mat'", gloss := "mother", gender := .fem, naturalGender := some .feminine }

/-- *brat* 'brother'. -/
def brat : Noun :=
  { form := "brat", gloss := "brother", gender := .masc, naturalGender := some .masculine }

/-- *sestra* 'sister'. -/
def sestra : Noun :=
  { form := "sestra", gloss := "sister", gender := .fem, naturalGender := some .feminine }

/-- *byk* 'bull'. -/
def byk : Noun :=
  { form := "byk", gloss := "bull", gender := .masc, naturalGender := some .masculine }

/-- *korova* 'cow'. -/
def korova : Noun :=
  { form := "korova", gloss := "cow", gender := .fem, naturalGender := some .feminine }

/-- *djadja* 'uncle', of the declension of most feminines and masculine by its referents. -/
def djadja : Noun :=
  { form := "djadja", gloss := "uncle", gender := .masc, naturalGender := some .masculine
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

/-- The declension class does not fix the gender: *znamja* and *kost'* share a class and differ in
gender. -/
theorem declClass_ne_gender :
    znamja.declClass = kost'.declClass ∧ znamja.gender ≠ kost'.gender := ⟨rfl, by decide⟩

/-! ### Agreement evidence -/

/-- The past-tense concord endings of the verb, *-∅*, *-a* and *-o*. -/
inductive PastConcord where
  | zero
  | a
  | o
  deriving DecidableEq, Repr

/-- The past-tense concord ending of each gender. -/
def Value.pastConcord : Value → PastConcord
  | .masc => .zero
  | .fem  => .a
  | .neut => .o

/-- The nominative endings of a hard-stem adjective such as *novyj* 'new': *-yj*, *-aja*,
*-oe* by gender in the singular, *-ye* for all three in the plural ([wade-2020];
[corbett-1998]). -/
inductive AdjEnding where
  | yj
  | aja
  | oe
  | ye
  deriving DecidableEq, Repr, Fintype

/-- Russian distinguishes the singular and the plural. -/
abbrev numberSystem : Number.System := .singularPlural

/-- The nominative ending by gender and number. -/
def Value.adjEnding (g : Value) : numberSystem.values → AdjEnding :=
  singularPlural.elim (match g with | .masc => .yj | .fem => .aja | .neut => .oe) .ye

/-- The singular ending alone distinguishes the three genders. -/
theorem faithful_adjEnding :
    Function.Injective (Value.adjEnding · (numberSystem.value .singular)) := by
  decide

/-- The past-tense concord distinguishes the three genders on a single target. -/
theorem faithful_pastConcord : Function.Injective Value.pastConcord := by decide

end Russian.Gender
