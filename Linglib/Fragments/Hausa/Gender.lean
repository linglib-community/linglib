module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Syntax.Gender.Assignment

/-!
# Hausa gender

Hausa has two genders, masculine and feminine, operative only in the singular: *yārò* 'boy' is
masculine and *yārinyā̀* 'girl' feminine, while the plural *yârā* 'children' has no gender. Nouns
for people and large animals take the gender of the referent's sex; for the rest gender is
lexically specific, *turmī* 'mortar' masculine and *wuƙā* 'knife' feminine.

Most native feminine nouns end in *-ā*, as *rìgā* 'gown', but the ending does not assign gender.
Some hundred feminines end otherwise, among them the old native word *màcè* 'woman', and over 250
of some 3,000 masculine nouns end in *-ā*: native stems such as *kadā̀* 'crocodile' and *ùbā*
'father', loanwords, and erstwhile plurals such as *gidā* 'house'. The correlation is historical:
feminine nouns acquired the ending by overt characterization, the addition of the feminine suffix
{-ā} to words that were already feminine ([newman-2000]).

## Main definitions

* `Hausa.Gender.Value` — the two genders, with their comparative labels
* `Hausa.Noun` — a noun with its gender and the sex of its referents where it has one
* `Hausa.Noun.EndsInAa` — the noun ends in *-ā*
* `Hausa.allNouns` — the nouns

## References

* [newman-2000]
-/

@[expose] public section

namespace Hausa

/-- The two genders. -/
inductive Gender.Value where
  | masculine
  | feminine
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Gender.Value.ofSex : Sex → Gender.Value
  | .male => .masculine
  | .female => .feminine

/-- A Hausa noun, with the gender its agreement shows and the sex it restricts its referents to
where it does. -/
abbrev Noun := GenderedNoun Gender.Value

namespace Noun

/-- A noun's gender is natural when it is the one its referents' sex is assigned. -/
abbrev IsNatural (n : Noun) : Prop :=
  _root_.Gender.IsNatural (Option.map Gender.Value.ofSex) GenderedNoun.sex GenderedNoun.gender n

/-- The noun ends in *-ā*, whatever its final tone: the long vowel is one of the last two
characters, the second being a tone mark. -/
abbrev EndsInAa (n : Noun) : Prop :=
  'ā' ∈ n.form.toList.reverse.take 2

end Noun

/-- *yārinyā̀* 'girl'. -/
def yarinya : Noun := ⟨⟨"yārinyā̀", "girl"⟩, .feminine, some .female⟩

/-- *màcè* 'woman', a basic feminine word not in *-ā*, perhaps once a derived form meaning
'female'. -/
def mace : Noun := ⟨⟨"màcè", "woman"⟩, .feminine, some .female⟩

/-- *kā̀zā* 'hen', opposite *zàkarā̀* 'cock'. -/
def kaza : Noun := ⟨⟨"kā̀zā", "hen"⟩, .feminine, some .female⟩

/-- *rìgā* 'gown'. -/
def riga : Noun := ⟨⟨"rìgā", "gown"⟩, .feminine, none⟩

/-- *yārò* 'boy'. -/
def yaro : Noun := ⟨⟨"yārò", "boy"⟩, .masculine, some .male⟩

/-- *mùtûm* 'man'. -/
def mutum : Noun := ⟨⟨"mùtûm", "man"⟩, .masculine, some .male⟩

/-- *turmī* 'mortar'. -/
def turmi : Noun := ⟨⟨"turmī", "mortar"⟩, .masculine, none⟩

/-- *gidā* 'house', a masculine in *-ā* that was once a plural. -/
def gida : Noun := ⟨⟨"gidā", "house"⟩, .masculine, none⟩

/-- *wuƙā* 'knife'. -/
def wuka : Noun := ⟨⟨"wuƙā", "knife"⟩, .feminine, none⟩

/-- *rānā* 'sun'. -/
def rana : Noun := ⟨⟨"rānā", "sun"⟩, .feminine, none⟩

/-- *kadā̀* 'crocodile', a native masculine in *-ā*. -/
def kada : Noun := ⟨⟨"kadā̀", "crocodile"⟩, .masculine, none⟩

/-- *ùbā* 'father', a native masculine in *-ā*. -/
def uba : Noun := ⟨⟨"ùbā", "father"⟩, .masculine, some .male⟩

/-- The nouns. -/
def allNouns : List Noun :=
  [yarinya, mace, kaza, riga, yaro, mutum, turmi, gida, wuka, rana, kada, uba]

end Hausa
