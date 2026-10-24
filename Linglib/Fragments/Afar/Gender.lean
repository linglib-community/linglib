module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Afar noun gender

Afar (Qafar) has two genders. Nouns denoting men and women take the gender of their referents;
for the
rest, the position of the accent decides: a citation form ending in an accented vowel is
feminine, any other masculine, with the pairs *bàxa* 'son' ~ *baxà* 'daughter' carrying both
signals at once ([parker-hayward-1985]; [corbett-1991]).

## References

* [E. M. Parker, R. J. Hayward, *An Afar-English-French Dictionary*
  (1985)][parker-hayward-1985]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

@[expose] public section

namespace Afar.Gender

/-- The two controller genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender.Label
  | .masc => .masculine
  | .fem => .feminine

/-- An Afar noun with its gender, the gender of its referents where it has one, and
whether its citation form ends in an accented vowel. -/
structure Noun extends GenderedNoun Value where
  /-- Whether the citation form ends in an accented vowel. -/
  finalAccentedVowel : Bool
  deriving DecidableEq, Repr

def baqla : Noun := ⟨⟨⟨"bàqla", "husband"⟩, .masc, some .masculine⟩, false⟩
def barra : Noun := ⟨⟨⟨"barrà", "woman, wife"⟩, .fem, some .feminine⟩, true⟩
def baxa : Noun := ⟨⟨⟨"bàxa", "son"⟩, .masc, some .masculine⟩, false⟩
def baxa' : Noun := ⟨⟨⟨"baxà", "daughter"⟩, .fem, some .feminine⟩, true⟩
def toobokoyta : Noun := ⟨⟨⟨"toobokòyta", "brother"⟩, .masc, some .masculine⟩, false⟩
def toobokoyta' : Noun := ⟨⟨⟨"toobokoytà", "sister"⟩, .fem, some .feminine⟩, true⟩
def bariseyna : Noun := ⟨⟨⟨"barisèyna", "male teacher"⟩, .masc, some .masculine⟩, false⟩
def bariseyna' : Noun := ⟨⟨⟨"bariseynà", "female teacher"⟩, .fem, some .feminine⟩, true⟩
def kuta : Noun := ⟨⟨⟨"kùta", "dog"⟩, .masc, some .masculine⟩, false⟩
def kuta' : Noun := ⟨⟨⟨"kutà", "bitch"⟩, .fem, some .feminine⟩, true⟩
def cato : Noun := ⟨⟨⟨"catò", "help"⟩, .fem, none⟩, true⟩
def karma : Noun := ⟨⟨⟨"karmà", "autumn"⟩, .fem, none⟩, true⟩
def ceder : Noun := ⟨⟨⟨"cedèr", "supper time"⟩, .masc, none⟩, false⟩
def gilal : Noun := ⟨⟨⟨"gilàl", "winter"⟩, .masc, none⟩, false⟩
def tamu : Noun := ⟨⟨⟨"tàmu", "taste"⟩, .masc, none⟩, false⟩
def baanta : Noun := ⟨⟨⟨"baànta", "trumpet"⟩, .masc, none⟩, false⟩
/-- *doònik* 'sail-boat': feminine against the accent rule. -/
def doonik : Noun := ⟨⟨⟨"doònik", "sail-boat"⟩, .fem, none⟩, false⟩
/-- *abbà* 'father' is masculine by its referents against the accent rule. -/
def abba : Noun := ⟨⟨⟨"abbà", "father"⟩, .masc, some .masculine⟩, true⟩
/-- *gabbixeèra* 'slender-waisted female' is feminine by its referents against the accent rule. -/
def gabbixeera : Noun := ⟨⟨⟨"gabbixeèra", "slender-waisted female"⟩, .fem, some .feminine⟩, false⟩

def allNouns : List Noun :=
  [baqla, barra, baxa, baxa', toobokoyta, toobokoyta', bariseyna, bariseyna', kuta, kuta', cato,
    karma, ceder, gilal, tamu, baanta, doonik, abba, gabbixeera]

end Afar.Gender
