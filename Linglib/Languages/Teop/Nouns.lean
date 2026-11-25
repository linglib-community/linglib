module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Syntax.Feature.Number.Basic

/-!
# Teop nouns

This file records the noun classes of Teop (Oceanic, Bougainville), the articles that mark them,
and nouns of each class.

A Teop noun belongs to one of three classes, named by the article it takes in the singular, *e*,
*a* or *o*. The article also marks number. An adjective or numeral agreeing with the noun takes
an article that distinguishes only two classes, and Mosel and Spriggs call these genders I and II,
with the e- and a-classes as the subgenders I-E and I-A of gender I. A body-part term takes the
a-class article when possessed and the o-class article otherwise.

## Main definitions

* `Teop.NounClass`: the three noun classes.
* `Teop.headArticle`: the article of a noun, by class and number.
* `Teop.targetArticle`: the article of an agreeing adjective or numeral.

## Implementation notes

* Number is a value of the singular-plural system.
* The plural article of the e-class is recorded as *o*. Personal names, kinship terms and
  *teiee* 'who' can also take the plural article *ere*.
* A body-part term is recorded with the class it takes without a possessor.

## References

* [mosel-spriggs-2000]
* [corbett-2000]
* [adamson-2024]
-/

@[expose] public section

namespace Teop

/-- The noun classes, named by the singular article. -/
inductive NounClass where
  /-- The class of personal names, kinship terms, socially important people and pets (gender
  I-E). -/
  | e
  /-- The class of most nouns, among them other people, animals with legs, fruit, food, and
  landmarks (gender I-A). -/
  | a
  /-- The class of plants, things made from plants, invertebrates without legs, and many mass
  and abstract nouns (gender II). -/
  | o
  deriving DecidableEq, Repr, Fintype

/-- The basic articles. -/
inductive Article where
  | a
  | e
  | o
  deriving DecidableEq, Repr, Fintype

/-- Teop distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

instance : Nontrivial numberSystem :=
  ⟨⟨⟨.singular, by decide⟩, ⟨.plural, by decide⟩, by decide⟩⟩

/-- The basic article of a noun, by class and number. -/
def headArticle (c : NounClass) : numberSystem → Article :=
  Number.elim numberSystem (match c with | .e => .e | .a => .a | .o => .o)
    (match c with | .e | .a => .o | .o => .a)

/-- The article of an adjective or numeral agreeing with a noun, by the noun's class and
number. -/
def targetArticle (c : NounClass) : numberSystem → Article :=
  Number.elim numberSystem (match c with | .e | .a => .a | .o => .o)
    (match c with | .e | .a => .o | .o => .a)

/-- A Teop noun with its class. -/
abbrev Noun := GenderedNoun NounClass

/-! ### The e-class -/

/-- *iaa* 'mum'. -/
def iaa : Noun := ⟨⟨"iaa", "mum", some .female⟩, .e⟩

/-- *tetee* 'dad'. -/
def tetee : Noun := ⟨⟨"tetee", "dad", some .male⟩, .e⟩

/-- *sina* 'mother', which takes a possessor. -/
def sina : Noun := ⟨⟨"sina", "mother", some .female⟩, .e⟩

/-- *maagee* 'friend'. -/
def maagee : Noun := ⟨⟨"maagee", "friend", none⟩, .e⟩

/-- *siisia* 'teacher'. -/
def siisia : Noun := ⟨⟨"siisia", "teacher", none⟩, .e⟩

/-- *magaru* 'earthquake'. -/
def magaru : Noun := ⟨⟨"magaru", "earthquake", none⟩, .e⟩

/-- *guu* 'pig'. -/
def guu : Noun := ⟨⟨"guu", "pig", none⟩, .e⟩

/-! ### The a-class -/

/-- *moon* 'woman'. -/
def moon : Noun := ⟨⟨"moon", "woman", some .female⟩, .a⟩

/-- *otei* 'man'. -/
def otei : Noun := ⟨⟨"otei", "man", some .male⟩, .a⟩

/-- *beikoo* 'child'. -/
def beikoo : Noun := ⟨⟨"beikoo", "child", none⟩, .a⟩

/-- *keusu* 'rat'. -/
def keusu : Noun := ⟨⟨"keusu", "rat", none⟩, .a⟩

/-- *naovana* 'bird'. -/
def naovana : Noun := ⟨⟨"naovana", "bird", none⟩, .a⟩

/-- *overe* 'coconut', the fruit. -/
def overe : Noun := ⟨⟨"overe", "coconut", none⟩, .a⟩

/-- *pauna* 'banana', the fruit. -/
def pauna : Noun := ⟨⟨"pauna", "banana", none⟩, .a⟩

/-- *kepaa* 'clay pot'. -/
def kepaa : Noun := ⟨⟨"kepaa", "clay pot", none⟩, .a⟩

/-- *anoo* 'peeler', made from pearl shell. -/
def anoo : Noun := ⟨⟨"anoo", "peeler", none⟩, .a⟩

/-- *taba'ani* 'food'. -/
def taba'ani : Noun := ⟨⟨"taba'ani", "food", none⟩, .a⟩

/-- *tahii* 'sea'. -/
def tahii : Noun := ⟨⟨"tahii", "sea", none⟩, .a⟩

/-- *huan* 'rain'. -/
def huan : Noun := ⟨⟨"huan", "rain", none⟩, .a⟩

/-- *uruuru* 'love'. -/
def uruuru : Noun := ⟨⟨"uruuru", "love", none⟩, .a⟩

/-- *inu* 'house'. -/
def inu : Noun := ⟨⟨"inu", "house", none⟩, .a⟩

/-! ### The o-class -/

/-- *overe* 'coconut palm', the plant. -/
def overePalm : Noun := ⟨⟨"overe", "coconut palm", none⟩, .o⟩

/-- *pauna* 'banana tree', the plant. -/
def paunaTree : Noun := ⟨⟨"pauna", "banana tree", none⟩, .o⟩

/-- *paka* 'leaf'. -/
def paka : Noun := ⟨⟨"paka", "leaf", none⟩, .o⟩

/-- *pus* 'stump'. -/
def pus : Noun := ⟨⟨"pus", "stump", none⟩, .o⟩

/-- *hinahoo* 'taro planting stick'. -/
def hinahoo : Noun := ⟨⟨"hinahoo", "taro planting stick", none⟩, .o⟩

/-- *sinivi* 'canoe'. -/
def sinivi : Noun := ⟨⟨"sinivi", "canoe", none⟩, .o⟩

/-- *hoi* 'basket'. -/
def hoi : Noun := ⟨⟨"hoi", "basket", none⟩, .o⟩

/-- *kurita* 'octopus'. -/
def kurita : Noun := ⟨⟨"kurita", "octopus", none⟩, .o⟩

/-- *demdem* 'snail'. -/
def demdem : Noun := ⟨⟨"demdem", "snail", none⟩, .o⟩

/-- *paku* 'feast'. -/
def paku : Noun := ⟨⟨"paku", "feast", none⟩, .o⟩

/-- *suraa* 'fire'. -/
def suraa : Noun := ⟨⟨"suraa", "fire", none⟩, .o⟩

/-- *giigii* 'shooting star'. -/
def giigii : Noun := ⟨⟨"giigii", "shooting star", none⟩, .o⟩

/-- *koara* 'language'. -/
def koara : Noun := ⟨⟨"koara", "language", none⟩, .o⟩

/-! ### Body-part terms -/

/-- *bina* 'spleen'. -/
def bina : Noun := ⟨⟨"bina", "spleen", none⟩, .o⟩

/-- *vuha* 'heart'. -/
def vuha : Noun := ⟨⟨"vuha", "heart", none⟩, .o⟩

/-- *kuri* 'hand', *kuri-na* without a possessor. -/
def kuri : Noun := ⟨⟨"kuri", "hand", none⟩, .o⟩

/-- *iru* 'back of the head'. -/
def iru : Noun := ⟨⟨"iru", "back of the head", none⟩, .o⟩

/-- *ihu* 'nose', *ihu-na* without a possessor. -/
def ihu : Noun := ⟨⟨"ihu", "nose", none⟩, .o⟩

/-- *revasin* 'blood'. -/
def revasin : Noun := ⟨⟨"revasin", "blood", none⟩, .o⟩

/-- *hena* 'name'. -/
def hena : Noun := ⟨⟨"hena", "name", none⟩, .o⟩

/-- *moo* 'leg', *moo-na* without a possessor outside a compound. -/
def moo : Noun := ⟨⟨"moo", "leg", none⟩, .o⟩

/-- The body-part terms. -/
def bodyPartTerms : List Noun := [bina, vuha, kuri, iru, ihu, revasin, hena, moo]

end Teop
