module

public import Linglib.Syntax.Category.Noun.Basic

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
abbrev numberSystem : Number.System := .singularPlural

/-- The basic article of a noun, by class and number. -/
def headArticle (c : NounClass) (n : numberSystem.values) : Article :=
  match c, n.1 with
  | .e, .singular => .e
  | .a, .singular => .a
  | .o, .singular => .o
  | .e, _ | .a, _ => .o
  | .o, _ => .a

/-- The article of an adjective or numeral agreeing with a noun, by the noun's class and
number. -/
def targetArticle (c : NounClass) (n : numberSystem.values) : Article :=
  match c, n.1 with
  | .e, .singular | .a, .singular => .a
  | .o, .singular => .o
  | .o, _ => .a
  | _, _ => .o

/-- A Teop noun with its class. -/
abbrev Noun := GenderedNoun NounClass

/-! ### The e-class -/

/-- *iaa* 'mum'. -/
def iaa : Noun := ⟨⟨"iaa", "mum"⟩, .e, some .feminine⟩

/-- *tetee* 'dad'. -/
def tetee : Noun := ⟨⟨"tetee", "dad"⟩, .e, some .masculine⟩

/-- *sina* 'mother', which takes a possessor. -/
def sina : Noun := ⟨⟨"sina", "mother"⟩, .e, some .feminine⟩

/-- *maagee* 'friend'. -/
def maagee : Noun := ⟨⟨"maagee", "friend"⟩, .e, none⟩

/-- *siisia* 'teacher'. -/
def siisia : Noun := ⟨⟨"siisia", "teacher"⟩, .e, none⟩

/-- *magaru* 'earthquake'. -/
def magaru : Noun := ⟨⟨"magaru", "earthquake"⟩, .e, none⟩

/-- *guu* 'pig'. -/
def guu : Noun := ⟨⟨"guu", "pig"⟩, .e, none⟩

/-! ### The a-class -/

/-- *moon* 'woman'. -/
def moon : Noun := ⟨⟨"moon", "woman"⟩, .a, some .feminine⟩

/-- *otei* 'man'. -/
def otei : Noun := ⟨⟨"otei", "man"⟩, .a, some .masculine⟩

/-- *beikoo* 'child'. -/
def beikoo : Noun := ⟨⟨"beikoo", "child"⟩, .a, none⟩

/-- *keusu* 'rat'. -/
def keusu : Noun := ⟨⟨"keusu", "rat"⟩, .a, none⟩

/-- *naovana* 'bird'. -/
def naovana : Noun := ⟨⟨"naovana", "bird"⟩, .a, none⟩

/-- *overe* 'coconut', the fruit. -/
def overe : Noun := ⟨⟨"overe", "coconut"⟩, .a, none⟩

/-- *pauna* 'banana', the fruit. -/
def pauna : Noun := ⟨⟨"pauna", "banana"⟩, .a, none⟩

/-- *kepaa* 'clay pot'. -/
def kepaa : Noun := ⟨⟨"kepaa", "clay pot"⟩, .a, none⟩

/-- *anoo* 'peeler', made from pearl shell. -/
def anoo : Noun := ⟨⟨"anoo", "peeler"⟩, .a, none⟩

/-- *taba'ani* 'food'. -/
def taba'ani : Noun := ⟨⟨"taba'ani", "food"⟩, .a, none⟩

/-- *tahii* 'sea'. -/
def tahii : Noun := ⟨⟨"tahii", "sea"⟩, .a, none⟩

/-- *huan* 'rain'. -/
def huan : Noun := ⟨⟨"huan", "rain"⟩, .a, none⟩

/-- *uruuru* 'love'. -/
def uruuru : Noun := ⟨⟨"uruuru", "love"⟩, .a, none⟩

/-- *inu* 'house'. -/
def inu : Noun := ⟨⟨"inu", "house"⟩, .a, none⟩

/-! ### The o-class -/

/-- *overe* 'coconut palm', the plant. -/
def overePalm : Noun := ⟨⟨"overe", "coconut palm"⟩, .o, none⟩

/-- *pauna* 'banana tree', the plant. -/
def paunaTree : Noun := ⟨⟨"pauna", "banana tree"⟩, .o, none⟩

/-- *paka* 'leaf'. -/
def paka : Noun := ⟨⟨"paka", "leaf"⟩, .o, none⟩

/-- *pus* 'stump'. -/
def pus : Noun := ⟨⟨"pus", "stump"⟩, .o, none⟩

/-- *hinahoo* 'taro planting stick'. -/
def hinahoo : Noun := ⟨⟨"hinahoo", "taro planting stick"⟩, .o, none⟩

/-- *sinivi* 'canoe'. -/
def sinivi : Noun := ⟨⟨"sinivi", "canoe"⟩, .o, none⟩

/-- *hoi* 'basket'. -/
def hoi : Noun := ⟨⟨"hoi", "basket"⟩, .o, none⟩

/-- *kurita* 'octopus'. -/
def kurita : Noun := ⟨⟨"kurita", "octopus"⟩, .o, none⟩

/-- *demdem* 'snail'. -/
def demdem : Noun := ⟨⟨"demdem", "snail"⟩, .o, none⟩

/-- *paku* 'feast'. -/
def paku : Noun := ⟨⟨"paku", "feast"⟩, .o, none⟩

/-- *suraa* 'fire'. -/
def suraa : Noun := ⟨⟨"suraa", "fire"⟩, .o, none⟩

/-- *giigii* 'shooting star'. -/
def giigii : Noun := ⟨⟨"giigii", "shooting star"⟩, .o, none⟩

/-- *koara* 'language'. -/
def koara : Noun := ⟨⟨"koara", "language"⟩, .o, none⟩

/-! ### Body-part terms -/

/-- *bina* 'spleen'. -/
def bina : Noun := ⟨⟨"bina", "spleen"⟩, .o, none⟩

/-- *vuha* 'heart'. -/
def vuha : Noun := ⟨⟨"vuha", "heart"⟩, .o, none⟩

/-- *kuri* 'hand', *kuri-na* without a possessor. -/
def kuri : Noun := ⟨⟨"kuri", "hand"⟩, .o, none⟩

/-- *iru* 'back of the head'. -/
def iru : Noun := ⟨⟨"iru", "back of the head"⟩, .o, none⟩

/-- *ihu* 'nose', *ihu-na* without a possessor. -/
def ihu : Noun := ⟨⟨"ihu", "nose"⟩, .o, none⟩

/-- *revasin* 'blood'. -/
def revasin : Noun := ⟨⟨"revasin", "blood"⟩, .o, none⟩

/-- *hena* 'name'. -/
def hena : Noun := ⟨⟨"hena", "name"⟩, .o, none⟩

/-- *moo* 'leg', *moo-na* without a possessor outside a compound. -/
def moo : Noun := ⟨⟨"moo", "leg"⟩, .o, none⟩

/-- The body-part terms. -/
def bodyPartTerms : List Noun := [bina, vuha, kuri, iru, ihu, revasin, hena, moo]

end Teop
