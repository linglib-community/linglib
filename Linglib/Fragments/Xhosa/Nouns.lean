module

public import Linglib.Semantics.Reference.Animacy
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Xhosa.Basic

/-!
# Xhosa nouns

Nouns of the class system, each with its gender and the kind of entity it denotes: the lexicon
behind the conjoined-subject agreement data of Carstens and of Taraldsen and colleagues, and the
deverbal nouns in the nominalizing final vowels -i and -o of Mletshe behind Halpert and Hammerly's
stacked class prefixes. Forms are cited with the augment. Class 1a nouns, *u-L*, *u-loliwe* 'train',
*u-nonkala* 'crab', are entered in gender 1/2, differing from class 1 only in the nominal prefix.

## References

* [carstens-2026]
* [taraldsen-et-al-2018]
* [mletshe-2019]
* [halpert-hammerly-2026]
-/

@[expose] public section

namespace Xhosa

/-- A noun is a gendered entry, whose gender pairs the singular class of its prefix with a
plural class, together with the animacy of what it denotes. -/
structure Noun extends GenderedNoun Gender where
  /-- The animacy of what the noun denotes. -/
  animacy : Animacy
  deriving DecidableEq, Repr

namespace Nouns

/-- *ummi* 'citizen'. -/
def ummi : Noun := { form := "ummi", gloss := "citizen", gender := .genderA, animacy := .human }
/-- *umongameli* 'president'. -/
def umongameli : Noun :=
  { form := "umongameli", gloss := "president", gender := .genderA, animacy := .human }
/-- *umntwana* 'child'. -/
def umntwana : Noun :=
  { form := "umntwana", gloss := "child", gender := .genderA, animacy := .human }
/-- *umfazi* 'woman'. -/
def umfazi : Noun := { form := "umfazi", gloss := "woman", gender := .genderA, animacy := .human }
/-- *uL* 'the letter L'. -/
def uL : Noun :=
  { form := "uL", gloss := "the letter L", gender := .genderA, animacy := .inanimate }
/-- *uM* 'the letter M'. -/
def uM : Noun :=
  { form := "uM", gloss := "the letter M", gender := .genderA, animacy := .inanimate }
/-- *uloliwe* 'train'. -/
def uloliwe : Noun :=
  { form := "uloliwe", gloss := "train", gender := .genderA, animacy := .inanimate }
/-- *umatshini* 'machine'. -/
def umatshini : Noun :=
  { form := "umatshini", gloss := "machine", gender := .genderA, animacy := .inanimate }
/-- *ubhaka* 'backpack'. -/
def ubhaka : Noun :=
  { form := "ubhaka", gloss := "backpack", gender := .genderA, animacy := .inanimate }
/-- *unonkala* 'crab'. -/
def unonkala : Noun :=
  { form := "unonkala", gloss := "crab", gender := .genderA, animacy := .animate }
/-- *ukrebe* 'shark'. -/
def ukrebe : Noun := { form := "ukrebe", gloss := "shark", gender := .genderA, animacy := .animate }
/-- *umgewu* 'criminal'. -/
def umgewu : Noun :=
  { form := "umgewu", gloss := "criminal", gender := .genderB, animacy := .human }
/-- *umlwelwe* 'sick person'. -/
def umlwelwe : Noun :=
  { form := "umlwelwe", gloss := "sick person", gender := .genderB, animacy := .human }
/-- *umgulukudu* 'gangster'. -/
def umgulukudu : Noun :=
  { form := "umgulukudu", gloss := "gangster", gender := .genderB, animacy := .human }
/-- *umnqwazi* 'hat'. -/
def umnqwazi : Noun :=
  { form := "umnqwazi", gloss := "hat", gender := .genderB, animacy := .inanimate }
/-- *umpu* 'gun'. -/
def umpu : Noun := { form := "umpu", gloss := "gun", gender := .genderB, animacy := .inanimate }
/-- *umhlonyane* 'wormwood tree'. -/
def umhlonyane : Noun :=
  { form := "umhlonyane", gloss := "wormwood tree", gender := .genderB, animacy := .inanimate }
/-- *umnquma* 'wild olive'. -/
def umnquma : Noun :=
  { form := "umnquma", gloss := "wild olive", gender := .genderB, animacy := .inanimate }
/-- *umkhonto* 'spear'. -/
def umkhonto : Noun :=
  { form := "umkhonto", gloss := "spear", gender := .genderB, animacy := .inanimate }
/-- *umbhobho* 'pipe'. -/
def umbhobho : Noun :=
  { form := "umbhobho", gloss := "pipe", gender := .genderB, animacy := .inanimate }
/-- *umnqathe* 'carrot'. -/
def umnqathe : Noun :=
  { form := "umnqathe", gloss := "carrot", gender := .genderB, animacy := .inanimate }
/-- *umvundla* 'rabbit'. -/
def umvundla : Noun :=
  { form := "umvundla", gloss := "rabbit", gender := .genderB, animacy := .animate }
/-- *umqhagi* 'rooster'. -/
def umqhagi : Noun :=
  { form := "umqhagi", gloss := "rooster", gender := .genderB, animacy := .animate }
/-- *igqwetha* 'lawyer'. -/
def igqwetha : Noun :=
  { form := "igqwetha", gloss := "lawyer", gender := .genderC, animacy := .human }
/-- *isela* 'thief'. -/
def isela : Noun := { form := "isela", gloss := "thief", gender := .genderC, animacy := .human }
/-- *igorha* 'hero'. -/
def igorha : Noun := { form := "igorha", gloss := "hero", gender := .genderC, animacy := .human }
/-- *ikhoboka* 'slave'. -/
def ikhoboka : Noun :=
  { form := "ikhoboka", gloss := "slave", gender := .genderC, animacy := .human }
/-- *ipolisa* 'policeman'. -/
def ipolisa : Noun :=
  { form := "ipolisa", gloss := "policeman", gender := .genderC, animacy := .human }
/-- *iqanda* 'egg'. -/
def iqanda : Noun := { form := "iqanda", gloss := "egg", gender := .genderC, animacy := .inanimate }
/-- *icepe* 'spoon'. -/
def icepe : Noun := { form := "icepe", gloss := "spoon", gender := .genderC, animacy := .inanimate }
/-- *ilitye* 'stone'. -/
def ilitye : Noun :=
  { form := "ilitye", gloss := "stone", gender := .genderC, animacy := .inanimate }
/-- *icici* 'earring'. -/
def icici : Noun :=
  { form := "icici", gloss := "earring", gender := .genderC, animacy := .inanimate }
/-- *ihobe* 'dove'. -/
def ihobe : Noun := { form := "ihobe", gloss := "dove", gender := .genderC, animacy := .animate }
/-- *isibane* 'lamp'. -/
def isibane : Noun :=
  { form := "isibane", gloss := "lamp", gender := .genderD, animacy := .inanimate }
/-- *isitya* 'dish'. -/
def isitya : Noun :=
  { form := "isitya", gloss := "dish", gender := .genderD, animacy := .inanimate }
/-- *isiXhosa* 'Xhosa'. -/
def isiXhosa : Noun :=
  { form := "isiXhosa", gloss := "Xhosa", gender := .genderD, animacy := .inanimate }
/-- *isiZulu* 'Zulu'. -/
def isiZulu : Noun :=
  { form := "isiZulu", gloss := "Zulu", gender := .genderD, animacy := .inanimate }
/-- *isanuse* 'diviner'. -/
def isanuse : Noun :=
  { form := "isanuse", gloss := "diviner", gender := .genderD, animacy := .human }
/-- *isazi* 'scholar'. -/
def isazi : Noun := { form := "isazi", gloss := "scholar", gender := .genderD, animacy := .human }
/-- *isangoma* 'healer'. -/
def isangoma : Noun :=
  { form := "isangoma", gloss := "healer", gender := .genderD, animacy := .human }
/-- *isibhanxa* 'fool'. -/
def isibhanxa : Noun :=
  { form := "isibhanxa", gloss := "fool", gender := .genderD, animacy := .human }
/-- *isikhova* 'owl'. -/
def isikhova : Noun :=
  { form := "isikhova", gloss := "owl", gender := .genderD, animacy := .animate }
/-- *intombi* 'girl'. -/
def intombi : Noun := { form := "intombi", gloss := "girl", gender := .genderE, animacy := .human }
/-- *imbongi* 'poet'. -/
def imbongi : Noun := { form := "imbongi", gloss := "poet", gender := .genderE, animacy := .human }
/-- *ingcaphephe* 'expert'. -/
def ingcaphephe : Noun :=
  { form := "ingcaphephe", gloss := "expert", gender := .genderE, animacy := .human }
/-- *ingcali* 'specialist'. -/
def ingcali : Noun :=
  { form := "ingcali", gloss := "specialist", gender := .genderE, animacy := .human }
/-- *incwadi* 'book'. -/
def incwadi : Noun :=
  { form := "incwadi", gloss := "book", gender := .genderE, animacy := .inanimate }
/-- *ipeni* 'pen'. -/
def ipeni : Noun := { form := "ipeni", gloss := "pen", gender := .genderE, animacy := .inanimate }
/-- *indlovu* 'elephant'. -/
def indlovu : Noun :=
  { form := "indlovu", gloss := "elephant", gender := .genderE, animacy := .animate }
/-- *ingwe* 'leopard'. -/
def ingwe : Noun := { form := "ingwe", gloss := "leopard", gender := .genderE, animacy := .animate }

/-! ### Deverbal nouns

Nominalizations of *thiml-* 'sneeze' and *khohlel-* 'cough' ([mletshe-2019]): the final vowel -i
forms animate nouns, in class 1 or class 7, and -o and -a inanimate ones. -/

/-- *umthimli* 'sneezer'. -/
def umthimli : Noun :=
  { form := "umthimli", gloss := "sneezer", gender := .genderA, animacy := .human }
/-- *umthimlo* 'manner of sneezing'. -/
def umthimlo : Noun :=
  { form := "umthimlo", gloss := "manner of sneezing", gender := .genderB, animacy := .inanimate }
/-- *isithimli* 'severe sneezer'. -/
def isithimli : Noun :=
  { form := "isithimli", gloss := "severe sneezer", gender := .genderD, animacy := .human }
/-- *umkhohleli* 'coughing person'. -/
def umkhohleli : Noun :=
  { form := "umkhohleli", gloss := "coughing person", gender := .genderA, animacy := .human }
/-- *isikhohleli* 'coughing person'. -/
def isikhohleli : Noun :=
  { form := "isikhohleli", gloss := "coughing person", gender := .genderD, animacy := .human }
/-- *isikhohlela* 'phlegm'. -/
def isikhohlela : Noun :=
  { form := "isikhohlela", gloss := "phlegm", gender := .genderD, animacy := .inanimate }

def all : List Noun :=
  [ummi, umongameli, umntwana, umfazi, uL, uM, uloliwe, umatshini, ubhaka, unonkala, ukrebe,
    umgewu, umlwelwe, umgulukudu, umnqwazi, umpu, umhlonyane, umnquma, umkhonto, umbhobho,
    umnqathe, umvundla, umqhagi, igqwetha, isela, igorha, ikhoboka, ipolisa, iqanda, icepe,
    ilitye, icici, ihobe, isibane, isitya, isiXhosa, isiZulu, isanuse, isazi, isangoma,
    isibhanxa, isikhova, intombi, imbongi, ingcaphephe, ingcali, incwadi, ipeni, indlovu, ingwe,
    umthimli, umthimlo, isithimli, umkhohleli, isikhohleli, isikhohlela]

end Nouns

end Xhosa
