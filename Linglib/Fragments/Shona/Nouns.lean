module

public import Linglib.Semantics.Reference.Animacy
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Shona.Basic

/-!
# Shona nouns

Nouns of the class system, each with its gender and the kind of entity it denotes: the lexicon
behind the conjoined-subject agreement data of Carstens. The class 12 diminutives *ka-sikana* 'small
girl', *ka-mba* 'small house' are nouns of their own, of the diminutive gender 12/13.

## References

* [carstens-2026]
-/

@[expose] public section

namespace Shona

/-- A noun is a gendered entry, whose gender pairs the singular class of its prefix with a
plural class, together with the animacy of what it denotes. -/
structure Noun extends GenderedNoun Gender where
  /-- The animacy of what the noun denotes. -/
  animacy : Animacy
  deriving DecidableEq, Repr

namespace Nouns

/-- *murume* 'man'. -/
def murume : Noun := { form := "murume", gloss := "man", gender := .genderA, animacy := .human }
/-- *mukadzi* 'woman'. -/
def mukadzi : Noun := { form := "mukadzi", gloss := "woman", gender := .genderA, animacy := .human }
/-- *musikana* 'girl'. -/
def musikana : Noun :=
  { form := "musikana", gloss := "girl", gender := .genderA, animacy := .human }
/-- *munwe* 'finger'. -/
def munwe : Noun :=
  { form := "munwe", gloss := "finger", gender := .genderB, animacy := .inanimate }
/-- *muromo* 'mouth'. -/
def muromo : Noun :=
  { form := "muromo", gloss := "mouth", gender := .genderB, animacy := .inanimate }
/-- *dombo* 'stone'. -/
def dombo : Noun := { form := "dombo", gloss := "stone", gender := .genderC, animacy := .inanimate }
/-- *zai* 'egg'. -/
def zai : Noun := { form := "zai", gloss := "egg", gender := .genderC, animacy := .inanimate }
/-- *benzi* 'fool'. -/
def benzi : Noun := { form := "benzi", gloss := "fool", gender := .genderC, animacy := .human }
/-- *dinga* 'dimwit'. -/
def dinga : Noun := { form := "dinga", gloss := "dimwit", gender := .genderC, animacy := .human }
/-- *chingwa* 'bread'. -/
def chingwa : Noun :=
  { form := "chingwa", gloss := "bread", gender := .genderD, animacy := .inanimate }
/-- *chibage* 'maize'. -/
def chibage : Noun :=
  { form := "chibage", gloss := "maize", gender := .genderD, animacy := .inanimate }
/-- *chidhakwa* 'drunkard'. -/
def chidhakwa : Noun :=
  { form := "chidhakwa", gloss := "drunkard", gender := .genderD, animacy := .human }
/-- *chikomana* 'small boy'. -/
def chikomana : Noun :=
  { form := "chikomana", gloss := "small boy", gender := .genderD, animacy := .human }
/-- *nherera* 'orphan'. -/
def nherera : Noun :=
  { form := "nherera", gloss := "orphan", gender := .genderE, animacy := .human }
/-- *nyanzvi* 'expert'. -/
def nyanzvi : Noun :=
  { form := "nyanzvi", gloss := "expert", gender := .genderE, animacy := .human }
/-- *imbwa* 'dog'. -/
def imbwa : Noun := { form := "imbwa", gloss := "dog", gender := .genderE, animacy := .animate }
/-- *mhou* 'cow'. -/
def mhou : Noun := { form := "mhou", gloss := "cow", gender := .genderE, animacy := .animate }
/-- *mhuno* 'nose'. -/
def mhuno : Noun := { form := "mhuno", gloss := "nose", gender := .genderE, animacy := .inanimate }
/-- *nzeve* 'ear'. -/
def nzeve : Noun := { form := "nzeve", gloss := "ear", gender := .genderE, animacy := .inanimate }
/-- *mbiya* 'bowl'. -/
def mbiya : Noun := { form := "mbiya", gloss := "bowl", gender := .genderE, animacy := .inanimate }
/-- *sando* 'hammer'. -/
def sando : Noun :=
  { form := "sando", gloss := "hammer", gender := .genderE, animacy := .inanimate }
/-- *nyota* 'thirst'. -/
def nyota : Noun :=
  { form := "nyota", gloss := "thirst", gender := .genderE, animacy := .inanimate }
/-- *nzara* 'hunger'. -/
def nzara : Noun :=
  { form := "nzara", gloss := "hunger", gender := .genderE, animacy := .inanimate }
/-- *rukova* 'stream'. -/
def rukova : Noun :=
  { form := "rukova", gloss := "stream", gender := .genderF, animacy := .inanimate }
/-- *uta* 'bow'. -/
def uta : Noun := { form := "uta", gloss := "bow", gender := .genderG, animacy := .inanimate }
/-- *utanho* 'ladder'. -/
def utanho : Noun :=
  { form := "utanho", gloss := "ladder", gender := .genderG, animacy := .inanimate }
/-- *kasikana* 'small girl'. -/
def kasikana : Noun :=
  { form := "kasikana", gloss := "small girl", gender := .genderH, animacy := .human }
/-- *kakomana* 'small boy'. -/
def kakomana : Noun :=
  { form := "kakomana", gloss := "small boy", gender := .genderH, animacy := .human }
/-- *kamba* 'small house'. -/
def kamba : Noun :=
  { form := "kamba", gloss := "small house", gender := .genderH, animacy := .inanimate }
/-- *kamotokari* 'small car'. -/
def kamotokari : Noun :=
  { form := "kamotokari", gloss := "small car", gender := .genderH, animacy := .inanimate }

def all : List Noun :=
  [murume, mukadzi, musikana, munwe, muromo, dombo, zai, benzi, dinga, chingwa, chibage,
    chidhakwa, chikomana, nherera, nyanzvi, imbwa, mhou, mhuno, nzeve, mbiya, sando, nyota,
    nzara, rukova, uta, utanho, kasikana, kakomana, kamba, kamotokari]

end Nouns

end Shona
