module

public import Linglib.Data.Wordlist.Schema

/-!
# `Walker2000`: word forms

Auto-generated from `Linglib/Data/Wordlist/Walker2000.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Walker2000.Wordlist`.
-/

@[expose] public section

namespace Walker2000.Wordlist

open CLDF.Wordlist

/-- The values of `Language` the source distinguishes. -/
inductive Language where
  /-- Sundanese, where nasality spreads rightward from a nasal stop through vowels and glottals,
  `Sundanese` in the source. -/
  | sundanese
  /-- The Johore dialect of Malay, where it spreads rightward from a nasal stop through glides as
  well, `Malay (Johore dialect)` in the source. -/
  | malay
  /-- The Kolokuma dialect of Ijo, where it spreads leftward from a nasal consonant or vowel,
  through liquids as well, `Ijo (Kolokuma dialect)` in the source. -/
  | ijo
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.toWet : Lexeme :=
  { id := "toWet", languageId := "sund1252", parameterId := "toWet" }

def Lexemes.how : Lexeme :=
  { id := "how", languageId := "sund1252", parameterId := "how" }

def Lexemes.toBeRich : Lexeme :=
  { id := "toBeRich", languageId := "sund1252", parameterId := "toBeRich" }

def Lexemes.toLove : Lexeme :=
  { id := "toLove", languageId := "sund1252", parameterId := "toLove" }

def Lexemes.toSift : Lexeme :=
  { id := "toSift", languageId := "sund1252", parameterId := "toSift" }

def Lexemes.toSpread : Lexeme :=
  { id := "toSpread", languageId := "sund1252", parameterId := "toSpread" }

def Lexemes.toStare : Lexeme :=
  { id := "toStare", languageId := "sund1252", parameterId := "toStare" }

def Lexemes.toHalve : Lexeme :=
  { id := "toHalve", languageId := "sund1252", parameterId := "toHalve" }

def Lexemes.toPursue : Lexeme :=
  { id := "toPursue", languageId := "sund1252", parameterId := "toPursue" }

def Lexemes.toArrange : Lexeme :=
  { id := "toArrange", languageId := "sund1252", parameterId := "toArrange" }

def Lexemes.toDrink : Lexeme :=
  { id := "toDrink", languageId := "stan1306", variety := "Johore", parameterId := "toDrink" }

def Lexemes.toRise : Lexeme :=
  { id := "toRise", languageId := "stan1306", variety := "Johore", parameterId := "toRise" }

def Lexemes.pardon : Lexeme :=
  { id := "pardon", languageId := "stan1306", variety := "Johore", parameterId := "pardon" }

def Lexemes.centralFocus : Lexeme :=
  { id := "centralFocus", languageId := "stan1306", variety := "Johore",
    parameterId := "centralFocus" }

def Lexemes.stalk : Lexeme :=
  { id := "stalk", languageId := "stan1306", variety := "Johore", parameterId := "stalk" }

def Lexemes.toCapture : Lexeme :=
  { id := "toCapture", languageId := "stan1306", variety := "Johore", parameterId := "toCapture" }

def Lexemes.toCauseToCry : Lexeme :=
  { id := "toCauseToCry", languageId := "stan1306", variety := "Johore",
    parameterId := "toCauseToCry" }

def Lexemes.supervision : Lexeme :=
  { id := "supervision", languageId := "stan1306", variety := "Johore",
    parameterId := "supervision" }

def Lexemes.toEat : Lexeme :=
  { id := "toEat", languageId := "stan1306", variety := "Johore", parameterId := "toEat" }

def Lexemes.breath : Lexeme :=
  { id := "breath", languageId := "izon1238", variety := "Kolokuma", parameterId := "breath" }

def Lexemes.wrestle : Lexeme :=
  { id := "wrestle", languageId := "izon1238", variety := "Kolokuma", parameterId := "wrestle" }

def Lexemes.prepareSugarcane : Lexeme :=
  { id := "prepareSugarcane", languageId := "izon1238", variety := "Kolokuma",
    parameterId := "prepareSugarcane" }

def Lexemes.shake : Lexeme :=
  { id := "shake", languageId := "izon1238", variety := "Kolokuma", parameterId := "shake" }

def Lexemes.five : Lexeme :=
  { id := "five", languageId := "izon1238", variety := "Kolokuma", parameterId := "five" }

def Lexemes.gills : Lexeme :=
  { id := "gills", languageId := "izon1238", variety := "Kolokuma", parameterId := "gills" }

def Lexemes.jug : Lexeme :=
  { id := "jug", languageId := "izon1238", variety := "Kolokuma", parameterId := "jug" }

def Lexemes.loft : Lexeme :=
  { id := "loft", languageId := "izon1238", variety := "Kolokuma", parameterId := "loft" }

def Lexemes.mosquito : Lexeme :=
  { id := "mosquito", languageId := "izon1238", variety := "Kolokuma", parameterId := "mosquito" }

def Lexemes.light : Lexeme :=
  { id := "light", languageId := "izon1238", variety := "Kolokuma", parameterId := "light" }

def toWet : Form Cell :=
  { id := "walker2000_toWet"
    lexeme := Lexemes.toWet
    cell := {}
    form := "ɲãĩãn"
    segments := ["ɲ", "ã", "ĩ", "ã", "n"]
    source := [
      ⟨"walker-2000", "(3a)"⟩
    ] }

def how : Form Cell :=
  { id := "walker2000_how"
    lexeme := Lexemes.how
    cell := {}
    form := "kumãh̃ã"
    segments := ["k", "u", "m", "ã", "h̃", "ã"]
    source := [
      ⟨"walker-2000", "(3b)"⟩
    ] }

def toBeRich : Form Cell :=
  { id := "walker2000_toBeRich"
    lexeme := Lexemes.toBeRich
    cell := {}
    form := "bɤŋh̃ãr"
    segments := ["b", "ɤ", "ŋ", "h̃", "ã", "r"]
    source := [
      ⟨"walker-2000", "(3c)"⟩
    ] }

def toLove : Form Cell :=
  { id := "walker2000_toLove"
    lexeme := Lexemes.toLove
    cell := {}
    form := "mĩʔ̃ãsih"
    segments := ["m", "ĩ", "ʔ̃", "ã", "s", "i", "h"]
    source := [
      ⟨"walker-2000", "(3d)"⟩
    ] }

def toSift : Form Cell :=
  { id := "walker2000_toSift"
    lexeme := Lexemes.toSift
    cell := {}
    form := "ŋãjak"
    segments := ["ŋ", "ã", "j", "a", "k"]
    source := [
      ⟨"walker-2000", "(3e)"⟩
    ] }

def toSpread : Form Cell :=
  { id := "walker2000_toSpread"
    lexeme := Lexemes.toSpread
    cell := {}
    form := "mãwur"
    segments := ["m", "ã", "w", "u", "r"]
    source := [
      ⟨"walker-2000", "(3f)"⟩
    ] }

def toStare : Form Cell :=
  { id := "walker2000_toStare"
    lexeme := Lexemes.toStare
    cell := {}
    form := "mõlohok"
    segments := ["m", "õ", "l", "o", "h", "o", "k"]
    source := [
      ⟨"walker-2000", "(3g)"⟩
    ] }

def toHalve : Form Cell :=
  { id := "walker2000_toHalve"
    lexeme := Lexemes.toHalve
    cell := {}
    form := "mãro"
    segments := ["m", "ã", "r", "o"]
    source := [
      ⟨"walker-2000", "(3h)"⟩
    ] }

def toPursue : Form Cell :=
  { id := "walker2000_toPursue"
    lexeme := Lexemes.toPursue
    cell := {}
    form := "ŋũdag"
    segments := ["ŋ", "ũ", "d", "a", "g"]
    source := [
      ⟨"walker-2000", "(3i)"⟩
    ] }

def toArrange : Form Cell :=
  { id := "walker2000_toArrange"
    lexeme := Lexemes.toArrange
    cell := {}
    form := "ŋãtur"
    segments := ["ŋ", "ã", "t", "u", "r"]
    source := [
      ⟨"walker-2000", "(3j)"⟩
    ] }

def toDrink : Form Cell :=
  { id := "walker2000_toDrink"
    lexeme := Lexemes.toDrink
    cell := {}
    form := "mĩnõm"
    segments := ["m", "ĩ", "n", "õ", "m"]
    source := [
      ⟨"walker-2000", "(4a)"⟩
    ] }

def toRise : Form Cell :=
  { id := "walker2000_toRise"
    lexeme := Lexemes.toRise
    cell := {}
    form := "baŋõn"
    segments := ["b", "a", "ŋ", "õ", "n"]
    source := [
      ⟨"walker-2000", "(4b)"⟩
    ] }

def pardon : Form Cell :=
  { id := "walker2000_pardon"
    lexeme := Lexemes.pardon
    cell := {}
    form := "mãʔ̃ãp"
    segments := ["m", "ã", "ʔ̃", "ã", "p"]
    source := [
      ⟨"walker-2000", "(4c)"⟩
    ] }

def centralFocus : Form Cell :=
  { id := "walker2000_centralFocus"
    lexeme := Lexemes.centralFocus
    cell := {}
    form := "pənə̃ŋãh̃ãn"
    segments := ["p", "ə", "n", "ə̃", "ŋ", "ã", "h̃", "ã", "n"]
    source := [
      ⟨"walker-2000", "(4d)"⟩
    ] }

def stalk : Form Cell :=
  { id := "walker2000_stalk"
    lexeme := Lexemes.stalk
    cell := {}
    form := "mãj̃ãŋ"
    segments := ["m", "ã", "j̃", "ã", "ŋ"]
    source := [
      ⟨"walker-2000", "(4e)"⟩
    ] }

def toCapture : Form Cell :=
  { id := "walker2000_toCapture"
    lexeme := Lexemes.toCapture
    cell := {}
    form := "mə̃nãw̃ãn"
    segments := ["m", "ə̃", "n", "ã", "w̃", "ã", "n"]
    source := [
      ⟨"walker-2000", "(4f)"⟩
    ] }

def toCauseToCry : Form Cell :=
  { id := "walker2000_toCauseToCry"
    lexeme := Lexemes.toCauseToCry
    cell := {}
    form := "mə̃ratappi"
    segments := ["m", "ə̃", "r", "a", "t", "a", "p", "p", "i"]
    source := [
      ⟨"walker-2000", "(4g)"⟩
    ] }

def supervision : Form Cell :=
  { id := "walker2000_supervision"
    lexeme := Lexemes.supervision
    cell := {}
    form := "pəŋãw̃ãsan"
    segments := ["p", "ə", "ŋ", "ã", "w̃", "ã", "s", "a", "n"]
    source := [
      ⟨"walker-2000", "(4h)"⟩
    ] }

def toEat : Form Cell :=
  { id := "walker2000_toEat"
    lexeme := Lexemes.toEat
    cell := {}
    form := "mãkan"
    segments := ["m", "ã", "k", "a", "n"]
    source := [
      ⟨"walker-2000", "(4i)"⟩
    ] }

def breath : Form Cell :=
  { id := "walker2000_breath"
    lexeme := Lexemes.breath
    cell := {}
    form := "ũmba"
    segments := ["ũ", "m", "b", "a"]
    source := [
      ⟨"walker-2000", "(5a)"⟩
    ] }

def wrestle : Form Cell :=
  { id := "walker2000_wrestle"
    lexeme := Lexemes.wrestle
    cell := {}
    form := "ãnda"
    segments := ["ã", "n", "d", "a"]
    source := [
      ⟨"walker-2000", "(5b)"⟩
    ] }

def prepareSugarcane : Form Cell :=
  { id := "walker2000_prepareSugarcane"
    lexeme := Lexemes.prepareSugarcane
    cell := {}
    form := "w̃ãĩ"
    segments := ["w̃", "ã", "ĩ"]
    source := [
      ⟨"walker-2000", "(5c)"⟩
    ] }

def shake : Form Cell :=
  { id := "walker2000_shake"
    lexeme := Lexemes.shake
    cell := {}
    form := "j̃ãɾ̃ĩ"
    segments := ["j̃", "ã", "ɾ̃", "ĩ"]
    source := [
      ⟨"walker-2000", "(5d)"⟩
    ] }

def five : Form Cell :=
  { id := "walker2000_five"
    lexeme := Lexemes.five
    cell := {}
    form := "sɔ̃ɾ̃ɔ̃"
    segments := ["s", "ɔ̃", "ɾ̃", "ɔ̃"]
    source := [
      ⟨"walker-2000", "(5e)"⟩
    ] }

def gills : Form Cell :=
  { id := "walker2000_gills"
    lexeme := Lexemes.gills
    cell := {}
    form := "sãnlo"
    segments := ["s", "ã", "n", "l", "o"]
    source := [
      ⟨"walker-2000", "(5f)"⟩
    ] }

def jug : Form Cell :=
  { id := "walker2000_jug"
    lexeme := Lexemes.jug
    cell := {}
    form := "izõŋgo"
    segments := ["i", "z", "õ", "ŋ", "g", "o"]
    source := [
      ⟨"walker-2000", "(5g)"⟩
    ] }

def loft : Form Cell :=
  { id := "walker2000_loft"
    lexeme := Lexemes.loft
    cell := {}
    form := "abãmu"
    segments := ["a", "b", "ã", "m", "u"]
    source := [
      ⟨"walker-2000", "(5h)"⟩
    ] }

def mosquito : Form Cell :=
  { id := "walker2000_mosquito"
    lexeme := Lexemes.mosquito
    cell := {}
    form := "otõŋgbolo"
    segments := ["o", "t", "õ", "ŋ", "gb", "o", "l", "o"]
    source := [
      ⟨"walker-2000", "(5i)"⟩
    ] }

def light : Form Cell :=
  { id := "walker2000_light"
    lexeme := Lexemes.light
    cell := {}
    form := "tɔ̃nĩ"
    segments := ["t", "ɔ̃", "n", "ĩ"]
    source := [
      ⟨"walker-2000", "(5j)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Language` column, the language of the form. -/
  language : Language
  deriving DecidableEq, Repr

def toWet.analysis : Analysis :=
  { form := toWet,
    language := Language.sundanese }

def how.analysis : Analysis :=
  { form := how,
    language := Language.sundanese }

def toBeRich.analysis : Analysis :=
  { form := toBeRich,
    language := Language.sundanese }

def toLove.analysis : Analysis :=
  { form := toLove,
    language := Language.sundanese }

def toSift.analysis : Analysis :=
  { form := toSift,
    language := Language.sundanese }

def toSpread.analysis : Analysis :=
  { form := toSpread,
    language := Language.sundanese }

def toStare.analysis : Analysis :=
  { form := toStare,
    language := Language.sundanese }

def toHalve.analysis : Analysis :=
  { form := toHalve,
    language := Language.sundanese }

def toPursue.analysis : Analysis :=
  { form := toPursue,
    language := Language.sundanese }

def toArrange.analysis : Analysis :=
  { form := toArrange,
    language := Language.sundanese }

def toDrink.analysis : Analysis :=
  { form := toDrink,
    language := Language.malay }

def toRise.analysis : Analysis :=
  { form := toRise,
    language := Language.malay }

def pardon.analysis : Analysis :=
  { form := pardon,
    language := Language.malay }

def centralFocus.analysis : Analysis :=
  { form := centralFocus,
    language := Language.malay }

def stalk.analysis : Analysis :=
  { form := stalk,
    language := Language.malay }

def toCapture.analysis : Analysis :=
  { form := toCapture,
    language := Language.malay }

def toCauseToCry.analysis : Analysis :=
  { form := toCauseToCry,
    language := Language.malay }

def supervision.analysis : Analysis :=
  { form := supervision,
    language := Language.malay }

def toEat.analysis : Analysis :=
  { form := toEat,
    language := Language.malay }

def breath.analysis : Analysis :=
  { form := breath,
    language := Language.ijo }

def wrestle.analysis : Analysis :=
  { form := wrestle,
    language := Language.ijo }

def prepareSugarcane.analysis : Analysis :=
  { form := prepareSugarcane,
    language := Language.ijo }

def shake.analysis : Analysis :=
  { form := shake,
    language := Language.ijo }

def five.analysis : Analysis :=
  { form := five,
    language := Language.ijo }

def gills.analysis : Analysis :=
  { form := gills,
    language := Language.ijo }

def jug.analysis : Analysis :=
  { form := jug,
    language := Language.ijo }

def loft.analysis : Analysis :=
  { form := loft,
    language := Language.ijo }

def mosquito.analysis : Analysis :=
  { form := mosquito,
    language := Language.ijo }

def light.analysis : Analysis :=
  { form := light,
    language := Language.ijo }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.toWet, Lexemes.how, Lexemes.toBeRich, Lexemes.toLove,
  Lexemes.toSift, Lexemes.toSpread, Lexemes.toStare, Lexemes.toHalve, Lexemes.toPursue,
  Lexemes.toArrange, Lexemes.toDrink, Lexemes.toRise, Lexemes.pardon, Lexemes.centralFocus,
  Lexemes.stalk, Lexemes.toCapture, Lexemes.toCauseToCry, Lexemes.supervision, Lexemes.toEat,
  Lexemes.breath, Lexemes.wrestle, Lexemes.prepareSugarcane, Lexemes.shake, Lexemes.five,
  Lexemes.gills, Lexemes.jug, Lexemes.loft, Lexemes.mosquito, Lexemes.light]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [toWet, how, toBeRich, toLove, toSift, toSpread, toStare, toHalve,
  toPursue, toArrange, toDrink, toRise, pardon, centralFocus, stalk, toCapture, toCauseToCry,
  supervision, toEat, breath, wrestle, prepareSugarcane, shake, five, gills, jug, loft, mosquito,
  light]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [toWet.analysis, how.analysis, toBeRich.analysis, toLove.analysis,
  toSift.analysis, toSpread.analysis, toStare.analysis, toHalve.analysis, toPursue.analysis,
  toArrange.analysis, toDrink.analysis, toRise.analysis, pardon.analysis, centralFocus.analysis,
  stalk.analysis, toCapture.analysis, toCauseToCry.analysis, supervision.analysis, toEat.analysis,
  breath.analysis, wrestle.analysis, prepareSugarcane.analysis, shake.analysis, five.analysis,
  gills.analysis, jug.analysis, loft.analysis, mosquito.analysis, light.analysis]

end Walker2000.Wordlist
