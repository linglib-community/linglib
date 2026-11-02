module

public import Linglib.Data.Wordlist.Schema

/-!
# `JackendoffAudring2020`: word forms

Auto-generated from `Linglib/Data/Wordlist/JackendoffAudring2020.json` by `scripts/gen_wordlist.py`.
Do not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
JackendoffAudring2020.Wordlist`.
-/

@[expose] public section

namespace JackendoffAudring2020.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.sing : Lexeme :=
  { id := "sing", languageId := "stan1293", parameterId := "sing" }

def Lexemes.sing_past : Lexeme :=
  { id := "sing_past", languageId := "stan1293", parameterId := "sing_past" }

def Lexemes.string : Lexeme :=
  { id := "string", languageId := "stan1293", parameterId := "string" }

def Lexemes.string_past : Lexeme :=
  { id := "string_past", languageId := "stan1293", parameterId := "string_past" }

def Lexemes.speak_stem : Lexeme :=
  { id := "speak_stem", languageId := "stan1295", parameterId := "speak_stem" }

def Lexemes.speak_stem_present_2_3_sg : Lexeme :=
  { id := "speak_stem_present_2_3_sg", languageId := "stan1295",
    parameterId := "speak_stem_present_2_3_sg" }

def Lexemes.like_a_pig : Lexeme :=
  { id := "like_a_pig", languageId := "stan1293", parameterId := "like_a_pig" }

def Lexemes.like_a_child : Lexeme :=
  { id := "like_a_child", languageId := "stan1293", parameterId := "like_a_child" }

def Lexemes.like_a_slug : Lexeme :=
  { id := "like_a_slug", languageId := "stan1293", parameterId := "like_a_slug" }

def Lexemes.like_a_fool : Lexeme :=
  { id := "like_a_fool", languageId := "stan1293", parameterId := "like_a_fool" }

def Lexemes.toponym : Lexeme :=
  { id := "toponym", languageId := "stan1293", parameterId := "toponym" }

def sing : Form Cell :=
  { id := "jackendoffaudring2020_sing"
    lexeme := Lexemes.sing
    cell := {}
    form := "sing"
    segments := ["s", "ɪ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] }

def sang : Form Cell :=
  { id := "jackendoffaudring2020_sang"
    lexeme := Lexemes.sing_past
    cell := {}
    form := "sang"
    segments := ["s", "æ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] }

def string : Form Cell :=
  { id := "jackendoffaudring2020_string"
    lexeme := Lexemes.string
    cell := {}
    form := "string"
    segments := ["s", "t", "ɹ", "ɪ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] }

def strung : Form Cell :=
  { id := "jackendoffaudring2020_strung"
    lexeme := Lexemes.string_past
    cell := {}
    form := "strung"
    segments := ["s", "t", "ɹ", "ʌ", "ŋ"]
    source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] }

def sprech : Form Cell :=
  { id := "jackendoffaudring2020_sprech"
    lexeme := Lexemes.speak_stem
    cell := {}
    form := "sprech-"
    segments := ["ʃ", "p", "r", "ɛ", "x"]
    source := [
      ⟨"jackendoff-audring-2020", "(43)"⟩
    ] }

def sprich : Form Cell :=
  { id := "jackendoffaudring2020_sprich"
    lexeme := Lexemes.speak_stem_present_2_3_sg
    cell := {}
    form := "sprich-"
    segments := ["ʃ", "p", "r", "ɪ", "x"]
    source := [
      ⟨"jackendoff-audring-2020", "(43)"⟩
    ] }

def piggish : Form Cell :=
  { id := "jackendoffaudring2020_piggish"
    lexeme := Lexemes.like_a_pig
    cell := {}
    form := "piggish"
    morphs := ["pig", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def childish : Form Cell :=
  { id := "jackendoffaudring2020_childish"
    lexeme := Lexemes.like_a_child
    cell := {}
    form := "childish"
    morphs := ["child", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def sluggish : Form Cell :=
  { id := "jackendoffaudring2020_sluggish"
    lexeme := Lexemes.like_a_slug
    cell := {}
    form := "sluggish"
    morphs := ["slug", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1 (5)"⟩
    ] }

def foolish : Form Cell :=
  { id := "jackendoffaudring2020_foolish"
    lexeme := Lexemes.like_a_fool
    cell := {}
    form := "foolish"
    morphs := ["fool", "ish"]
    source := [
      ⟨"jackendoff-audring-2020", "7.8.1"⟩
    ] }

def arrowheadLake : Form Cell :=
  { id := "jackendoffaudring2020_arrowheadLake"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Arrowhead Lake"
    morphs := ["Arrowhead", "Lake"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def loonMountain : Form Cell :=
  { id := "jackendoffaudring2020_loonMountain"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Loon Mountain"
    morphs := ["Loon", "Mountain"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def wissahickonCreek : Form Cell :=
  { id := "jackendoffaudring2020_wissahickonCreek"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Wissahickon Creek"
    morphs := ["Wissahickon", "Creek"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def laurelHill : Form Cell :=
  { id := "jackendoffaudring2020_laurelHill"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Laurel Hill"
    morphs := ["Laurel", "Hill"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def sugarIsland : Form Cell :=
  { id := "jackendoffaudring2020_sugarIsland"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Sugar Island"
    morphs := ["Sugar", "Island"]
    source := [
      ⟨"jackendoff-audring-2020", "(17a)"⟩
    ] }

def mountEverest : Form Cell :=
  { id := "jackendoffaudring2020_mountEverest"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Mount Everest"
    morphs := ["Mount", "Everest"]
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def lakeMichigan : Form Cell :=
  { id := "jackendoffaudring2020_lakeMichigan"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Lake Michigan"
    morphs := ["Lake", "Michigan"]
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def capeCod : Form Cell :=
  { id := "jackendoffaudring2020_capeCod"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Cape Cod"
    morphs := ["Cape", "Cod"]
    source := [
      ⟨"jackendoff-audring-2020", "(17b)"⟩
    ] }

def bayOfFundy : Form Cell :=
  { id := "jackendoffaudring2020_bayOfFundy"
    lexeme := Lexemes.toponym
    cell := {}
    form := "the Bay of Fundy"
    morphs := ["the", "Bay", "of", "Fundy"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def gulfOfStLawrence : Form Cell :=
  { id := "jackendoffaudring2020_gulfOfStLawrence"
    lexeme := Lexemes.toponym
    cell := {}
    form := "the Gulf of St. Lawrence"
    morphs := ["the", "Gulf", "of", "St. Lawrence"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def capeOfGoodHope : Form Cell :=
  { id := "jackendoffaudring2020_capeOfGoodHope"
    lexeme := Lexemes.toponym
    cell := {}
    form := "the Cape of Good Hope"
    morphs := ["the", "Cape", "of", "Good Hope"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def isleOfWight : Form Cell :=
  { id := "jackendoffaudring2020_isleOfWight"
    lexeme := Lexemes.toponym
    cell := {}
    form := "the Isle of Wight"
    morphs := ["the", "Isle", "of", "Wight"]
    source := [
      ⟨"jackendoff-audring-2020", "(17d)"⟩
    ] }

def morrisMountain : Form Cell :=
  { id := "jackendoffaudring2020_morrisMountain"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Morris Mountain"
    morphs := ["Morris", "Mountain"]
    source := [
      ⟨"jackendoff-audring-2020", "2.7"⟩
    ] }

def mountMorris : Form Cell :=
  { id := "jackendoffaudring2020_mountMorris"
    lexeme := Lexemes.toponym
    cell := {}
    form := "Mount Morris"
    morphs := ["Mount", "Morris"]
    source := [
      ⟨"jackendoff-audring-2020", "2.7"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.sing, Lexemes.sing_past, Lexemes.string, Lexemes.string_past,
  Lexemes.speak_stem, Lexemes.speak_stem_present_2_3_sg, Lexemes.like_a_pig, Lexemes.like_a_child,
  Lexemes.like_a_slug, Lexemes.like_a_fool, Lexemes.toponym]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [sing, sang, string, strung, sprech, sprich, piggish, childish,
  sluggish, foolish, arrowheadLake, loonMountain, wissahickonCreek, laurelHill, sugarIsland,
  mountEverest, lakeMichigan, capeCod, bayOfFundy, gulfOfStLawrence, capeOfGoodHope, isleOfWight,
  morrisMountain, mountMorris]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "jackendoffaudring2020_sing_sang", form := sing, target := sang, relation := "past",
    source := [
      ⟨"jackendoff-audring-2020", "(24)"⟩
    ] },
  { id := "jackendoffaudring2020_string_strung", form := string, target := strung,
    relation := "past", source := [
      ⟨"jackendoff-audring-2020", "(26)"⟩
    ] },
  { id := "jackendoffaudring2020_sprech_sprich", form := sprech, target := sprich,
    relation := "present_2_3_sg_stem", source := [
      ⟨"jackendoff-audring-2020", "(45)"⟩
    ] }]

end JackendoffAudring2020.Wordlist
