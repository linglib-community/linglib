module

public import Linglib.Data.Wordlist.Schema

/-!
# `Jardine2016a`: word forms

Auto-generated from `Linglib/Data/Wordlist/Jardine2016a.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Jardine2016a.Wordlist`.
-/

@[expose] public section

namespace Jardine2016a.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.cup : Lexeme :=
  { id := "cup", languageId := "gand1255", parameterId := "cup" }

def Lexemes.log : Lexeme :=
  { id := "log", languageId := "gand1255", parameterId := "log" }

def Lexemes.book : Lexeme :=
  { id := "book", languageId := "gand1255", parameterId := "book" }

def Lexemes.seller : Lexeme :=
  { id := "seller", languageId := "gand1255", parameterId := "seller" }

def Lexemes.chopper : Lexeme :=
  { id := "chopper", languageId := "gand1255", parameterId := "chopper" }

def Lexemes.cup_seller : Lexeme :=
  { id := "cup_seller", languageId := "gand1255", parameterId := "cup_seller" }

def Lexemes.log_chopper : Lexeme :=
  { id := "log_chopper", languageId := "gand1255", parameterId := "log_chopper" }

def Lexemes.we_were_seen_by_walusimbi : Lexeme :=
  { id := "we_were_seen_by_walusimbi", languageId := "gand1255",
    parameterId := "we_were_seen_by_walusimbi" }

def Lexemes.we_saw_those_of_walusimbi : Lexeme :=
  { id := "we_saw_those_of_walusimbi", languageId := "gand1255",
    parameterId := "we_saw_those_of_walusimbi" }

def Lexemes.we_went_with_those_of_walusimbi : Lexeme :=
  { id := "we_went_with_those_of_walusimbi", languageId := "gand1255",
    parameterId := "we_went_with_those_of_walusimbi" }

def Lexemes.no_gloss_18b : Lexeme :=
  { id := "no_gloss_18b", languageId := "zulu1248", parameterId := "no_gloss_18b" }

def Lexemes.the_handsome_person : Lexeme :=
  { id := "the_handsome_person", languageId := "sara1340", parameterId := "the_handsome_person" }

def Lexemes.the_handsome_man : Lexeme :=
  { id := "the_handsome_man", languageId := "sara1340", parameterId := "the_handsome_man" }

def Lexemes.the_handsome_woman : Lexeme :=
  { id := "the_handsome_woman", languageId := "sara1340", parameterId := "the_handsome_woman" }

def Lexemes.the_iguana_there_has_eggs : Lexeme :=
  { id := "the_iguana_there_has_eggs", languageId := "sara1340",
    parameterId := "the_iguana_there_has_eggs" }

def Lexemes.the_strong_american_man : Lexeme :=
  { id := "the_strong_american_man", languageId := "sara1340",
    parameterId := "the_strong_american_man" }

def f_8_kikopo : Form Cell :=
  { id := "jardine2016a_8_kikopo"
    lexeme := Lexemes.cup
    cell := {}
    form := "kikópo"
    segments := ["k", "i", "k", "ó", "p", "o"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ] }

def f_8_kisiki : Form Cell :=
  { id := "jardine2016a_8_kisiki"
    lexeme := Lexemes.log
    cell := {}
    form := "kisikî"
    segments := ["k", "i", "s", "i", "k", "î"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ] }

def f_8_kitabo : Form Cell :=
  { id := "jardine2016a_8_kitabo"
    lexeme := Lexemes.book
    cell := {}
    form := "kitabo"
    segments := ["k", "i", "t", "a", "b", "o"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ] }

def f_8_mutunda : Form Cell :=
  { id := "jardine2016a_8_mutunda"
    lexeme := Lexemes.seller
    cell := {}
    form := "mutunda"
    segments := ["m", "u", "t", "u", "n", "d", "a"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ] }

def f_8_mutema : Form Cell :=
  { id := "jardine2016a_8_mutema"
    lexeme := Lexemes.chopper
    cell := {}
    form := "mutéma"
    segments := ["m", "u", "t", "é", "m", "a"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ] }

def f_9a : Form Cell :=
  { id := "jardine2016a_9a"
    lexeme := Lexemes.cup_seller
    cell := {}
    form := "mutunda-bikópo"
    segments := ["m", "u", "t", "u", "n", "d", "a", "+", "b", "i", "k", "ó", "p", "o"]
    source := [
      ⟨"jardine-2016a", "(9a)"⟩
    ] }

def f_9b : Form Cell :=
  { id := "jardine2016a_9b"
    lexeme := Lexemes.log_chopper
    cell := {}
    form := "mutémá-bísíkî"
    segments := ["m", "u", "t", "é", "m", "á", "+", "b", "í", "s", "í", "k", "î"]
    source := [
      ⟨"jardine-2016a", "(9b)"⟩
    ] }

def f_10b : Form Cell :=
  { id := "jardine2016a_10b"
    lexeme := Lexemes.we_were_seen_by_walusimbi
    cell := {}
    form := "tw-áá-láb-wá wálúsimbi"
    segments := ["t", "w", "+", "á", "á", "+", "l", "á", "b", "+", "w", "á", "_", "w", "á", "l",
      "ú", "s", "i", "m", "b", "i"]
    source := [
      ⟨"jardine-2016a", "(10b)"⟩
    ] }

def f_12a : Form Cell :=
  { id := "jardine2016a_12a"
    lexeme := Lexemes.we_saw_those_of_walusimbi
    cell := {}
    form := "tw-áá-láb-á byáá-wálúsimbi"
    segments := ["t", "w", "+", "á", "á", "+", "l", "á", "b", "+", "á", "_", "b", "y", "á", "á",
      "+", "w", "á", "l", "ú", "s", "i", "m", "b", "i"]
    source := [
      ⟨"jardine-2016a", "(12a)"⟩
    ] }

def f_12b : Form Cell :=
  { id := "jardine2016a_12b"
    lexeme := Lexemes.we_went_with_those_of_walusimbi
    cell := {}
    form := "tw-áá-génd-á ná=byáá=bá=wálúsimbi"
    segments := ["t", "w", "+", "á", "á", "+", "g", "é", "n", "d", "+", "á", "_", "n", "á", "+",
      "b", "y", "á", "á", "+", "b", "á", "+", "w", "á", "l", "ú", "s", "i", "m", "b", "i"]
    source := [
      ⟨"jardine-2016a", "(12b)"⟩
    ] }

def f_18b : Form Cell :=
  { id := "jardine2016a_18b"
    lexeme := Lexemes.no_gloss_18b
    cell := {}
    form := "ámákhósꜜánà"
    segments := ["á", "m", "á", "k", "h", "ó", "s", "ꜜ", "á", "n", "à"]
    source := [
      ⟨"jardine-2016a", "(18b)"⟩
    ] }

def f_21a : Form Cell :=
  { id := "jardine2016a_21a"
    lexeme := Lexemes.the_handsome_person
    cell := {}
    form := "dí hánsò sëmbë"
    segments := ["d", "í", "_", "h", "á", "n", "s", "ò", "_", "s", "ë", "m", "b", "ë"]
    source := [
      ⟨"jardine-2016a", "(21a)"⟩
    ] }

def f_21b : Form Cell :=
  { id := "jardine2016a_21b"
    lexeme := Lexemes.the_handsome_man
    cell := {}
    form := "dí hánsó wómì"
    segments := ["d", "í", "_", "h", "á", "n", "s", "ó", "_", "w", "ó", "m", "ì"]
    source := [
      ⟨"jardine-2016a", "(21b)"⟩
    ] }

def f_21c : Form Cell :=
  { id := "jardine2016a_21c"
    lexeme := Lexemes.the_handsome_woman
    cell := {}
    form := "dí hánsó mújêë"
    segments := ["d", "í", "_", "h", "á", "n", "s", "ó", "_", "m", "ú", "j", "ê", "ë"]
    source := [
      ⟨"jardine-2016a", "(21c)"⟩
    ] }

def f_21d : Form Cell :=
  { id := "jardine2016a_21d"
    lexeme := Lexemes.the_iguana_there_has_eggs
    cell := {}
    form := "dí wájámáká=dé á óbo"
    segments := ["d", "í", "_", "w", "á", "j", "á", "m", "á", "k", "á", "+", "d", "é", "_", "á",
      "_", "ó", "b", "o"]
    source := [
      ⟨"jardine-2016a", "(21d)"⟩
    ] }

def f_21e : Form Cell :=
  { id := "jardine2016a_21e"
    lexeme := Lexemes.the_strong_american_man
    cell := {}
    form := "tàángá ámêêká wómì"
    segments := ["t", "à", "á", "n", "g", "á", "_", "á", "m", "ê", "ê", "k", "á", "_", "w", "ó",
      "m", "ì"]
    source := [
      ⟨"jardine-2016a", "(21e)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Underlying` column. -/
  underlying : String
  /-- The `UnderlyingTones` column. -/
  underlyingTones : String
  /-- The `SurfaceTones` column. -/
  surfaceTones : String
  deriving DecidableEq, Repr

def f_8_kikopo.analysis : Analysis :=
  { form := f_8_kikopo,
    underlying := "/ki-kópo/",
    underlyingTones := "OHO",
    surfaceTones := "OHO" }

def f_8_kisiki.analysis : Analysis :=
  { form := f_8_kisiki,
    underlying := "/ki-sikí/",
    underlyingTones := "OOH",
    surfaceTones := "OOH" }

def f_8_kitabo.analysis : Analysis :=
  { form := f_8_kitabo,
    underlying := "/ki-tabo/",
    underlyingTones := "OOO",
    surfaceTones := "OOO" }

def f_8_mutunda.analysis : Analysis :=
  { form := f_8_mutunda,
    underlying := "/mu-tund-a/",
    underlyingTones := "OOO",
    surfaceTones := "OOO" }

def f_8_mutema.analysis : Analysis :=
  { form := f_8_mutema,
    underlying := "/mu-tém-a/",
    underlyingTones := "OHO",
    surfaceTones := "OHO" }

def f_9a.analysis : Analysis :=
  { form := f_9a,
    underlying := "/mu-tund-a+bi-kópo/",
    underlyingTones := "OOOOHO",
    surfaceTones := "OOOOHO" }

def f_9b.analysis : Analysis :=
  { form := f_9b,
    underlying := "/mu-tém-a+bi-sikí/",
    underlyingTones := "OHOOOH",
    surfaceTones := "OHHHHH" }

def f_10b.analysis : Analysis :=
  { form := f_10b,
    underlying := "/tw-áa-láb-w-a walúsimbi/",
    underlyingTones := "HHHOOHOO",
    surfaceTones := "HHHHHHOO" }

def f_12a.analysis : Analysis :=
  { form := f_12a,
    underlying := "/tw-áa-láb-a byaa=walúsimbi/",
    underlyingTones := "HHHOOOOHOO",
    surfaceTones := "HHHHHHHHOO" }

def f_12b.analysis : Analysis :=
  { form := f_12b,
    underlying := "/tw-áa-génd-a na=byaa=ba=walúsimbi/",
    underlyingTones := "HHHOOOOOOHOO",
    surfaceTones := "HHHHHHHHHHOO" }

def f_18b.analysis : Analysis :=
  { form := f_18b,
    underlying := "/ámàkhòsánà/",
    underlyingTones := "HOOHO",
    surfaceTones := "HHHHO" }

def f_21a.analysis : Analysis :=
  { form := f_21a,
    underlying := "/dí hánso sëmbë/",
    underlyingTones := "HHOOO",
    surfaceTones := "HHOOO" }

def f_21b.analysis : Analysis :=
  { form := f_21b,
    underlying := "/dí hánso wómi/",
    underlyingTones := "HHOHO",
    surfaceTones := "HHHHO" }

def f_21c.analysis : Analysis :=
  { form := f_21c,
    underlying := "/dí hánso mujêE/",
    underlyingTones := "HHOOHO",
    surfaceTones := "HHHHHO" }

def f_21d.analysis : Analysis :=
  { form := f_21d,
    underlying := "/dí wajamáka=dé á óbo/",
    underlyingTones := "HOOHOHHHO",
    surfaceTones := "HHHHHHHHO" }

def f_21e.analysis : Analysis :=
  { form := f_21e,
    underlying := "/taánga amEEká wómi/",
    underlyingTones := "OHOOOOHHO",
    surfaceTones := "OHHHHHHHO" }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.cup, Lexemes.log, Lexemes.book, Lexemes.seller,
  Lexemes.chopper, Lexemes.cup_seller, Lexemes.log_chopper, Lexemes.we_were_seen_by_walusimbi,
  Lexemes.we_saw_those_of_walusimbi, Lexemes.we_went_with_those_of_walusimbi, Lexemes.no_gloss_18b,
  Lexemes.the_handsome_person, Lexemes.the_handsome_man, Lexemes.the_handsome_woman,
  Lexemes.the_iguana_there_has_eggs, Lexemes.the_strong_american_man]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_8_kikopo, f_8_kisiki, f_8_kitabo, f_8_mutunda, f_8_mutema, f_9a,
  f_9b, f_10b, f_12a, f_12b, f_18b, f_21a, f_21b, f_21c, f_21d, f_21e]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [f_8_kikopo.analysis, f_8_kisiki.analysis, f_8_kitabo.analysis,
  f_8_mutunda.analysis, f_8_mutema.analysis, f_9a.analysis, f_9b.analysis, f_10b.analysis,
  f_12a.analysis, f_12b.analysis, f_18b.analysis, f_21a.analysis, f_21b.analysis, f_21c.analysis,
  f_21d.analysis, f_21e.analysis]

end Jardine2016a.Wordlist
