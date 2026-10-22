module

public import Linglib.Data.Wordlist.Schema

/-!
# `Short1993`: word forms

Auto-generated from `Linglib/Data/Wordlist/Short1993.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Short1993.Wordlist`.
-/

@[expose] public section

namespace Short1993.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.dal : Lexeme :=
  { id := "dal", languageId := "czec1258", parameterId := "dal" }

def Lexemes.dal_long : Lexeme :=
  { id := "dal_long", languageId := "czec1258", parameterId := "dal_long" }

def Lexemes.dul : Lexeme :=
  { id := "dul", languageId := "czec1258", parameterId := "dul" }

def Lexemes.dul_long : Lexeme :=
  { id := "dul_long", languageId := "czec1258", parameterId := "dul_long" }

def Lexemes.ryby : Lexeme :=
  { id := "ryby", languageId := "czec1258", parameterId := "ryby" }

def Lexemes.ryby_long : Lexeme :=
  { id := "ryby_long", languageId := "czec1258", parameterId := "ryby_long" }

def Lexemes.sud : Lexeme :=
  { id := "sud", languageId := "czec1258", parameterId := "sud" }

def Lexemes.soud : Lexeme :=
  { id := "soud", languageId := "czec1258", parameterId := "soud" }

def Lexemes.pena : Lexeme :=
  { id := "pena", languageId := "czec1258", parameterId := "pena" }

def Lexemes.veno : Lexeme :=
  { id := "veno", languageId := "czec1258", parameterId := "veno" }

def Lexemes.harfe : Lexeme :=
  { id := "harfe", languageId := "czec1258", parameterId := "harfe" }

def Lexemes.mesto : Lexeme :=
  { id := "mesto", languageId := "czec1258", parameterId := "mesto" }

def Lexemes.obed : Lexeme :=
  { id := "obed", languageId := "czec1258", parameterId := "obed" }

def Lexemes.dabel : Lexeme :=
  { id := "dabel", languageId := "czec1258", parameterId := "dabel" }

def Lexemes.tuhyk : Lexeme :=
  { id := "tuhyk", languageId := "czec1258", parameterId := "tuhyk" }

def Lexemes.mlady : Lexeme :=
  { id := "mlady", languageId := "czec1258", parameterId := "mlady" }

def Lexemes.mladi : Lexeme :=
  { id := "mladi", languageId := "czec1258", parameterId := "mladi" }

def Lexemes.mlade : Lexeme :=
  { id := "mlade", languageId := "czec1258", parameterId := "mlade" }

def Lexemes.kruty : Lexeme :=
  { id := "kruty", languageId := "czec1258", parameterId := "kruty" }

def Lexemes.kruti : Lexeme :=
  { id := "kruti", languageId := "czec1258", parameterId := "kruti" }

def Lexemes.krute : Lexeme :=
  { id := "krute", languageId := "czec1258", parameterId := "krute" }

def Lexemes.plny : Lexeme :=
  { id := "plny", languageId := "czec1258", parameterId := "plny" }

def Lexemes.plne : Lexeme :=
  { id := "plne", languageId := "czec1258", parameterId := "plne" }

def dal : Form Cell :=
  { id := "short1993_dal"
    lexeme := Lexemes.dal
    cell := {}
    form := "dal"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def dal_long : Form Cell :=
  { id := "short1993_dal_long"
    lexeme := Lexemes.dal_long
    cell := {}
    form := "dál"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def dul : Form Cell :=
  { id := "short1993_dul"
    lexeme := Lexemes.dul
    cell := {}
    form := "dul"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def dul_long : Form Cell :=
  { id := "short1993_dul_long"
    lexeme := Lexemes.dul_long
    cell := {}
    form := "důl"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def ryby : Form Cell :=
  { id := "short1993_ryby"
    lexeme := Lexemes.ryby
    cell := {}
    form := "ryby"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def ryby_long : Form Cell :=
  { id := "short1993_ryby_long"
    lexeme := Lexemes.ryby_long
    cell := {}
    form := "rybí"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def sud : Form Cell :=
  { id := "short1993_sud"
    lexeme := Lexemes.sud
    cell := {}
    form := "sud"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def soud : Form Cell :=
  { id := "short1993_soud"
    lexeme := Lexemes.soud
    cell := {}
    form := "soud"
    source := [
      ⟨"short-1993-czech", "p. 456"⟩
    ] }

def pena : Form Cell :=
  { id := "short1993_pena"
    lexeme := Lexemes.pena
    cell := {}
    form := "pěna"
    segments := ["p", "j", "e", "n", "a"]
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def veno : Form Cell :=
  { id := "short1993_veno"
    lexeme := Lexemes.veno
    cell := {}
    form := "věno"
    segments := ["v", "j", "e", "n", "o"]
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def harfe : Form Cell :=
  { id := "short1993_harfe"
    lexeme := Lexemes.harfe
    cell := {}
    form := "harfě"
    segments := ["h", "a", "r", "f", "j", "e"]
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def mesto : Form Cell :=
  { id := "short1993_mesto"
    lexeme := Lexemes.mesto
    cell := {}
    form := "město"
    segments := ["m", "ň", "e", "s", "t", "o"]
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def obed : Form Cell :=
  { id := "short1993_obed"
    lexeme := Lexemes.obed
    cell := {}
    form := "oběd"
    segments := ["o", "b", "j", "e", "t"]
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def dabel : Form Cell :=
  { id := "short1993_dabel"
    lexeme := Lexemes.dabel
    cell := {}
    form := "ďábel"
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def tuhyk : Form Cell :=
  { id := "short1993_tuhyk"
    lexeme := Lexemes.tuhyk
    cell := {}
    form := "ťuhýk"
    source := [
      ⟨"short-1993-czech", "p. 459"⟩
    ] }

def mlady : Form Cell :=
  { id := "short1993_mlady"
    lexeme := Lexemes.mlady
    cell := {}
    form := "mladý"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def mladi : Form Cell :=
  { id := "short1993_mladi"
    lexeme := Lexemes.mladi
    cell := {}
    form := "mladí"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def mlade : Form Cell :=
  { id := "short1993_mlade"
    lexeme := Lexemes.mlade
    cell := {}
    form := "mladě"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def kruty : Form Cell :=
  { id := "short1993_kruty"
    lexeme := Lexemes.kruty
    cell := {}
    form := "krutý"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def kruti : Form Cell :=
  { id := "short1993_kruti"
    lexeme := Lexemes.kruti
    cell := {}
    form := "krutí"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def krute : Form Cell :=
  { id := "short1993_krute"
    lexeme := Lexemes.krute
    cell := {}
    form := "krutě"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def plny : Form Cell :=
  { id := "short1993_plny"
    lexeme := Lexemes.plny
    cell := {}
    form := "plný"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

def plne : Form Cell :=
  { id := "short1993_plne"
    lexeme := Lexemes.plne
    cell := {}
    form := "plně"
    source := [
      ⟨"short-1993-czech", "p. 462"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.dal, Lexemes.dal_long, Lexemes.dul, Lexemes.dul_long,
  Lexemes.ryby, Lexemes.ryby_long, Lexemes.sud, Lexemes.soud, Lexemes.pena, Lexemes.veno,
  Lexemes.harfe, Lexemes.mesto, Lexemes.obed, Lexemes.dabel, Lexemes.tuhyk, Lexemes.mlady,
  Lexemes.mladi, Lexemes.mlade, Lexemes.kruty, Lexemes.kruti, Lexemes.krute, Lexemes.plny,
  Lexemes.plne]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [dal, dal_long, dul, dul_long, ryby, ryby_long, sud, soud, pena, veno,
  harfe, mesto, obed, dabel, tuhyk, mlady, mladi, mlade, kruty, kruti, krute, plny, plne]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end Short1993.Wordlist
