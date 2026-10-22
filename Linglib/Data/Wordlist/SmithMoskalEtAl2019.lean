module

public import Linglib.Data.Wordlist.Schema

/-!
# `SmithMoskalEtAl2019`: word forms

Auto-generated from `Linglib/Data/Wordlist/SmithMoskalEtAl2019.json` by `scripts/gen_wordlist.py`.
Do not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
SmithMoskalEtAl2019.Wordlist`.
-/

@[expose] public section

namespace SmithMoskalEtAl2019.Wordlist

open CLDF.Wordlist

/-- The values of `Base` the source distinguishes. -/
inductive Base where
  /-- The base of the first cell, `A` in the source. -/
  | a
  /-- A second base, `B` in the source. -/
  | b
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.x_3sg_abs : Lexeme :=
  { id := "x_3sg_abs", languageId := "ward1246", parameterId := "3sg_abs" }

def Lexemes.x_3sg_erg : Lexeme :=
  { id := "x_3sg_erg", languageId := "ward1246", parameterId := "3sg_erg" }

def Lexemes.x_3sg_dat : Lexeme :=
  { id := "x_3sg_dat", languageId := "ward1246", parameterId := "3sg_dat" }

def Lexemes.x_2sg_abs : Lexeme :=
  { id := "x_2sg_abs", languageId := "khin1240", parameterId := "2sg_abs" }

def Lexemes.x_2sg_erg : Lexeme :=
  { id := "x_2sg_erg", languageId := "khin1240", parameterId := "2sg_erg" }

def Lexemes.x_2sg_dat : Lexeme :=
  { id := "x_2sg_dat", languageId := "khin1240", parameterId := "2sg_dat" }

def Lexemes.x_2sg_abs_arch1244 : Lexeme :=
  { id := "x_2sg_abs_arch1244", languageId := "arch1244", parameterId := "2sg_abs" }

def Lexemes.x_2sg_erg_arch1244 : Lexeme :=
  { id := "x_2sg_erg_arch1244", languageId := "arch1244", parameterId := "2sg_erg" }

def Lexemes.x_2sg_dat_arch1244 : Lexeme :=
  { id := "x_2sg_dat_arch1244", languageId := "arch1244", parameterId := "2sg_dat" }

def Lexemes.x_1sg_nom : Lexeme :=
  { id := "x_1sg_nom", languageId := "icel1247", parameterId := "1sg_nom" }

def Lexemes.x_1sg_acc : Lexeme :=
  { id := "x_1sg_acc", languageId := "icel1247", parameterId := "1sg_acc" }

def Lexemes.x_1sg_dat : Lexeme :=
  { id := "x_1sg_dat", languageId := "icel1247", parameterId := "1sg_dat" }

def Lexemes.x_1sg_nom_russ1263 : Lexeme :=
  { id := "x_1sg_nom_russ1263", languageId := "russ1263", parameterId := "1sg_nom" }

def Lexemes.x_1sg_acc_russ1263 : Lexeme :=
  { id := "x_1sg_acc_russ1263", languageId := "russ1263", parameterId := "1sg_acc" }

def Lexemes.x_1sg_dat_russ1263 : Lexeme :=
  { id := "x_1sg_dat_russ1263", languageId := "russ1263", parameterId := "1sg_dat" }

def Lexemes.x_1sg_abs : Lexeme :=
  { id := "x_1sg_abs", languageId := "lezg1247", parameterId := "1sg_abs" }

def Lexemes.x_1sg_erg : Lexeme :=
  { id := "x_1sg_erg", languageId := "lezg1247", parameterId := "1sg_erg" }

def Lexemes.x_1sg_dat_lezg1247 : Lexeme :=
  { id := "x_1sg_dat_lezg1247", languageId := "lezg1247", parameterId := "1sg_dat" }

def Lexemes.x_1_sg : Lexeme :=
  { id := "x_1_sg", languageId := "awtu1239", parameterId := "1_sg" }

def Lexemes.x_1_pl : Lexeme :=
  { id := "x_1_pl", languageId := "awtu1239", parameterId := "1_pl" }

def Lexemes.x_1_dl : Lexeme :=
  { id := "x_1_dl", languageId := "awtu1239", parameterId := "1_dl" }

def Lexemes.x_2_sg : Lexeme :=
  { id := "x_2_sg", languageId := "yagu1244", parameterId := "2_sg" }

def Lexemes.x_2_pl : Lexeme :=
  { id := "x_2_pl", languageId := "yagu1244", parameterId := "2_pl" }

def Lexemes.x_2_dl : Lexeme :=
  { id := "x_2_dl", languageId := "yagu1244", parameterId := "2_dl" }

def Lexemes.x_1incl_sg : Lexeme :=
  { id := "x_1incl_sg", languageId := "wamb1258", parameterId := "1incl_sg" }

def Lexemes.x_1incl_pl : Lexeme :=
  { id := "x_1incl_pl", languageId := "wamb1258", parameterId := "1incl_pl" }

def Lexemes.x_1incl_dl : Lexeme :=
  { id := "x_1incl_dl", languageId := "wamb1258", parameterId := "1incl_dl" }

def Lexemes.x_3m_sg : Lexeme :=
  { id := "x_3m_sg", languageId := "dehu1237", parameterId := "3m_sg" }

def Lexemes.x_3m_pl : Lexeme :=
  { id := "x_3m_pl", languageId := "dehu1237", parameterId := "3m_pl" }

def Lexemes.x_3m_dl : Lexeme :=
  { id := "x_3m_dl", languageId := "dehu1237", parameterId := "3m_dl" }

def wardaman_3sg_abs : Form Cell :=
  { id := "smithmoskaletal2019_wardaman_3sg_abs"
    lexeme := Lexemes.x_3sg_abs
    cell := {}
    form := "narnaj"
    segments := ["narnaj"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 25"⟩
    ] }

def wardaman_3sg_erg : Form Cell :=
  { id := "smithmoskaletal2019_wardaman_3sg_erg"
    lexeme := Lexemes.x_3sg_erg
    cell := {}
    form := "narnaj-(j)i"
    segments := ["narnaj", "(j)i"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 25"⟩
    ] }

def wardaman_3sg_dat : Form Cell :=
  { id := "smithmoskaletal2019_wardaman_3sg_dat"
    lexeme := Lexemes.x_3sg_dat
    cell := {}
    form := "gunga"
    segments := ["gunga"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 25"⟩
    ] }

def khinalugh_2sg_abs : Form Cell :=
  { id := "smithmoskaletal2019_khinalugh_2sg_abs"
    lexeme := Lexemes.x_2sg_abs
    cell := {}
    form := "vɨ"
    segments := ["vɨ"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 24"⟩
    ] }

def khinalugh_2sg_erg : Form Cell :=
  { id := "smithmoskaletal2019_khinalugh_2sg_erg"
    lexeme := Lexemes.x_2sg_erg
    cell := {}
    form := "va"
    segments := ["va"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 24"⟩
    ] }

def khinalugh_2sg_dat : Form Cell :=
  { id := "smithmoskaletal2019_khinalugh_2sg_dat"
    lexeme := Lexemes.x_2sg_dat
    cell := {}
    form := "oX(ɨr)"
    segments := ["oX(ɨr)"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 24"⟩
    ] }

def archi_2sg_abs : Form Cell :=
  { id := "smithmoskaletal2019_archi_2sg_abs"
    lexeme := Lexemes.x_2sg_abs_arch1244
    cell := {}
    form := "un"
    segments := ["un"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 20"⟩
    ] }

def archi_2sg_erg : Form Cell :=
  { id := "smithmoskaletal2019_archi_2sg_erg"
    lexeme := Lexemes.x_2sg_erg_arch1244
    cell := {}
    form := "un"
    segments := ["un"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 20"⟩
    ] }

def archi_2sg_dat : Form Cell :=
  { id := "smithmoskaletal2019_archi_2sg_dat"
    lexeme := Lexemes.x_2sg_dat_arch1244
    cell := {}
    form := "wa-s"
    segments := ["wa", "s"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 20"⟩
    ] }

def icelandic_1sg_nom : Form Cell :=
  { id := "smithmoskaletal2019_icelandic_1sg_nom"
    lexeme := Lexemes.x_1sg_nom
    cell := {}
    form := "ég"
    segments := ["ég"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 6"⟩
    ] }

def icelandic_1sg_acc : Form Cell :=
  { id := "smithmoskaletal2019_icelandic_1sg_acc"
    lexeme := Lexemes.x_1sg_acc
    cell := {}
    form := "mig"
    segments := ["mig"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 6"⟩
    ] }

def icelandic_1sg_dat : Form Cell :=
  { id := "smithmoskaletal2019_icelandic_1sg_dat"
    lexeme := Lexemes.x_1sg_dat
    cell := {}
    form := "mér"
    segments := ["mér"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 6"⟩
    ] }

def russian_1sg_nom : Form Cell :=
  { id := "smithmoskaletal2019_russian_1sg_nom"
    lexeme := Lexemes.x_1sg_nom_russ1263
    cell := {}
    form := "ja"
    segments := ["ja"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 10"⟩
    ] }

def russian_1sg_acc : Form Cell :=
  { id := "smithmoskaletal2019_russian_1sg_acc"
    lexeme := Lexemes.x_1sg_acc_russ1263
    cell := {}
    form := "menja"
    segments := ["menja"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 10"⟩
    ] }

def russian_1sg_dat : Form Cell :=
  { id := "smithmoskaletal2019_russian_1sg_dat"
    lexeme := Lexemes.x_1sg_dat_russ1263
    cell := {}
    form := "mnje"
    segments := ["mnje"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 10"⟩
    ] }

def lezgian_1sg_abs : Form Cell :=
  { id := "smithmoskaletal2019_lezgian_1sg_abs"
    lexeme := Lexemes.x_1sg_abs
    cell := {}
    form := "zun"
    segments := ["zun"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 11"⟩
    ] }

def lezgian_1sg_erg : Form Cell :=
  { id := "smithmoskaletal2019_lezgian_1sg_erg"
    lexeme := Lexemes.x_1sg_erg
    cell := {}
    form := "za"
    segments := ["za"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 11"⟩
    ] }

def lezgian_1sg_dat : Form Cell :=
  { id := "smithmoskaletal2019_lezgian_1sg_dat"
    lexeme := Lexemes.x_1sg_dat_lezg1247
    cell := {}
    form := "zaz"
    segments := ["zaz"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 11"⟩
    ] }

def awtuw_1_sg : Form Cell :=
  { id := "smithmoskaletal2019_awtuw_1_sg"
    lexeme := Lexemes.x_1_sg
    cell := {}
    form := "wan"
    segments := ["wan"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 33"⟩
    ] }

def awtuw_1_pl : Form Cell :=
  { id := "smithmoskaletal2019_awtuw_1_pl"
    lexeme := Lexemes.x_1_pl
    cell := {}
    form := "nom"
    segments := ["nom"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 33"⟩
    ] }

def awtuw_1_dl : Form Cell :=
  { id := "smithmoskaletal2019_awtuw_1_dl"
    lexeme := Lexemes.x_1_dl
    cell := {}
    form := "nan"
    segments := ["nan"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 33"⟩
    ] }

def yagua_2_sg : Form Cell :=
  { id := "smithmoskaletal2019_yagua_2_sg"
    lexeme := Lexemes.x_2_sg
    cell := {}
    form := "jiy"
    segments := ["jiy"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def yagua_2_pl : Form Cell :=
  { id := "smithmoskaletal2019_yagua_2_pl"
    lexeme := Lexemes.x_2_pl
    cell := {}
    form := "jiryéy"
    segments := ["jiryéy"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def yagua_2_dl : Form Cell :=
  { id := "smithmoskaletal2019_yagua_2_dl"
    lexeme := Lexemes.x_2_dl
    cell := {}
    form := "sááda"
    segments := ["sááda"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def wambaya_1incl_sg : Form Cell :=
  { id := "smithmoskaletal2019_wambaya_1incl_sg"
    lexeme := Lexemes.x_1incl_sg
    cell := {}
    form := "ngawu(rniji)"
    segments := ["ngawu(rniji)"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def wambaya_1incl_pl : Form Cell :=
  { id := "smithmoskaletal2019_wambaya_1incl_pl"
    lexeme := Lexemes.x_1incl_pl
    cell := {}
    form := "ngurruwani"
    segments := ["ngurruwani"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def wambaya_1incl_dl : Form Cell :=
  { id := "smithmoskaletal2019_wambaya_1incl_dl"
    lexeme := Lexemes.x_1incl_dl
    cell := {}
    form := "mrindiyani"
    segments := ["mrindiyani"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def dehu_3m_sg : Form Cell :=
  { id := "smithmoskaletal2019_dehu_3m_sg"
    lexeme := Lexemes.x_3m_sg
    cell := {}
    form := "angeice"
    segments := ["angeice"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def dehu_3m_pl : Form Cell :=
  { id := "smithmoskaletal2019_dehu_3m_pl"
    lexeme := Lexemes.x_3m_pl
    cell := {}
    form := "angate"
    segments := ["angate"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

def dehu_3m_dl : Form Cell :=
  { id := "smithmoskaletal2019_dehu_3m_dl"
    lexeme := Lexemes.x_3m_dl
    cell := {}
    form := "nyido"
    segments := ["nyido"]
    source := [
      ⟨"smith-moskal-xu-kang-bobaljik-2019", "Table 46"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Base` column. -/
  base : Base
  deriving DecidableEq, Repr

def wardaman_3sg_abs.analysis : Analysis :=
  { form := wardaman_3sg_abs,
    base := Base.a }

def wardaman_3sg_erg.analysis : Analysis :=
  { form := wardaman_3sg_erg,
    base := Base.a }

def wardaman_3sg_dat.analysis : Analysis :=
  { form := wardaman_3sg_dat,
    base := Base.b }

def khinalugh_2sg_abs.analysis : Analysis :=
  { form := khinalugh_2sg_abs,
    base := Base.a }

def khinalugh_2sg_erg.analysis : Analysis :=
  { form := khinalugh_2sg_erg,
    base := Base.a }

def khinalugh_2sg_dat.analysis : Analysis :=
  { form := khinalugh_2sg_dat,
    base := Base.b }

def archi_2sg_abs.analysis : Analysis :=
  { form := archi_2sg_abs,
    base := Base.a }

def archi_2sg_erg.analysis : Analysis :=
  { form := archi_2sg_erg,
    base := Base.a }

def archi_2sg_dat.analysis : Analysis :=
  { form := archi_2sg_dat,
    base := Base.b }

def icelandic_1sg_nom.analysis : Analysis :=
  { form := icelandic_1sg_nom,
    base := Base.a }

def icelandic_1sg_acc.analysis : Analysis :=
  { form := icelandic_1sg_acc,
    base := Base.b }

def icelandic_1sg_dat.analysis : Analysis :=
  { form := icelandic_1sg_dat,
    base := Base.b }

def russian_1sg_nom.analysis : Analysis :=
  { form := russian_1sg_nom,
    base := Base.a }

def russian_1sg_acc.analysis : Analysis :=
  { form := russian_1sg_acc,
    base := Base.b }

def russian_1sg_dat.analysis : Analysis :=
  { form := russian_1sg_dat,
    base := Base.b }

def lezgian_1sg_abs.analysis : Analysis :=
  { form := lezgian_1sg_abs,
    base := Base.a }

def lezgian_1sg_erg.analysis : Analysis :=
  { form := lezgian_1sg_erg,
    base := Base.a }

def lezgian_1sg_dat.analysis : Analysis :=
  { form := lezgian_1sg_dat,
    base := Base.a }

def awtuw_1_sg.analysis : Analysis :=
  { form := awtuw_1_sg,
    base := Base.a }

def awtuw_1_pl.analysis : Analysis :=
  { form := awtuw_1_pl,
    base := Base.b }

def awtuw_1_dl.analysis : Analysis :=
  { form := awtuw_1_dl,
    base := Base.b }

def yagua_2_sg.analysis : Analysis :=
  { form := yagua_2_sg,
    base := Base.a }

def yagua_2_pl.analysis : Analysis :=
  { form := yagua_2_pl,
    base := Base.a }

def yagua_2_dl.analysis : Analysis :=
  { form := yagua_2_dl,
    base := Base.b }

def wambaya_1incl_sg.analysis : Analysis :=
  { form := wambaya_1incl_sg,
    base := Base.a }

def wambaya_1incl_pl.analysis : Analysis :=
  { form := wambaya_1incl_pl,
    base := Base.a }

def wambaya_1incl_dl.analysis : Analysis :=
  { form := wambaya_1incl_dl,
    base := Base.b }

def dehu_3m_sg.analysis : Analysis :=
  { form := dehu_3m_sg,
    base := Base.a }

def dehu_3m_pl.analysis : Analysis :=
  { form := dehu_3m_pl,
    base := Base.a }

def dehu_3m_dl.analysis : Analysis :=
  { form := dehu_3m_dl,
    base := Base.b }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.x_3sg_abs, Lexemes.x_3sg_erg, Lexemes.x_3sg_dat,
  Lexemes.x_2sg_abs, Lexemes.x_2sg_erg, Lexemes.x_2sg_dat, Lexemes.x_2sg_abs_arch1244,
  Lexemes.x_2sg_erg_arch1244, Lexemes.x_2sg_dat_arch1244, Lexemes.x_1sg_nom, Lexemes.x_1sg_acc,
  Lexemes.x_1sg_dat, Lexemes.x_1sg_nom_russ1263, Lexemes.x_1sg_acc_russ1263,
  Lexemes.x_1sg_dat_russ1263, Lexemes.x_1sg_abs, Lexemes.x_1sg_erg, Lexemes.x_1sg_dat_lezg1247,
  Lexemes.x_1_sg, Lexemes.x_1_pl, Lexemes.x_1_dl, Lexemes.x_2_sg, Lexemes.x_2_pl, Lexemes.x_2_dl,
  Lexemes.x_1incl_sg, Lexemes.x_1incl_pl, Lexemes.x_1incl_dl, Lexemes.x_3m_sg, Lexemes.x_3m_pl,
  Lexemes.x_3m_dl]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [wardaman_3sg_abs, wardaman_3sg_erg, wardaman_3sg_dat,
  khinalugh_2sg_abs, khinalugh_2sg_erg, khinalugh_2sg_dat, archi_2sg_abs, archi_2sg_erg,
  archi_2sg_dat, icelandic_1sg_nom, icelandic_1sg_acc, icelandic_1sg_dat, russian_1sg_nom,
  russian_1sg_acc, russian_1sg_dat, lezgian_1sg_abs, lezgian_1sg_erg, lezgian_1sg_dat, awtuw_1_sg,
  awtuw_1_pl, awtuw_1_dl, yagua_2_sg, yagua_2_pl, yagua_2_dl, wambaya_1incl_sg, wambaya_1incl_pl,
  wambaya_1incl_dl, dehu_3m_sg, dehu_3m_pl, dehu_3m_dl]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [wardaman_3sg_abs.analysis, wardaman_3sg_erg.analysis,
  wardaman_3sg_dat.analysis, khinalugh_2sg_abs.analysis, khinalugh_2sg_erg.analysis,
  khinalugh_2sg_dat.analysis, archi_2sg_abs.analysis, archi_2sg_erg.analysis,
  archi_2sg_dat.analysis, icelandic_1sg_nom.analysis, icelandic_1sg_acc.analysis,
  icelandic_1sg_dat.analysis, russian_1sg_nom.analysis, russian_1sg_acc.analysis,
  russian_1sg_dat.analysis, lezgian_1sg_abs.analysis, lezgian_1sg_erg.analysis,
  lezgian_1sg_dat.analysis, awtuw_1_sg.analysis, awtuw_1_pl.analysis, awtuw_1_dl.analysis,
  yagua_2_sg.analysis, yagua_2_pl.analysis, yagua_2_dl.analysis, wambaya_1incl_sg.analysis,
  wambaya_1incl_pl.analysis, wambaya_1incl_dl.analysis, dehu_3m_sg.analysis, dehu_3m_pl.analysis,
  dehu_3m_dl.analysis]

end SmithMoskalEtAl2019.Wordlist
