module

public import Linglib.Data.Wordlist.Schema

/-!
# `Jacobs2026`: word forms

Auto-generated from `Linglib/Data/Wordlist/Jacobs2026.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Jacobs2026.Wordlist`.
-/

@[expose] public section

namespace Jacobs2026.Wordlist

open CLDF.Wordlist

/-- The values of `Status` the source distinguishes. -/
inductive Status where
  /-- A form the paper's account derives, `regular` in the source. -/
  | regular
  /-- A later -alis form the paper derives from a [j] formed from a front vowel in hiatus, `glide`
  in the source. -/
  | glide
  /-- A form the paper calls an exception, `exception` in the source. -/
  | exception
  /-- A form the paper reports without accounting for it, `unexplained` in the source. -/
  | unexplained
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.navalis : Lexeme :=
  { id := "navalis", languageId := "lati1261", parameterId := "navalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.natalis : Lexeme :=
  { id := "natalis", languageId := "lati1261", parameterId := "natalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.criminalis : Lexeme :=
  { id := "criminalis", languageId := "lati1261", parameterId := "criminalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.solaris : Lexeme :=
  { id := "solaris", languageId := "lati1261", parameterId := "solaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.militaris : Lexeme :=
  { id := "militaris", languageId := "lati1261", parameterId := "militaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.lunaris : Lexeme :=
  { id := "lunaris", languageId := "lati1261", parameterId := "lunaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.floralis : Lexeme :=
  { id := "floralis", languageId := "lati1261", parameterId := "floralis", pos := ↑UD.UPOS.ADJ }

def Lexemes.lateralis : Lexeme :=
  { id := "lateralis", languageId := "lati1261", parameterId := "lateralis", pos := ↑UD.UPOS.ADJ }

def Lexemes.ridicularis : Lexeme :=
  { id := "ridicularis", languageId := "lati1261", parameterId := "ridicularis",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.tricliniaris : Lexeme :=
  { id := "tricliniaris", languageId := "lati1261", parameterId := "tricliniaris",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.umbilicalis : Lexeme :=
  { id := "umbilicalis", languageId := "lati1261", parameterId := "umbilicalis",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.cloacalis : Lexeme :=
  { id := "cloacalis", languageId := "lati1261", parameterId := "cloacalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.vulcanalis : Lexeme :=
  { id := "vulcanalis", languageId := "lati1261", parameterId := "vulcanalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.intellectualis : Lexeme :=
  { id := "intellectualis", languageId := "lati1261", parameterId := "intellectualis",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.glacialis : Lexeme :=
  { id := "glacialis", languageId := "lati1261", parameterId := "glacialis", pos := ↑UD.UPOS.ADJ }

def Lexemes.localis : Lexeme :=
  { id := "localis", languageId := "lati1261", parameterId := "localis", pos := ↑UD.UPOS.ADJ }

def Lexemes.legalis : Lexeme :=
  { id := "legalis", languageId := "lati1261", parameterId := "legalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.lectualis : Lexeme :=
  { id := "lectualis", languageId := "lati1261", parameterId := "lectualis", pos := ↑UD.UPOS.ADJ }

def Lexemes.pluvialis : Lexeme :=
  { id := "pluvialis", languageId := "lati1261", parameterId := "pluvialis", pos := ↑UD.UPOS.ADJ }

def Lexemes.fluvialis : Lexeme :=
  { id := "fluvialis", languageId := "lati1261", parameterId := "fluvialis", pos := ↑UD.UPOS.ADJ }

def Lexemes.flavialis : Lexeme :=
  { id := "flavialis", languageId := "lati1261", parameterId := "flavialis", pos := ↑UD.UPOS.ADJ }

def Lexemes.lupanaris : Lexeme :=
  { id := "lupanaris", languageId := "lati1261", parameterId := "lupanaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.lapidaris : Lexeme :=
  { id := "lapidaris", languageId := "lati1261", parameterId := "lapidaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.lupinaris : Lexeme :=
  { id := "lupinaris", languageId := "lati1261", parameterId := "lupinaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.limitaris : Lexeme :=
  { id := "limitaris", languageId := "lati1261", parameterId := "limitaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.luminaris : Lexeme :=
  { id := "luminaris", languageId := "lati1261", parameterId := "luminaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.palmaris : Lexeme :=
  { id := "palmaris", languageId := "lati1261", parameterId := "palmaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.elementaris : Lexeme :=
  { id := "elementaris", languageId := "lati1261", parameterId := "elementaris",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.caelibaris : Lexeme :=
  { id := "caelibaris", languageId := "lati1261", parameterId := "caelibaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.fulminaris : Lexeme :=
  { id := "fulminaris", languageId := "lati1261", parameterId := "fulminaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.glebalis : Lexeme :=
  { id := "glebalis", languageId := "lati1261", parameterId := "glebalis", pos := ↑UD.UPOS.ADJ }

def Lexemes.latiaris : Lexeme :=
  { id := "latiaris", languageId := "lati1261", parameterId := "latiaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.palearis : Lexeme :=
  { id := "palearis", languageId := "lati1261", parameterId := "palearis", pos := ↑UD.UPOS.ADJ }

def Lexemes.proeliaris : Lexeme :=
  { id := "proeliaris", languageId := "lati1261", parameterId := "proeliaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.linearis : Lexeme :=
  { id := "linearis", languageId := "lati1261", parameterId := "linearis", pos := ↑UD.UPOS.ADJ }

def Lexemes.caligaris : Lexeme :=
  { id := "caligaris", languageId := "lati1261", parameterId := "caligaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.vulgaris : Lexeme :=
  { id := "vulgaris", languageId := "lati1261", parameterId := "vulgaris", pos := ↑UD.UPOS.ADJ }

def Lexemes.letalis : Lexeme :=
  { id := "letalis", languageId := "lati1261", parameterId := "letalis", pos := ↑UD.UPOS.ADJ }

def navalis : Form Cell :=
  { id := "jacobs2026_navalis"
    lexeme := Lexemes.navalis
    cell := {}
    form := "navalis"
    segments := ["n", "a", "w", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1a)"⟩
    ] }

def natalis : Form Cell :=
  { id := "jacobs2026_natalis"
    lexeme := Lexemes.natalis
    cell := {}
    form := "natalis"
    segments := ["n", "a", "t", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1a)"⟩
    ] }

def criminalis : Form Cell :=
  { id := "jacobs2026_criminalis"
    lexeme := Lexemes.criminalis
    cell := {}
    form := "criminalis"
    segments := ["k", "r", "i", "m", "i", "n", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1a)"⟩
    ] }

def solaris : Form Cell :=
  { id := "jacobs2026_solaris"
    lexeme := Lexemes.solaris
    cell := {}
    form := "solaris"
    segments := ["s", "o", "l", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1b)"⟩
    ] }

def militaris : Form Cell :=
  { id := "jacobs2026_militaris"
    lexeme := Lexemes.militaris
    cell := {}
    form := "militaris"
    segments := ["m", "i", "l", "i", "t", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1b)"⟩
    ] }

def lunaris : Form Cell :=
  { id := "jacobs2026_lunaris"
    lexeme := Lexemes.lunaris
    cell := {}
    form := "lunaris"
    segments := ["l", "u", "n", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1b)"⟩
    ] }

def floralis : Form Cell :=
  { id := "jacobs2026_floralis"
    lexeme := Lexemes.floralis
    cell := {}
    form := "floralis"
    segments := ["f", "l", "o", "r", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1c)"⟩
    ] }

def lateralis : Form Cell :=
  { id := "jacobs2026_lateralis"
    lexeme := Lexemes.lateralis
    cell := {}
    form := "lateralis"
    segments := ["l", "a", "t", "e", "r", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1c)"⟩
    ] }

def ridicularis : Form Cell :=
  { id := "jacobs2026_ridicularis"
    lexeme := Lexemes.ridicularis
    cell := {}
    form := "ridicularis"
    segments := ["r", "i", "d", "i", "k", "u", "l", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1d)"⟩
    ] }

def tricliniaris : Form Cell :=
  { id := "jacobs2026_tricliniaris"
    lexeme := Lexemes.tricliniaris
    cell := {}
    form := "tricliniaris"
    segments := ["t", "r", "i", "k", "l", "i", "n", "i", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(1d)"⟩
    ] }

def umbilicalis : Form Cell :=
  { id := "jacobs2026_umbilicalis"
    lexeme := Lexemes.umbilicalis
    cell := {}
    form := "umbilicalis"
    segments := ["u", "m", "b", "i", "l", "i", "k", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def cloacalis : Form Cell :=
  { id := "jacobs2026_cloacalis"
    lexeme := Lexemes.cloacalis
    cell := {}
    form := "cloacalis"
    segments := ["k", "l", "o", "a", "k", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def vulcanalis : Form Cell :=
  { id := "jacobs2026_vulcanalis"
    lexeme := Lexemes.vulcanalis
    cell := {}
    form := "vulcanalis"
    segments := ["w", "u", "l", "k", "a", "n", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def intellectualis : Form Cell :=
  { id := "jacobs2026_intellectualis"
    lexeme := Lexemes.intellectualis
    cell := {}
    form := "intellectualis"
    segments := ["i", "n", "t", "e", "l", "l", "e", "k", "t", "u", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def glacialis : Form Cell :=
  { id := "jacobs2026_glacialis"
    lexeme := Lexemes.glacialis
    cell := {}
    form := "glacialis"
    segments := ["g", "l", "a", "k", "i", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def localis : Form Cell :=
  { id := "jacobs2026_localis"
    lexeme := Lexemes.localis
    cell := {}
    form := "localis"
    segments := ["l", "o", "k", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def legalis : Form Cell :=
  { id := "jacobs2026_legalis"
    lexeme := Lexemes.legalis
    cell := {}
    form := "legalis"
    segments := ["l", "e", "g", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15a)"⟩
    ] }

def lectualis : Form Cell :=
  { id := "jacobs2026_lectualis"
    lexeme := Lexemes.lectualis
    cell := {}
    form := "lectualis"
    segments := ["l", "e", "k", "t", "u", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 131"⟩
    ] }

def pluvialis : Form Cell :=
  { id := "jacobs2026_pluvialis"
    lexeme := Lexemes.pluvialis
    cell := {}
    form := "pluvialis"
    segments := ["p", "l", "u", "w", "i", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15b)"⟩
    ] }

def fluvialis : Form Cell :=
  { id := "jacobs2026_fluvialis"
    lexeme := Lexemes.fluvialis
    cell := {}
    form := "fluvialis"
    segments := ["f", "l", "u", "w", "i", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15b)"⟩
    ] }

def flavialis : Form Cell :=
  { id := "jacobs2026_flavialis"
    lexeme := Lexemes.flavialis
    cell := {}
    form := "Flavialis"
    segments := ["f", "l", "a", "w", "i", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(15b)"⟩
    ] }

def lupanaris : Form Cell :=
  { id := "jacobs2026_lupanaris"
    lexeme := Lexemes.lupanaris
    cell := {}
    form := "lupanaris"
    segments := ["l", "u", "p", "a", "n", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 132"⟩
    ] }

def lapidaris : Form Cell :=
  { id := "jacobs2026_lapidaris"
    lexeme := Lexemes.lapidaris
    cell := {}
    form := "lapidaris"
    segments := ["l", "a", "p", "i", "d", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 132"⟩
    ] }

def lupinaris : Form Cell :=
  { id := "jacobs2026_lupinaris"
    lexeme := Lexemes.lupinaris
    cell := {}
    form := "lupinaris"
    segments := ["l", "u", "p", "i", "n", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 132"⟩
    ] }

def limitaris : Form Cell :=
  { id := "jacobs2026_limitaris"
    lexeme := Lexemes.limitaris
    cell := {}
    form := "limitaris"
    segments := ["l", "i", "m", "i", "t", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def luminaris : Form Cell :=
  { id := "jacobs2026_luminaris"
    lexeme := Lexemes.luminaris
    cell := {}
    form := "luminaris"
    segments := ["l", "u", "m", "i", "n", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def palmaris : Form Cell :=
  { id := "jacobs2026_palmaris"
    lexeme := Lexemes.palmaris
    cell := {}
    form := "palmaris"
    segments := ["p", "a", "l", "m", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def elementaris : Form Cell :=
  { id := "jacobs2026_elementaris"
    lexeme := Lexemes.elementaris
    cell := {}
    form := "elementaris"
    segments := ["e", "l", "e", "m", "e", "n", "t", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def caelibaris : Form Cell :=
  { id := "jacobs2026_caelibaris"
    lexeme := Lexemes.caelibaris
    cell := {}
    form := "caelibaris"
    segments := ["k", "a", "j", "l", "i", "b", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def fulminaris : Form Cell :=
  { id := "jacobs2026_fulminaris"
    lexeme := Lexemes.fulminaris
    cell := {}
    form := "fulminaris"
    segments := ["f", "u", "l", "m", "i", "n", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def glebalis : Form Cell :=
  { id := "jacobs2026_glebalis"
    lexeme := Lexemes.glebalis
    cell := {}
    form := "glebalis"
    segments := ["g", "l", "e", "b", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 139"⟩
    ] }

def latiaris : Form Cell :=
  { id := "jacobs2026_latiaris"
    lexeme := Lexemes.latiaris
    cell := {}
    form := "Latiaris"
    segments := ["l", "a", "t", "i", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 137"⟩
    ] }

def palearis : Form Cell :=
  { id := "jacobs2026_palearis"
    lexeme := Lexemes.palearis
    cell := {}
    form := "palearis"
    segments := ["p", "a", "l", "e", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 138"⟩
    ] }

def proeliaris : Form Cell :=
  { id := "jacobs2026_proeliaris"
    lexeme := Lexemes.proeliaris
    cell := {}
    form := "proeliaris"
    segments := ["p", "r", "o", "j", "l", "i", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 138"⟩
    ] }

def linearis : Form Cell :=
  { id := "jacobs2026_linearis"
    lexeme := Lexemes.linearis
    cell := {}
    form := "linearis"
    segments := ["l", "i", "n", "e", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 137"⟩
    ] }

def latialis : Form Cell :=
  { id := "jacobs2026_latialis"
    lexeme := Lexemes.latiaris
    cell := {}
    form := "Latialis"
    segments := ["l", "a", "t", "i", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(23)"⟩
    ] }

def palealis : Form Cell :=
  { id := "jacobs2026_palealis"
    lexeme := Lexemes.palearis
    cell := {}
    form := "palealis"
    segments := ["p", "a", "l", "e", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 138"⟩
    ] }

def proelialis : Form Cell :=
  { id := "jacobs2026_proelialis"
    lexeme := Lexemes.proeliaris
    cell := {}
    form := "proelialis"
    segments := ["p", "r", "o", "j", "l", "i", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 138"⟩
    ] }

def linealis : Form Cell :=
  { id := "jacobs2026_linealis"
    lexeme := Lexemes.linearis
    cell := {}
    form := "linealis"
    segments := ["l", "i", "n", "e", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "(23)"⟩
    ] }

def caligaris : Form Cell :=
  { id := "jacobs2026_caligaris"
    lexeme := Lexemes.caligaris
    cell := {}
    form := "caligaris"
    segments := ["k", "a", "l", "i", "g", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 131"⟩
    ] }

def vulgaris : Form Cell :=
  { id := "jacobs2026_vulgaris"
    lexeme := Lexemes.vulgaris
    cell := {}
    form := "vulgaris"
    segments := ["w", "u", "l", "g", "a", "r", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 131"⟩
    ] }

def letalis : Form Cell :=
  { id := "jacobs2026_letalis"
    lexeme := Lexemes.letalis
    cell := {}
    form := "letalis"
    segments := ["l", "e", "t", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 131"⟩
    ] }

def caelibalis : Form Cell :=
  { id := "jacobs2026_caelibalis"
    lexeme := Lexemes.caelibaris
    cell := {}
    form := "caelibalis"
    segments := ["k", "a", "j", "l", "i", "b", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

def fulminalis : Form Cell :=
  { id := "jacobs2026_fulminalis"
    lexeme := Lexemes.fulminaris
    cell := {}
    form := "fulminalis"
    segments := ["f", "u", "l", "m", "i", "n", "a", "l", "i", "s"]
    source := [
      ⟨"jacobs-2026", "p. 133"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Underlying` column, the underlying form the paper assigns, stem and suffix. -/
  underlying : String
  /-- The `Status` column, how the paper classifies the form. -/
  status : Status
  deriving DecidableEq, Repr

def navalis.analysis : Analysis :=
  { form := navalis,
    underlying := "/naw-alis/",
    status := Status.regular }

def natalis.analysis : Analysis :=
  { form := natalis,
    underlying := "/nat-alis/",
    status := Status.regular }

def criminalis.analysis : Analysis :=
  { form := criminalis,
    underlying := "/krimin-alis/",
    status := Status.regular }

def solaris.analysis : Analysis :=
  { form := solaris,
    underlying := "/sol-alis/",
    status := Status.regular }

def militaris.analysis : Analysis :=
  { form := militaris,
    underlying := "/milit-alis/",
    status := Status.regular }

def lunaris.analysis : Analysis :=
  { form := lunaris,
    underlying := "/lun-alis/",
    status := Status.regular }

def floralis.analysis : Analysis :=
  { form := floralis,
    underlying := "/flor-alis/",
    status := Status.regular }

def lateralis.analysis : Analysis :=
  { form := lateralis,
    underlying := "/later-alis/",
    status := Status.regular }

def ridicularis.analysis : Analysis :=
  { form := ridicularis,
    underlying := "/ridikul-alis/",
    status := Status.regular }

def tricliniaris.analysis : Analysis :=
  { form := tricliniaris,
    underlying := "/triklini-alis/",
    status := Status.regular }

def umbilicalis.analysis : Analysis :=
  { form := umbilicalis,
    underlying := "/umbilik-alis/",
    status := Status.regular }

def cloacalis.analysis : Analysis :=
  { form := cloacalis,
    underlying := "/kloak-alis/",
    status := Status.regular }

def vulcanalis.analysis : Analysis :=
  { form := vulcanalis,
    underlying := "/wulkan-alis/",
    status := Status.regular }

def intellectualis.analysis : Analysis :=
  { form := intellectualis,
    underlying := "/intellektu-alis/",
    status := Status.regular }

def glacialis.analysis : Analysis :=
  { form := glacialis,
    underlying := "/glaki-alis/",
    status := Status.regular }

def localis.analysis : Analysis :=
  { form := localis,
    underlying := "/lok-alis/",
    status := Status.regular }

def legalis.analysis : Analysis :=
  { form := legalis,
    underlying := "/leg-alis/",
    status := Status.regular }

def lectualis.analysis : Analysis :=
  { form := lectualis,
    underlying := "/lektu-alis/",
    status := Status.regular }

def pluvialis.analysis : Analysis :=
  { form := pluvialis,
    underlying := "/pluwi-alis/",
    status := Status.regular }

def fluvialis.analysis : Analysis :=
  { form := fluvialis,
    underlying := "/fluwi-alis/",
    status := Status.regular }

def flavialis.analysis : Analysis :=
  { form := flavialis,
    underlying := "/flawi-alis/",
    status := Status.regular }

def lupanaris.analysis : Analysis :=
  { form := lupanaris,
    underlying := "/lupan-alis/",
    status := Status.regular }

def lapidaris.analysis : Analysis :=
  { form := lapidaris,
    underlying := "/lapid-alis/",
    status := Status.regular }

def lupinaris.analysis : Analysis :=
  { form := lupinaris,
    underlying := "/lupin-alis/",
    status := Status.regular }

def limitaris.analysis : Analysis :=
  { form := limitaris,
    underlying := "/limit-alis/",
    status := Status.regular }

def luminaris.analysis : Analysis :=
  { form := luminaris,
    underlying := "/lumin-alis/",
    status := Status.regular }

def palmaris.analysis : Analysis :=
  { form := palmaris,
    underlying := "/palm-alis/",
    status := Status.regular }

def elementaris.analysis : Analysis :=
  { form := elementaris,
    underlying := "/element-alis/",
    status := Status.regular }

def caelibaris.analysis : Analysis :=
  { form := caelibaris,
    underlying := "/kajlib-alis/",
    status := Status.regular }

def fulminaris.analysis : Analysis :=
  { form := fulminaris,
    underlying := "/fulmin-alis/",
    status := Status.regular }

def glebalis.analysis : Analysis :=
  { form := glebalis,
    underlying := "/glajb-alis/",
    status := Status.regular }

def latiaris.analysis : Analysis :=
  { form := latiaris,
    underlying := "/lati-alis/",
    status := Status.regular }

def palearis.analysis : Analysis :=
  { form := palearis,
    underlying := "/pale-alis/",
    status := Status.regular }

def proeliaris.analysis : Analysis :=
  { form := proeliaris,
    underlying := "/projli-alis/",
    status := Status.regular }

def linearis.analysis : Analysis :=
  { form := linearis,
    underlying := "/line-alis/",
    status := Status.regular }

def latialis.analysis : Analysis :=
  { form := latialis,
    underlying := "/latj-alis/",
    status := Status.glide }

def palealis.analysis : Analysis :=
  { form := palealis,
    underlying := "/palj-alis/",
    status := Status.glide }

def proelialis.analysis : Analysis :=
  { form := proelialis,
    underlying := "/projlj-alis/",
    status := Status.glide }

def linealis.analysis : Analysis :=
  { form := linealis,
    underlying := "/linj-alis/",
    status := Status.glide }

def caligaris.analysis : Analysis :=
  { form := caligaris,
    underlying := "/kalig-alis/",
    status := Status.exception }

def vulgaris.analysis : Analysis :=
  { form := vulgaris,
    underlying := "/wulg-alis/",
    status := Status.exception }

def letalis.analysis : Analysis :=
  { form := letalis,
    underlying := "/let-alis/",
    status := Status.exception }

def caelibalis.analysis : Analysis :=
  { form := caelibalis,
    underlying := "/kajlib-alis/",
    status := Status.exception }

def fulminalis.analysis : Analysis :=
  { form := fulminalis,
    underlying := "/fulmin-alis/",
    status := Status.unexplained }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.navalis, Lexemes.natalis, Lexemes.criminalis, Lexemes.solaris,
  Lexemes.militaris, Lexemes.lunaris, Lexemes.floralis, Lexemes.lateralis, Lexemes.ridicularis,
  Lexemes.tricliniaris, Lexemes.umbilicalis, Lexemes.cloacalis, Lexemes.vulcanalis,
  Lexemes.intellectualis, Lexemes.glacialis, Lexemes.localis, Lexemes.legalis, Lexemes.lectualis,
  Lexemes.pluvialis, Lexemes.fluvialis, Lexemes.flavialis, Lexemes.lupanaris, Lexemes.lapidaris,
  Lexemes.lupinaris, Lexemes.limitaris, Lexemes.luminaris, Lexemes.palmaris, Lexemes.elementaris,
  Lexemes.caelibaris, Lexemes.fulminaris, Lexemes.glebalis, Lexemes.latiaris, Lexemes.palearis,
  Lexemes.proeliaris, Lexemes.linearis, Lexemes.caligaris, Lexemes.vulgaris, Lexemes.letalis]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [navalis, natalis, criminalis, solaris, militaris, lunaris, floralis,
  lateralis, ridicularis, tricliniaris, umbilicalis, cloacalis, vulcanalis, intellectualis,
  glacialis, localis, legalis, lectualis, pluvialis, fluvialis, flavialis, lupanaris, lapidaris,
  lupinaris, limitaris, luminaris, palmaris, elementaris, caelibaris, fulminaris, glebalis,
  latiaris, palearis, proeliaris, linearis, latialis, palealis, proelialis, linealis, caligaris,
  vulgaris, letalis, caelibalis, fulminalis]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [navalis.analysis, natalis.analysis, criminalis.analysis,
  solaris.analysis, militaris.analysis, lunaris.analysis, floralis.analysis, lateralis.analysis,
  ridicularis.analysis, tricliniaris.analysis, umbilicalis.analysis, cloacalis.analysis,
  vulcanalis.analysis, intellectualis.analysis, glacialis.analysis, localis.analysis,
  legalis.analysis, lectualis.analysis, pluvialis.analysis, fluvialis.analysis, flavialis.analysis,
  lupanaris.analysis, lapidaris.analysis, lupinaris.analysis, limitaris.analysis,
  luminaris.analysis, palmaris.analysis, elementaris.analysis, caelibaris.analysis,
  fulminaris.analysis, glebalis.analysis, latiaris.analysis, palearis.analysis, proeliaris.analysis,
  linearis.analysis, latialis.analysis, palealis.analysis, proelialis.analysis, linealis.analysis,
  caligaris.analysis, vulgaris.analysis, letalis.analysis, caelibalis.analysis, fulminalis.analysis]

end Jacobs2026.Wordlist
