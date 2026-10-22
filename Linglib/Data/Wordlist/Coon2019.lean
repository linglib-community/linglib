module

public import Linglib.Data.Wordlist.Schema

/-!
# `Coon2019`: word forms

Auto-generated from `Linglib/Data/Wordlist/Coon2019.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace Coon2019.Wordlist`.
-/

@[expose] public section

namespace Coon2019.Wordlist

open Data.Wordlist

/-- The values of `RootClass` the source distinguishes. -/
inductive RootClass where
  /-- A transitive root, forming bare transitive stems, `tv` in the source. -/
  | tv
  /-- An intransitive root, taking the null head of intransitive stems, `itv` in the source. -/
  | itv
  /-- A positional root, forming stative -an stems and taking -w, `pos` in the source. -/
  | pos
  /-- A nominal root, appearing underived in nominal contexts, `nom` in the source. -/
  | nom
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.root_xik : Lexeme :=
  { id := "root_xik", languageId := "chuj1250", parameterId := "chop", label := "xik" }

def Lexemes.root_chonh : Lexeme :=
  { id := "root_chonh", languageId := "chuj1250", parameterId := "sell", label := "chonh" }

def Lexemes.root_jax : Lexeme :=
  { id := "root_jax", languageId := "chuj1250", parameterId := "grind", label := "jax" }

def Lexemes.root_chel : Lexeme :=
  { id := "root_chel", languageId := "chuj1250", parameterId := "hug", label := "chel" }

def Lexemes.root_tek : Lexeme :=
  { id := "root_tek", languageId := "chuj1250", parameterId := "kick", label := "tek'" }

def Lexemes.root_mak_hit : Lexeme :=
  { id := "root_mak_hit", languageId := "chuj1250", parameterId := "hit", label := "mak'" }

def Lexemes.root_il : Lexeme :=
  { id := "root_il", languageId := "chuj1250", parameterId := "see", label := "il" }

def Lexemes.root_chak : Lexeme :=
  { id := "root_chak", languageId := "chuj1250", parameterId := "fell", label := "ch'ak" }

def Lexemes.root_bo : Lexeme :=
  { id := "root_bo", languageId := "chuj1250", parameterId := "make", label := "b'o'" }

def Lexemes.root_man : Lexeme :=
  { id := "root_man", languageId := "chuj1250", parameterId := "buy", label := "man" }

def Lexemes.root_kal : Lexeme :=
  { id := "root_kal", languageId := "chuj1250", parameterId := "stir", label := "kal" }

def Lexemes.root_tzil : Lexeme :=
  { id := "root_tzil", languageId := "chuj1250", parameterId := "tear", label := "tzil" }

def Lexemes.root_yam : Lexeme :=
  { id := "root_yam", languageId := "chuj1250", parameterId := "catch", label := "yam" }

def Lexemes.root_mak : Lexeme :=
  { id := "root_mak", languageId := "chuj1250", parameterId := "close", label := "mak" }

def Lexemes.root_bat : Lexeme :=
  { id := "root_bat", languageId := "chuj1250", parameterId := "go", label := "b'at" }

def Lexemes.root_way : Lexeme :=
  { id := "root_way", languageId := "chuj1250", parameterId := "sleep", label := "way" }

def Lexemes.root_key : Lexeme :=
  { id := "root_key", languageId := "chuj1250", parameterId := "ascend", label := "k'ey" }

def Lexemes.root_jaw : Lexeme :=
  { id := "root_jaw", languageId := "chuj1250", parameterId := "arrive", label := "jaw" }

def Lexemes.root_ok : Lexeme :=
  { id := "root_ok", languageId := "chuj1250", parameterId := "cry", label := "ok'" }

def Lexemes.root_bey : Lexeme :=
  { id := "root_bey", languageId := "chuj1250", parameterId := "walk", label := "b'ey" }

def Lexemes.root_ul : Lexeme :=
  { id := "root_ul", languageId := "chuj1250", parameterId := "dissolve", label := "ul" }

def Lexemes.root_el : Lexeme :=
  { id := "root_el", languageId := "chuj1250", parameterId := "leave", label := "el" }

def Lexemes.root_chot : Lexeme :=
  { id := "root_chot", languageId := "chuj1250", parameterId := "crouched", label := "chot" }

def Lexemes.root_jenh : Lexeme :=
  { id := "root_jenh", languageId := "chuj1250", parameterId := "outstretched", label := "jenh" }

def Lexemes.root_chek : Lexeme :=
  { id := "root_chek", languageId := "chuj1250", parameterId := "leaning", label := "chek'" }

def Lexemes.root_lich : Lexeme :=
  { id := "root_lich", languageId := "chuj1250", parameterId := "extended", label := "lich'" }

def Lexemes.root_bul : Lexeme :=
  { id := "root_bul", languageId := "chuj1250", parameterId := "gathered", label := "b'ul" }

def Lexemes.root_kot : Lexeme :=
  { id := "root_kot", languageId := "chuj1250", parameterId := "on_four_legs", label := "kot" }

def Lexemes.root_tel : Lexeme :=
  { id := "root_tel", languageId := "chuj1250", parameterId := "lying_down", label := "tel" }

def Lexemes.root_chet : Lexeme :=
  { id := "root_chet", languageId := "chuj1250", parameterId := "on_two_legs", label := "chet" }

def Lexemes.root_pat : Lexeme :=
  { id := "root_pat", languageId := "chuj1250", parameterId := "house", label := "pat" }

def Lexemes.root_katzitz : Lexeme :=
  { id := "root_katzitz", languageId := "chuj1250", parameterId := "wood", label := "k'atzitz" }

def Lexemes.root_ixim : Lexeme :=
  { id := "root_ixim", languageId := "chuj1250", parameterId := "corn", label := "ixim" }

def Lexemes.root_winak : Lexeme :=
  { id := "root_winak", languageId := "chuj1250", parameterId := "man", label := "winak" }

def Lexemes.root_chanhal : Lexeme :=
  { id := "root_chanhal", languageId := "chuj1250", parameterId := "dance", label := "chanhal" }

def Lexemes.root_atis : Lexeme :=
  { id := "root_atis", languageId := "chuj1250", parameterId := "sneeze", label := "at'is" }

def Lexemes.root_tzib : Lexeme :=
  { id := "root_tzib", languageId := "chuj1250", parameterId := "writing", label := "tz'ib'" }

def Lexemes.root_patan : Lexeme :=
  { id := "root_patan", languageId := "chuj1250", parameterId := "cleared_land", label := "patan" }

def xik : Form Cell :=
  { id := "coon2019_xik"
    lexeme := Lexemes.root_xik
    cell := {}
    form := "xik"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def chonh : Form Cell :=
  { id := "coon2019_chonh"
    lexeme := Lexemes.root_chonh
    cell := {}
    form := "chonh"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def jax : Form Cell :=
  { id := "coon2019_jax"
    lexeme := Lexemes.root_jax
    cell := {}
    form := "jax"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def chel : Form Cell :=
  { id := "coon2019_chel"
    lexeme := Lexemes.root_chel
    cell := {}
    form := "chel"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def tek : Form Cell :=
  { id := "coon2019_tek"
    lexeme := Lexemes.root_tek
    cell := {}
    form := "tek'"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def mak_hit : Form Cell :=
  { id := "coon2019_mak_hit"
    lexeme := Lexemes.root_mak_hit
    cell := {}
    form := "mak'"
    source := [
      ⟨"coon-2019", "(55b)"⟩
    ] }

def il : Form Cell :=
  { id := "coon2019_il"
    lexeme := Lexemes.root_il
    cell := {}
    form := "il"
    source := [
      ⟨"coon-2019", "(10d)"⟩
    ] }

def chak : Form Cell :=
  { id := "coon2019_chak"
    lexeme := Lexemes.root_chak
    cell := {}
    form := "ch'ak"
    source := [
      ⟨"coon-2019", "(63a)"⟩
    ] }

def bo : Form Cell :=
  { id := "coon2019_bo"
    lexeme := Lexemes.root_bo
    cell := {}
    form := "b'o'"
    source := [
      ⟨"coon-2019", "(62)"⟩
    ] }

def man : Form Cell :=
  { id := "coon2019_man"
    lexeme := Lexemes.root_man
    cell := {}
    form := "man"
    source := [
      ⟨"coon-2019", "(59a)"⟩
    ] }

def kal : Form Cell :=
  { id := "coon2019_kal"
    lexeme := Lexemes.root_kal
    cell := {}
    form := "kal"
    source := [
      ⟨"coon-2019", "(29a)"⟩
    ] }

def tzil : Form Cell :=
  { id := "coon2019_tzil"
    lexeme := Lexemes.root_tzil
    cell := {}
    form := "tzil"
    source := [
      ⟨"coon-2019", "(35a)"⟩
    ] }

def yam : Form Cell :=
  { id := "coon2019_yam"
    lexeme := Lexemes.root_yam
    cell := {}
    form := "yam"
    source := [
      ⟨"coon-2019", "(60a)"⟩
    ] }

def mak : Form Cell :=
  { id := "coon2019_mak"
    lexeme := Lexemes.root_mak
    cell := {}
    form := "mak"
    source := [
      ⟨"coon-2019", "(70a)"⟩
    ] }

def bat : Form Cell :=
  { id := "coon2019_bat"
    lexeme := Lexemes.root_bat
    cell := {}
    form := "b'at"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def way : Form Cell :=
  { id := "coon2019_way"
    lexeme := Lexemes.root_way
    cell := {}
    form := "way"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def key : Form Cell :=
  { id := "coon2019_key"
    lexeme := Lexemes.root_key
    cell := {}
    form := "k'ey"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def jaw : Form Cell :=
  { id := "coon2019_jaw"
    lexeme := Lexemes.root_jaw
    cell := {}
    form := "jaw"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def ok : Form Cell :=
  { id := "coon2019_ok"
    lexeme := Lexemes.root_ok
    cell := {}
    form := "ok'"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def bey : Form Cell :=
  { id := "coon2019_bey"
    lexeme := Lexemes.root_bey
    cell := {}
    form := "b'ey"
    source := [
      ⟨"coon-2019", "(7c)"⟩
    ] }

def ul : Form Cell :=
  { id := "coon2019_ul"
    lexeme := Lexemes.root_ul
    cell := {}
    form := "ul"
    source := [
      ⟨"coon-2019", "(48a)"⟩
    ] }

def el : Form Cell :=
  { id := "coon2019_el"
    lexeme := Lexemes.root_el
    cell := {}
    form := "el"
    source := [
      ⟨"coon-2019", "(57)"⟩
    ] }

def chot : Form Cell :=
  { id := "coon2019_chot"
    lexeme := Lexemes.root_chot
    cell := {}
    form := "chot"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def jenh : Form Cell :=
  { id := "coon2019_jenh"
    lexeme := Lexemes.root_jenh
    cell := {}
    form := "jenh"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def chek : Form Cell :=
  { id := "coon2019_chek"
    lexeme := Lexemes.root_chek
    cell := {}
    form := "chek'"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def lich : Form Cell :=
  { id := "coon2019_lich"
    lexeme := Lexemes.root_lich
    cell := {}
    form := "lich'"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def bul : Form Cell :=
  { id := "coon2019_bul"
    lexeme := Lexemes.root_bul
    cell := {}
    form := "b'ul"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def kot : Form Cell :=
  { id := "coon2019_kot"
    lexeme := Lexemes.root_kot
    cell := {}
    form := "kot"
    source := [
      ⟨"coon-2019", "(20)"⟩
    ] }

def tel : Form Cell :=
  { id := "coon2019_tel"
    lexeme := Lexemes.root_tel
    cell := {}
    form := "tel"
    source := [
      ⟨"coon-2019", "(20)"⟩
    ] }

def chet : Form Cell :=
  { id := "coon2019_chet"
    lexeme := Lexemes.root_chet
    cell := {}
    form := "chet"
    source := [
      ⟨"coon-2019", "(20)"⟩
    ] }

def pat : Form Cell :=
  { id := "coon2019_pat"
    lexeme := Lexemes.root_pat
    cell := {}
    form := "pat"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def katzitz : Form Cell :=
  { id := "coon2019_katzitz"
    lexeme := Lexemes.root_katzitz
    cell := {}
    form := "k'atzitz"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def ixim : Form Cell :=
  { id := "coon2019_ixim"
    lexeme := Lexemes.root_ixim
    cell := {}
    form := "ixim"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def winak : Form Cell :=
  { id := "coon2019_winak"
    lexeme := Lexemes.root_winak
    cell := {}
    form := "winak"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def chanhal : Form Cell :=
  { id := "coon2019_chanhal"
    lexeme := Lexemes.root_chanhal
    cell := {}
    form := "chanhal"
    source := [
      ⟨"coon-2019", "(5)"⟩
    ] }

def atis : Form Cell :=
  { id := "coon2019_atis"
    lexeme := Lexemes.root_atis
    cell := {}
    form := "at'is"
    source := [
      ⟨"coon-2019", "(17)"⟩
    ] }

def tzib : Form Cell :=
  { id := "coon2019_tzib"
    lexeme := Lexemes.root_tzib
    cell := {}
    form := "tz'ib'"
    source := [
      ⟨"coon-2019", "(17)"⟩
    ] }

def patan : Form Cell :=
  { id := "coon2019_patan"
    lexeme := Lexemes.root_patan
    cell := {}
    form := "patan"
    source := [
      ⟨"coon-2019", "(17)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Class` column, the root class, the column of (5) the root heads or the class Coon names
  it by. -/
  rootClass : RootClass
  deriving DecidableEq, Repr

def xik.analysis : Analysis :=
  { form := xik,
    rootClass := RootClass.tv }

def chonh.analysis : Analysis :=
  { form := chonh,
    rootClass := RootClass.tv }

def jax.analysis : Analysis :=
  { form := jax,
    rootClass := RootClass.tv }

def chel.analysis : Analysis :=
  { form := chel,
    rootClass := RootClass.tv }

def tek.analysis : Analysis :=
  { form := tek,
    rootClass := RootClass.tv }

def mak_hit.analysis : Analysis :=
  { form := mak_hit,
    rootClass := RootClass.tv }

def il.analysis : Analysis :=
  { form := il,
    rootClass := RootClass.tv }

def chak.analysis : Analysis :=
  { form := chak,
    rootClass := RootClass.tv }

def bo.analysis : Analysis :=
  { form := bo,
    rootClass := RootClass.tv }

def man.analysis : Analysis :=
  { form := man,
    rootClass := RootClass.tv }

def kal.analysis : Analysis :=
  { form := kal,
    rootClass := RootClass.tv }

def tzil.analysis : Analysis :=
  { form := tzil,
    rootClass := RootClass.tv }

def yam.analysis : Analysis :=
  { form := yam,
    rootClass := RootClass.tv }

def mak.analysis : Analysis :=
  { form := mak,
    rootClass := RootClass.tv }

def bat.analysis : Analysis :=
  { form := bat,
    rootClass := RootClass.itv }

def way.analysis : Analysis :=
  { form := way,
    rootClass := RootClass.itv }

def key.analysis : Analysis :=
  { form := key,
    rootClass := RootClass.itv }

def jaw.analysis : Analysis :=
  { form := jaw,
    rootClass := RootClass.itv }

def ok.analysis : Analysis :=
  { form := ok,
    rootClass := RootClass.itv }

def bey.analysis : Analysis :=
  { form := bey,
    rootClass := RootClass.itv }

def ul.analysis : Analysis :=
  { form := ul,
    rootClass := RootClass.itv }

def el.analysis : Analysis :=
  { form := el,
    rootClass := RootClass.itv }

def chot.analysis : Analysis :=
  { form := chot,
    rootClass := RootClass.pos }

def jenh.analysis : Analysis :=
  { form := jenh,
    rootClass := RootClass.pos }

def chek.analysis : Analysis :=
  { form := chek,
    rootClass := RootClass.pos }

def lich.analysis : Analysis :=
  { form := lich,
    rootClass := RootClass.pos }

def bul.analysis : Analysis :=
  { form := bul,
    rootClass := RootClass.pos }

def kot.analysis : Analysis :=
  { form := kot,
    rootClass := RootClass.pos }

def tel.analysis : Analysis :=
  { form := tel,
    rootClass := RootClass.pos }

def chet.analysis : Analysis :=
  { form := chet,
    rootClass := RootClass.pos }

def pat.analysis : Analysis :=
  { form := pat,
    rootClass := RootClass.nom }

def katzitz.analysis : Analysis :=
  { form := katzitz,
    rootClass := RootClass.nom }

def ixim.analysis : Analysis :=
  { form := ixim,
    rootClass := RootClass.nom }

def winak.analysis : Analysis :=
  { form := winak,
    rootClass := RootClass.nom }

def chanhal.analysis : Analysis :=
  { form := chanhal,
    rootClass := RootClass.nom }

def atis.analysis : Analysis :=
  { form := atis,
    rootClass := RootClass.nom }

def tzib.analysis : Analysis :=
  { form := tzib,
    rootClass := RootClass.nom }

def patan.analysis : Analysis :=
  { form := patan,
    rootClass := RootClass.nom }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.root_xik, Lexemes.root_chonh, Lexemes.root_jax,
  Lexemes.root_chel, Lexemes.root_tek, Lexemes.root_mak_hit, Lexemes.root_il, Lexemes.root_chak,
  Lexemes.root_bo, Lexemes.root_man, Lexemes.root_kal, Lexemes.root_tzil, Lexemes.root_yam,
  Lexemes.root_mak, Lexemes.root_bat, Lexemes.root_way, Lexemes.root_key, Lexemes.root_jaw,
  Lexemes.root_ok, Lexemes.root_bey, Lexemes.root_ul, Lexemes.root_el, Lexemes.root_chot,
  Lexemes.root_jenh, Lexemes.root_chek, Lexemes.root_lich, Lexemes.root_bul, Lexemes.root_kot,
  Lexemes.root_tel, Lexemes.root_chet, Lexemes.root_pat, Lexemes.root_katzitz, Lexemes.root_ixim,
  Lexemes.root_winak, Lexemes.root_chanhal, Lexemes.root_atis, Lexemes.root_tzib,
  Lexemes.root_patan]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [xik, chonh, jax, chel, tek, mak_hit, il, chak, bo, man, kal, tzil,
  yam, mak, bat, way, key, jaw, ok, bey, ul, el, chot, jenh, chek, lich, bul, kot, tel, chet, pat,
  katzitz, ixim, winak, chanhal, atis, tzib, patan]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [xik.analysis, chonh.analysis, jax.analysis, chel.analysis,
  tek.analysis, mak_hit.analysis, il.analysis, chak.analysis, bo.analysis, man.analysis,
  kal.analysis, tzil.analysis, yam.analysis, mak.analysis, bat.analysis, way.analysis, key.analysis,
  jaw.analysis, ok.analysis, bey.analysis, ul.analysis, el.analysis, chot.analysis, jenh.analysis,
  chek.analysis, lich.analysis, bul.analysis, kot.analysis, tel.analysis, chet.analysis,
  pat.analysis, katzitz.analysis, ixim.analysis, winak.analysis, chanhal.analysis, atis.analysis,
  tzib.analysis, patan.analysis]

end Coon2019.Wordlist
