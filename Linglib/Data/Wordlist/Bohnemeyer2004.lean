module

public import Linglib.Data.Wordlist.Schema

/-!
# `Bohnemeyer2004`: word forms

Auto-generated from `Linglib/Data/Wordlist/Bohnemeyer2004.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Bohnemeyer2004.Wordlist`.
-/

@[expose] public section

namespace Bohnemeyer2004.Wordlist

open CLDF.Wordlist

/-- The values of `StemClass` the source distinguishes. -/
inductive StemClass where
  /-- An active intransitive stem, unmarked in the incompletive, `active` in the source. -/
  | active
  /-- An inactive intransitive stem, unmarked in the completive, `inactive` in the source. -/
  | inactive
  /-- An inchoative stem, derived from a stative root, `inchoative` in the source. -/
  | inchoative
  /-- A positional stem, `positional` in the source. -/
  | positional
  /-- A transitive active stem, `transitive` in the source. -/
  | transitive
  deriving DecidableEq, Repr

/-- The values of `Causation` the source distinguishes. -/
inductive Causation where
  /-- The base entails internal causation, `internal` in the source. -/
  | internal
  /-- The base denotes an externally-caused event, `external` in the source. -/
  | external
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.work : Lexeme :=
  { id := "work", languageId := "yuca1254", parameterId := "work", label := "meyah",
    pos := ↑UD.UPOS.VERB }

def Lexemes.play : Lexeme :=
  { id := "play", languageId := "yuca1254", parameterId := "play", label := "bàaxal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.eat : Lexeme :=
  { id := "eat", languageId := "yuca1254", parameterId := "eat", label := "hàan",
    pos := ↑UD.UPOS.VERB }

def Lexemes.roll : Lexeme :=
  { id := "roll", languageId := "yuca1254", parameterId := "roll", label := "balak'",
    pos := ↑UD.UPOS.VERB }

def Lexemes.move : Lexeme :=
  { id := "move", languageId := "yuca1254", parameterId := "move", label := "péek",
    pos := ↑UD.UPOS.VERB }

def Lexemes.buzz : Lexeme :=
  { id := "buzz", languageId := "yuca1254", parameterId := "buzz", label := "tsíirin",
    pos := ↑UD.UPOS.VERB }

def Lexemes.squeak : Lexeme :=
  { id := "squeak", languageId := "yuca1254", parameterId := "squeak", label := "nik'ich",
    pos := ↑UD.UPOS.VERB }

def Lexemes.shake : Lexeme :=
  { id := "shake", languageId := "yuca1254", parameterId := "shake", label := "chíik",
    pos := ↑UD.UPOS.VERB }

def Lexemes.slide : Lexeme :=
  { id := "slide", languageId := "yuca1254", parameterId := "slide", label := "háarax",
    pos := ↑UD.UPOS.VERB }

def Lexemes.stir : Lexeme :=
  { id := "stir", languageId := "yuca1254", parameterId := "stir", label := "húuy",
    pos := ↑UD.UPOS.VERB }

def Lexemes.whirl : Lexeme :=
  { id := "whirl", languageId := "yuca1254", parameterId := "whirl", label := "mosòon",
    pos := ↑UD.UPOS.VERB }

def Lexemes.flick : Lexeme :=
  { id := "flick", languageId := "yuca1254", parameterId := "flick", label := "pirix",
    pos := ↑UD.UPOS.VERB }

def Lexemes.turn : Lexeme :=
  { id := "turn", languageId := "yuca1254", parameterId := "turn", label := "walak'",
    pos := ↑UD.UPOS.VERB }

def Lexemes.die : Lexeme :=
  { id := "die", languageId := "yuca1254", parameterId := "die", label := "kim",
    pos := ↑UD.UPOS.VERB }

def Lexemes.fall : Lexeme :=
  { id := "fall", languageId := "yuca1254", parameterId := "fall", label := "lúub",
    pos := ↑UD.UPOS.VERB }

def Lexemes.get_tired : Lexeme :=
  { id := "get_tired", languageId := "yuca1254", parameterId := "get-tired", label := "ka'n",
    pos := ↑UD.UPOS.VERB }

def Lexemes.deteriorate : Lexeme :=
  { id := "deteriorate", languageId := "yuca1254", parameterId := "deteriorate", label := "la'b",
    pos := ↑UD.UPOS.VERB }

def Lexemes.ascend : Lexeme :=
  { id := "ascend", languageId := "yuca1254", parameterId := "ascend", label := "na'k",
    pos := ↑UD.UPOS.VERB }

def Lexemes.last : Lexeme :=
  { id := "last", languageId := "yuca1254", parameterId := "last", label := "t'íil",
    pos := ↑UD.UPOS.VERB }

def Lexemes.rot : Lexeme :=
  { id := "rot", languageId := "yuca1254", parameterId := "rot", label := "ts'u'k",
    pos := ↑UD.UPOS.VERB }

def Lexemes.blacken : Lexeme :=
  { id := "blacken", languageId := "yuca1254", parameterId := "blacken", label := "bòox-tal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.shrink : Lexeme :=
  { id := "shrink", languageId := "yuca1254", parameterId := "shrink", label := "chichan-tal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.stand_up : Lexeme :=
  { id := "stand_up", languageId := "yuca1254", parameterId := "stand-up", label := "wa'l-tal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.sit_down : Lexeme :=
  { id := "sit_down", languageId := "yuca1254", parameterId := "sit-down", label := "kul-tal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.lie_down : Lexeme :=
  { id := "lie_down", languageId := "yuca1254", parameterId := "lie-down", label := "chil-tal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.kneel : Lexeme :=
  { id := "kneel", languageId := "yuca1254", parameterId := "kneel", label := "xol-tal",
    pos := ↑UD.UPOS.VERB }

def Lexemes.make : Lexeme :=
  { id := "make", languageId := "yuca1254", parameterId := "make", label := "meyah-t",
    pos := ↑UD.UPOS.VERB }

def Lexemes.play_with : Lexeme :=
  { id := "play_with", languageId := "yuca1254", parameterId := "play-with", label := "bàax-t",
    pos := ↑UD.UPOS.VERB }

def Lexemes.kill : Lexeme :=
  { id := "kill", languageId := "yuca1254", parameterId := "kill", label := "kim-s",
    pos := ↑UD.UPOS.VERB }

def Lexemes.fell : Lexeme :=
  { id := "fell", languageId := "yuca1254", parameterId := "fell", label := "lúub-s",
    pos := ↑UD.UPOS.VERB }

def Lexemes.cause_to_move : Lexeme :=
  { id := "cause_to_move", languageId := "yuca1254", parameterId := "cause-to-move",
    label := "péek-s", pos := ↑UD.UPOS.VERB }

def Lexemes.eat_something : Lexeme :=
  { id := "eat_something", languageId := "yuca1254", parameterId := "eat-something",
    label := "hàan-t", pos := ↑UD.UPOS.VERB }

def Lexemes.cause_to_roll : Lexeme :=
  { id := "cause_to_roll", languageId := "yuca1254", parameterId := "cause-to-roll",
    label := "balak'-t", pos := ↑UD.UPOS.VERB }

def Lexemes.cause_to_buzz : Lexeme :=
  { id := "cause_to_buzz", languageId := "yuca1254", parameterId := "cause-to-buzz",
    label := "tsíirin-t", pos := ↑UD.UPOS.VERB }

def Lexemes.erect : Lexeme :=
  { id := "erect", languageId := "yuca1254", parameterId := "erect", label := "wa'l-kunt",
    pos := ↑UD.UPOS.VERB }

def meyah : Form Cell :=
  { id := "bohnemeyer2004_meyah"
    lexeme := Lexemes.work
    cell := {}
    form := "meyah"
    source := [
      ⟨"bohnemeyer-2004", "(4)"⟩
    ] }

def baaxal : Form Cell :=
  { id := "bohnemeyer2004_baaxal"
    lexeme := Lexemes.play
    cell := {}
    form := "bàaxal"
    source := [
      ⟨"bohnemeyer-2004", "(5)"⟩
    ] }

def haan : Form Cell :=
  { id := "bohnemeyer2004_haan"
    lexeme := Lexemes.eat
    cell := {}
    form := "hàan"
    source := [
      ⟨"bohnemeyer-2004", "(9)"⟩
    ] }

def balak : Form Cell :=
  { id := "bohnemeyer2004_balak"
    lexeme := Lexemes.roll
    cell := {}
    form := "balak'"
    source := [
      ⟨"bohnemeyer-2004", "(10)"⟩
    ] }

def peek : Form Cell :=
  { id := "bohnemeyer2004_peek"
    lexeme := Lexemes.move
    cell := {}
    form := "péek"
    source := [
      ⟨"bohnemeyer-2004", "(8)"⟩
    ] }

def tsiirin : Form Cell :=
  { id := "bohnemeyer2004_tsiirin"
    lexeme := Lexemes.buzz
    cell := {}
    form := "tsíirin"
    source := [
      ⟨"bohnemeyer-2004", "(11)"⟩
    ] }

def nikich : Form Cell :=
  { id := "bohnemeyer2004_nikich"
    lexeme := Lexemes.squeak
    cell := {}
    form := "nik'ich"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def chiik : Form Cell :=
  { id := "bohnemeyer2004_chiik"
    lexeme := Lexemes.shake
    cell := {}
    form := "chíik"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def haarax : Form Cell :=
  { id := "bohnemeyer2004_haarax"
    lexeme := Lexemes.slide
    cell := {}
    form := "háarax"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def huuy : Form Cell :=
  { id := "bohnemeyer2004_huuy"
    lexeme := Lexemes.stir
    cell := {}
    form := "húuy"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def mosoon : Form Cell :=
  { id := "bohnemeyer2004_mosoon"
    lexeme := Lexemes.whirl
    cell := {}
    form := "mosòon"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def pirix : Form Cell :=
  { id := "bohnemeyer2004_pirix"
    lexeme := Lexemes.flick
    cell := {}
    form := "pirix"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def walak : Form Cell :=
  { id := "bohnemeyer2004_walak"
    lexeme := Lexemes.turn
    cell := {}
    form := "walak'"
    source := [
      ⟨"bohnemeyer-2004", "p. 92"⟩
    ] }

def kim : Form Cell :=
  { id := "bohnemeyer2004_kim"
    lexeme := Lexemes.die
    cell := {}
    form := "kim"
    source := [
      ⟨"bohnemeyer-2004", "(6)"⟩
    ] }

def luub : Form Cell :=
  { id := "bohnemeyer2004_luub"
    lexeme := Lexemes.fall
    cell := {}
    form := "lúub"
    source := [
      ⟨"bohnemeyer-2004", "(7)"⟩
    ] }

def kan : Form Cell :=
  { id := "bohnemeyer2004_kan"
    lexeme := Lexemes.get_tired
    cell := {}
    form := "ka'n"
    source := [
      ⟨"bohnemeyer-2004", "(17)"⟩
    ] }

def lab : Form Cell :=
  { id := "bohnemeyer2004_lab"
    lexeme := Lexemes.deteriorate
    cell := {}
    form := "la'b"
    source := [
      ⟨"bohnemeyer-2004", "(17)"⟩
    ] }

def nak : Form Cell :=
  { id := "bohnemeyer2004_nak"
    lexeme := Lexemes.ascend
    cell := {}
    form := "na'k"
    source := [
      ⟨"bohnemeyer-2004", "(17)"⟩
    ] }

def tiil : Form Cell :=
  { id := "bohnemeyer2004_tiil"
    lexeme := Lexemes.last
    cell := {}
    form := "t'íil"
    source := [
      ⟨"bohnemeyer-2004", "(17)"⟩
    ] }

def tsuk : Form Cell :=
  { id := "bohnemeyer2004_tsuk"
    lexeme := Lexemes.rot
    cell := {}
    form := "ts'u'k"
    source := [
      ⟨"bohnemeyer-2004", "(17)"⟩
    ] }

def booxtal : Form Cell :=
  { id := "bohnemeyer2004_booxtal"
    lexeme := Lexemes.blacken
    cell := {}
    form := "bòox-tal"
    source := [
      ⟨"bohnemeyer-2004", "(18)"⟩
    ] }

def chichantal : Form Cell :=
  { id := "bohnemeyer2004_chichantal"
    lexeme := Lexemes.shrink
    cell := {}
    form := "chichan-tal"
    source := [
      ⟨"bohnemeyer-2004", "(18)"⟩
    ] }

def waltal : Form Cell :=
  { id := "bohnemeyer2004_waltal"
    lexeme := Lexemes.stand_up
    cell := {}
    form := "wa'l-tal"
    source := [
      ⟨"bohnemeyer-2004", "(24)"⟩
    ] }

def kultal : Form Cell :=
  { id := "bohnemeyer2004_kultal"
    lexeme := Lexemes.sit_down
    cell := {}
    form := "kul-tal"
    source := [
      ⟨"bohnemeyer-2004", "(24)"⟩
    ] }

def chiltal : Form Cell :=
  { id := "bohnemeyer2004_chiltal"
    lexeme := Lexemes.lie_down
    cell := {}
    form := "chil-tal"
    source := [
      ⟨"bohnemeyer-2004", "(24)"⟩
    ] }

def xoltal : Form Cell :=
  { id := "bohnemeyer2004_xoltal"
    lexeme := Lexemes.kneel
    cell := {}
    form := "xol-tal"
    source := [
      ⟨"bohnemeyer-2004", "(24)"⟩
    ] }

def meyah_t : Form Cell :=
  { id := "bohnemeyer2004_meyah_t"
    lexeme := Lexemes.make
    cell := {}
    form := "meyah-t"
    morphs := ["meyah", "t"]
    source := [
      ⟨"bohnemeyer-2004", "(4b)"⟩
    ] }

def baax_t : Form Cell :=
  { id := "bohnemeyer2004_baax_t"
    lexeme := Lexemes.play_with
    cell := {}
    form := "bàax-t"
    morphs := ["bàax", "t"]
    source := [
      ⟨"bohnemeyer-2004", "(5b)"⟩
    ] }

def kim_s : Form Cell :=
  { id := "bohnemeyer2004_kim_s"
    lexeme := Lexemes.kill
    cell := {}
    form := "kim-s"
    morphs := ["kim", "s"]
    source := [
      ⟨"bohnemeyer-2004", "(6b)"⟩
    ] }

def luub_s : Form Cell :=
  { id := "bohnemeyer2004_luub_s"
    lexeme := Lexemes.fell
    cell := {}
    form := "lúub-s"
    morphs := ["lúub", "s"]
    source := [
      ⟨"bohnemeyer-2004", "(7b)"⟩
    ] }

def peek_s : Form Cell :=
  { id := "bohnemeyer2004_peek_s"
    lexeme := Lexemes.cause_to_move
    cell := {}
    form := "péek-s"
    morphs := ["péek", "s"]
    source := [
      ⟨"bohnemeyer-2004", "(8b)"⟩
    ] }

def haan_t : Form Cell :=
  { id := "bohnemeyer2004_haan_t"
    lexeme := Lexemes.eat_something
    cell := {}
    form := "hàan-t"
    morphs := ["hàan", "t"]
    source := [
      ⟨"bohnemeyer-2004", "(9b)"⟩
    ] }

def balak_t : Form Cell :=
  { id := "bohnemeyer2004_balak_t"
    lexeme := Lexemes.cause_to_roll
    cell := {}
    form := "balak'-t"
    morphs := ["balak'", "t"]
    source := [
      ⟨"bohnemeyer-2004", "(10b)"⟩
    ] }

def tsiirin_t : Form Cell :=
  { id := "bohnemeyer2004_tsiirin_t"
    lexeme := Lexemes.cause_to_buzz
    cell := {}
    form := "tsíirin-t"
    morphs := ["tsíirin", "t"]
    source := [
      ⟨"bohnemeyer-2004", "(11b)"⟩
    ] }

def wal_kunt : Form Cell :=
  { id := "bohnemeyer2004_wal_kunt"
    lexeme := Lexemes.erect
    cell := {}
    form := "wa'l-kunt"
    morphs := ["wa'l", "kunt"]
    source := [
      ⟨"bohnemeyer-2004", "(25)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Class` column, the stem class, by status pattern. -/
  stemClass : StemClass
  /-- The `Causation` column, the causation type the paper assigns an intransitive base. -/
  causation : Option Causation := none
  deriving DecidableEq, Repr

def meyah.analysis : Analysis :=
  { form := meyah,
    stemClass := StemClass.active,
    causation := some Causation.internal }

def baaxal.analysis : Analysis :=
  { form := baaxal,
    stemClass := StemClass.active,
    causation := some Causation.internal }

def haan.analysis : Analysis :=
  { form := haan,
    stemClass := StemClass.inactive,
    causation := some Causation.internal }

def balak.analysis : Analysis :=
  { form := balak,
    stemClass := StemClass.active,
    causation := some Causation.external }

def peek.analysis : Analysis :=
  { form := peek,
    stemClass := StemClass.active,
    causation := some Causation.external }

def tsiirin.analysis : Analysis :=
  { form := tsiirin,
    stemClass := StemClass.active,
    causation := some Causation.external }

def nikich.analysis : Analysis :=
  { form := nikich,
    stemClass := StemClass.active,
    causation := some Causation.external }

def chiik.analysis : Analysis :=
  { form := chiik,
    stemClass := StemClass.active,
    causation := some Causation.external }

def haarax.analysis : Analysis :=
  { form := haarax,
    stemClass := StemClass.active,
    causation := some Causation.external }

def huuy.analysis : Analysis :=
  { form := huuy,
    stemClass := StemClass.active,
    causation := some Causation.external }

def mosoon.analysis : Analysis :=
  { form := mosoon,
    stemClass := StemClass.active,
    causation := some Causation.external }

def pirix.analysis : Analysis :=
  { form := pirix,
    stemClass := StemClass.active,
    causation := some Causation.external }

def walak.analysis : Analysis :=
  { form := walak,
    stemClass := StemClass.active,
    causation := some Causation.external }

def kim.analysis : Analysis :=
  { form := kim,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def luub.analysis : Analysis :=
  { form := luub,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def kan.analysis : Analysis :=
  { form := kan,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def lab.analysis : Analysis :=
  { form := lab,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def nak.analysis : Analysis :=
  { form := nak,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def tiil.analysis : Analysis :=
  { form := tiil,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def tsuk.analysis : Analysis :=
  { form := tsuk,
    stemClass := StemClass.inactive,
    causation := some Causation.external }

def booxtal.analysis : Analysis :=
  { form := booxtal,
    stemClass := StemClass.inchoative,
    causation := some Causation.external }

def chichantal.analysis : Analysis :=
  { form := chichantal,
    stemClass := StemClass.inchoative,
    causation := some Causation.external }

def waltal.analysis : Analysis :=
  { form := waltal,
    stemClass := StemClass.positional,
    causation := some Causation.external }

def kultal.analysis : Analysis :=
  { form := kultal,
    stemClass := StemClass.positional,
    causation := some Causation.external }

def chiltal.analysis : Analysis :=
  { form := chiltal,
    stemClass := StemClass.positional,
    causation := some Causation.external }

def xoltal.analysis : Analysis :=
  { form := xoltal,
    stemClass := StemClass.positional,
    causation := some Causation.external }

def meyah_t.analysis : Analysis :=
  { form := meyah_t,
    stemClass := StemClass.transitive }

def baax_t.analysis : Analysis :=
  { form := baax_t,
    stemClass := StemClass.transitive }

def kim_s.analysis : Analysis :=
  { form := kim_s,
    stemClass := StemClass.transitive }

def luub_s.analysis : Analysis :=
  { form := luub_s,
    stemClass := StemClass.transitive }

def peek_s.analysis : Analysis :=
  { form := peek_s,
    stemClass := StemClass.transitive }

def haan_t.analysis : Analysis :=
  { form := haan_t,
    stemClass := StemClass.transitive }

def balak_t.analysis : Analysis :=
  { form := balak_t,
    stemClass := StemClass.transitive }

def tsiirin_t.analysis : Analysis :=
  { form := tsiirin_t,
    stemClass := StemClass.transitive }

def wal_kunt.analysis : Analysis :=
  { form := wal_kunt,
    stemClass := StemClass.transitive }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.work, Lexemes.play, Lexemes.eat, Lexemes.roll, Lexemes.move,
  Lexemes.buzz, Lexemes.squeak, Lexemes.shake, Lexemes.slide, Lexemes.stir, Lexemes.whirl,
  Lexemes.flick, Lexemes.turn, Lexemes.die, Lexemes.fall, Lexemes.get_tired, Lexemes.deteriorate,
  Lexemes.ascend, Lexemes.last, Lexemes.rot, Lexemes.blacken, Lexemes.shrink, Lexemes.stand_up,
  Lexemes.sit_down, Lexemes.lie_down, Lexemes.kneel, Lexemes.make, Lexemes.play_with, Lexemes.kill,
  Lexemes.fell, Lexemes.cause_to_move, Lexemes.eat_something, Lexemes.cause_to_roll,
  Lexemes.cause_to_buzz, Lexemes.erect]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [meyah, baaxal, haan, balak, peek, tsiirin, nikich, chiik, haarax,
  huuy, mosoon, pirix, walak, kim, luub, kan, lab, nak, tiil, tsuk, booxtal, chichantal, waltal,
  kultal, chiltal, xoltal, meyah_t, baax_t, kim_s, luub_s, peek_s, haan_t, balak_t, tsiirin_t,
  wal_kunt]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "bohnemeyer2004_r_meyah_t", form := meyah, target := meyah_t, relation := "applicative",
    source := [
      ⟨"bohnemeyer-2004", "(4b)"⟩
    ] },
  { id := "bohnemeyer2004_r_baax_t", form := baaxal, target := baax_t, relation := "applicative",
    source := [
      ⟨"bohnemeyer-2004", "(5b)"⟩
    ] },
  { id := "bohnemeyer2004_r_kim_s", form := kim, target := kim_s, relation := "causative",
    source := [
      ⟨"bohnemeyer-2004", "(6b)"⟩
    ] },
  { id := "bohnemeyer2004_r_luub_s", form := luub, target := luub_s, relation := "causative",
    source := [
      ⟨"bohnemeyer-2004", "(7b)"⟩
    ] },
  { id := "bohnemeyer2004_r_peek_s", form := peek, target := peek_s, relation := "causative",
    source := [
      ⟨"bohnemeyer-2004", "(8b)"⟩
    ] },
  { id := "bohnemeyer2004_r_haan_t", form := haan, target := haan_t, relation := "applicative",
    source := [
      ⟨"bohnemeyer-2004", "(9b)"⟩
    ] },
  { id := "bohnemeyer2004_r_balak_t", form := balak, target := balak_t, relation := "applicative",
    source := [
      ⟨"bohnemeyer-2004", "(10b)"⟩
    ] },
  { id := "bohnemeyer2004_r_tsiirin_t", form := tsiirin, target := tsiirin_t,
    relation := "applicative", source := [
      ⟨"bohnemeyer-2004", "(11b)"⟩
    ] },
  { id := "bohnemeyer2004_r_wal_kunt", form := waltal, target := wal_kunt, relation := "causative",
    source := [
      ⟨"bohnemeyer-2004", "(25)"⟩
    ] }]

/-- Every relation the sources assert, between the forms' analyses. -/
def analysisRelations : List (FormRelation Analysis) := [
  { id := "bohnemeyer2004_r_meyah_t", form := meyah.analysis, target := meyah_t.analysis,
    relation := "applicative", source := [
      ⟨"bohnemeyer-2004", "(4b)"⟩
    ] },
  { id := "bohnemeyer2004_r_baax_t", form := baaxal.analysis, target := baax_t.analysis,
    relation := "applicative", source := [
      ⟨"bohnemeyer-2004", "(5b)"⟩
    ] },
  { id := "bohnemeyer2004_r_kim_s", form := kim.analysis, target := kim_s.analysis,
    relation := "causative", source := [
      ⟨"bohnemeyer-2004", "(6b)"⟩
    ] },
  { id := "bohnemeyer2004_r_luub_s", form := luub.analysis, target := luub_s.analysis,
    relation := "causative", source := [
      ⟨"bohnemeyer-2004", "(7b)"⟩
    ] },
  { id := "bohnemeyer2004_r_peek_s", form := peek.analysis, target := peek_s.analysis,
    relation := "causative", source := [
      ⟨"bohnemeyer-2004", "(8b)"⟩
    ] },
  { id := "bohnemeyer2004_r_haan_t", form := haan.analysis, target := haan_t.analysis,
    relation := "applicative", source := [
      ⟨"bohnemeyer-2004", "(9b)"⟩
    ] },
  { id := "bohnemeyer2004_r_balak_t", form := balak.analysis, target := balak_t.analysis,
    relation := "applicative", source := [
      ⟨"bohnemeyer-2004", "(10b)"⟩
    ] },
  { id := "bohnemeyer2004_r_tsiirin_t", form := tsiirin.analysis, target := tsiirin_t.analysis,
    relation := "applicative", source := [
      ⟨"bohnemeyer-2004", "(11b)"⟩
    ] },
  { id := "bohnemeyer2004_r_wal_kunt", form := waltal.analysis, target := wal_kunt.analysis,
    relation := "causative", source := [
      ⟨"bohnemeyer-2004", "(25)"⟩
    ] }]

/-- Every analysis of the data. -/
def analyses : List Analysis := [meyah.analysis, baaxal.analysis, haan.analysis, balak.analysis,
  peek.analysis, tsiirin.analysis, nikich.analysis, chiik.analysis, haarax.analysis, huuy.analysis,
  mosoon.analysis, pirix.analysis, walak.analysis, kim.analysis, luub.analysis, kan.analysis,
  lab.analysis, nak.analysis, tiil.analysis, tsuk.analysis, booxtal.analysis, chichantal.analysis,
  waltal.analysis, kultal.analysis, chiltal.analysis, xoltal.analysis, meyah_t.analysis,
  baax_t.analysis, kim_s.analysis, luub_s.analysis, peek_s.analysis, haan_t.analysis,
  balak_t.analysis, tsiirin_t.analysis, wal_kunt.analysis]

end Bohnemeyer2004.Wordlist
