module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `GokselKerslake2005` — typed example data

Auto-generated from `Linglib/Data/Examples/GokselKerslake2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GokselKerslake2005.Examples`.
-/

@[expose] public section

namespace GokselKerslake2005.Examples

def kizin : Datum :=
  { id := "gokselkerslake2005_kizin"
    source := ⟨"goksel-kerslake-2005", "3.2.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "kızın"
    glossedTokens := [("kız-ın", "")]
    glossedWords := [⟨['k', 'ı', 'z', '-', 'ı', 'n'], [], [⟨['k', 'ı', 'z'], [], none⟩, ⟨['ı', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "kiz"⟩]
    paperFeatures := [("suffix", "2SG.POSS")] }

def elin : Datum :=
  { id := "gokselkerslake2005_elin"
    source := ⟨"goksel-kerslake-2005", "3.2.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "elin"
    glossedTokens := [("el-in", "")]
    glossedWords := [⟨['e', 'l', '-', 'i', 'n'], [], [⟨['e', 'l'], [], none⟩, ⟨['i', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "el"⟩]
    paperFeatures := [("suffix", "2SG.POSS")] }

def kolun : Datum :=
  { id := "gokselkerslake2005_kolun"
    source := ⟨"goksel-kerslake-2005", "3.2.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "kolun"
    glossedTokens := [("kol-un", "")]
    glossedWords := [⟨['k', 'o', 'l', '-', 'u', 'n'], [], [⟨['k', 'o', 'l'], [], none⟩, ⟨['u', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "kol"⟩]
    paperFeatures := [("suffix", "2SG.POSS")] }

def gozun : Datum :=
  { id := "gokselkerslake2005_gozun"
    source := ⟨"goksel-kerslake-2005", "3.2.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "gözün"
    glossedTokens := [("göz-ün", "")]
    glossedWords := [⟨['g', 'ö', 'z', '-', 'ü', 'n'], [], [⟨['g', 'ö', 'z'], [], none⟩, ⟨['ü', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "goz"⟩]
    paperFeatures := [("suffix", "2SG.POSS")] }

def otobusler : Datum :=
  { id := "gokselkerslake2005_otobusler"
    source := ⟨"goksel-kerslake-2005", "3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "otobüsler"
    glossedTokens := [("otobüs-ler", "")]
    glossedWords := [⟨['o', 't', 'o', 'b', 'ü', 's', '-', 'l', 'e', 'r'], [], [⟨['o', 't', 'o', 'b', 'ü', 's'], [], none⟩, ⟨['l', 'e', 'r'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "otobus"⟩]
    paperFeatures := [("suffix", "PL")] }

def uzuldunuz : Datum :=
  { id := "gokselkerslake2005_uzuldunuz"
    source := ⟨"goksel-kerslake-2005", "3.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "üzüldünüz"
    glossedTokens := [("üz-ül-dü-nüz", "")]
    glossedWords := [⟨['ü', 'z', '-', 'ü', 'l', '-', 'd', 'ü', '-', 'n', 'ü', 'z'], [], [⟨['ü', 'z'], [], none⟩, ⟨['ü', 'l'], [], some '-'⟩, ⟨['d', 'ü'], [], some '-'⟩, ⟨['n', 'ü', 'z'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "uz"⟩]
    paperFeatures := [("suffix", "PASS"), ("suffix", "PF"), ("suffix", "2PL")] }

def goruyorum : Datum :=
  { id := "gokselkerslake2005_goruyorum"
    source := ⟨"goksel-kerslake-2005", "3.4 (vi)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "görüyorum"
    glossedTokens := [("görüyorum", "")]
    glossedWords := [⟨['g', 'ö', 'r', 'ü', 'y', 'o', 'r', 'u', 'm'], [], [⟨['g', 'ö', 'r', 'ü', 'y', 'o', 'r', 'u', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "gor"⟩]
    paperFeatures := [("suffix", "IMPF"), ("suffix", "1SG")] }

def bakmisken : Datum :=
  { id := "gokselkerslake2005_bakmisken"
    source := ⟨"goksel-kerslake-2005", "3.4 (vi)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "bakmışken"
    glossedTokens := [("bakmışken", "")]
    glossedWords := [⟨['b', 'a', 'k', 'm', 'ı', 'ş', 'k', 'e', 'n'], [], [⟨['b', 'a', 'k', 'm', 'ı', 'ş', 'k', 'e', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "bak"⟩]
    paperFeatures := [("suffix", "EV/PF"), ("suffix", "CV")] }

def golu : Datum :=
  { id := "gokselkerslake2005_golu"
    source := ⟨"goksel-kerslake-2005", "3.4 (iv)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "golü"
    glossedTokens := [("gol-ü", "goal-3SG.POSS")]
    glossedWords := [⟨['g', 'o', 'l', '-', 'ü'], ['g', 'o', 'a', 'l', '-', '3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], [⟨['g', 'o', 'l'], ['g', 'o', 'a', 'l'], none⟩, ⟨['ü'], ['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "gol"⟩]
    paperFeatures := [("suffix", "3SG.POSS")] }

def halim : Datum :=
  { id := "gokselkerslake2005_halim"
    source := ⟨"goksel-kerslake-2005", "3.4 (iv)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "halim"
    glossedTokens := [("hal-im", "condition-1SG.POSS")]
    glossedWords := [⟨['h', 'a', 'l', '-', 'i', 'm'], ['c', 'o', 'n', 'd', 'i', 't', 'i', 'o', 'n', '-', '1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], [⟨['h', 'a', 'l'], ['c', 'o', 'n', 'd', 'i', 't', 'i', 'o', 'n'], none⟩, ⟨['i', 'm'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "hal"⟩]
    paperFeatures := [("suffix", "1SG.POSS")] }

def all : List Datum := [kizin, elin, kolun, gozun, otobusler, uzuldunuz, goruyorum, bakmisken, golu, halim]

/-- The suffixes of the word under test, in order, under the grammar's glosses. -/
inductive Suffix where
  /-- 1SG.POSS: the first-person singular possessive -(I)m -/
  | poss1sg
  /-- 2SG.POSS: the second-person singular possessive -(I)n -/
  | poss2sg
  /-- 3SG.POSS: the third-person singular possessive -(s)I -/
  | poss3sg
  /-- PL: the plural -lAr -/
  | pl
  /-- PASS: the passive -Il -/
  | pass
  /-- PF: the perfective -DI -/
  | pf
  /-- EV/PF: the evidential and perfective -mIş -/
  | evPf
  /-- IMPF: the imperfective -(I)yor -/
  | impf
  /-- CV: the converbial marker -(y)ken -/
  | cv
  /-- 1SG: a first-person singular person marker -/
  | p1sg
  /-- 2PL: a second-person plural person marker -/
  | p2pl
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `suffix`. -/
def suffixes (e : Datum) : List Suffix :=
  (e.features "suffix").filterMap (List.lookup · [("1SG.POSS", .poss1sg), ("2SG.POSS", .poss2sg), ("3SG.POSS", .poss3sg), ("PL", .pl),
    ("PASS", .pass), ("PF", .pf), ("EV/PF", .evPf), ("IMPF", .impf), ("CV", .cv),
    ("1SG", .p1sg), ("2PL", .p2pl)])

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- stem: the word under test, a form of the lexeme that is its stem -/
  | stem
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("stem", .stem)]

/-- The stems of the words under test. -/
inductive Lexeme where
  /-- kiz: kız 'girl, daughter' -/
  | kiz
  /-- el: el 'hand' -/
  | el
  /-- kol: kol 'arm' -/
  | kol
  /-- goz: göz 'eye' -/
  | goz
  /-- otobus: otobüs 'bus', a loan -/
  | otobus
  /-- uz: üz- 'sadden' -/
  | uz
  /-- gor: gör- 'see' -/
  | gor
  /-- bak: bak- 'look' -/
  | bak
  /-- gol: gol 'goal', a loan ending in a palatal l -/
  | gol
  /-- hal: hal 'condition', a loan ending in a palatal l -/
  | hal
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("kiz", .kiz), ("el", .el), ("kol", .kol), ("goz", .goz), ("otobus", .otobus), ("uz", .uz), ("gor", .gor), ("bak", .bak), ("gol", .gol), ("hal", .hal)])

/-- The grammar's example words. -/
inductive Example where
  | kizin
  | elin
  | kolun
  | gozun
  | otobusler
  | uzuldunuz
  | goruyorum
  | bakmisken
  | golu
  | halim
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.kizin, .elin, .kolun, .gozun, .otobusler, .uzuldunuz, .goruyorum, .bakmisken, .golu, .halim]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .kizin => _root_.GokselKerslake2005.Examples.kizin
  | .elin => _root_.GokselKerslake2005.Examples.elin
  | .kolun => _root_.GokselKerslake2005.Examples.kolun
  | .gozun => _root_.GokselKerslake2005.Examples.gozun
  | .otobusler => _root_.GokselKerslake2005.Examples.otobusler
  | .uzuldunuz => _root_.GokselKerslake2005.Examples.uzuldunuz
  | .goruyorum => _root_.GokselKerslake2005.Examples.goruyorum
  | .bakmisken => _root_.GokselKerslake2005.Examples.bakmisken
  | .golu => _root_.GokselKerslake2005.Examples.golu
  | .halim => _root_.GokselKerslake2005.Examples.halim

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.GokselKerslake2005.Examples.all := rfl

/-- The values the example records under `suffix`. -/
def Example.suffixes : Example → List Suffix
  | .kizin => [.poss2sg]
  | .elin => [.poss2sg]
  | .kolun => [.poss2sg]
  | .gozun => [.poss2sg]
  | .otobusler => [.pl]
  | .uzuldunuz => [.pass, .pf, .p2pl]
  | .goruyorum => [.impf, .p1sg]
  | .bakmisken => [.evPf, .cv]
  | .golu => [.poss3sg]
  | .halim => [.poss1sg]

theorem Example.suffixes_datum :
    ∀ x : Example, _root_.GokselKerslake2005.Examples.suffixes x.datum = x.suffixes := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .kizin => [(.stem, .kiz)]
  | .elin => [(.stem, .el)]
  | .kolun => [(.stem, .kol)]
  | .gozun => [(.stem, .goz)]
  | .otobusler => [(.stem, .otobus)]
  | .uzuldunuz => [(.stem, .uz)]
  | .goruyorum => [(.stem, .gor)]
  | .bakmisken => [(.stem, .bak)]
  | .golu => [(.stem, .gol)]
  | .halim => [(.stem, .hal)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.GokselKerslake2005.Examples.label? · = some l)).filterMap _root_.GokselKerslake2005.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end GokselKerslake2005.Examples
