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

def kaldi : Datum :=
  { id := "gokselkerslake2005_kaldi"
    source := ⟨"goksel-kerslake-2005", "6.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "kaldı"
    glossedTokens := [("kal-dı", "")]
    glossedWords := [⟨['k', 'a', 'l', '-', 'd', 'ı'], [], [⟨['k', 'a', 'l'], [], none⟩, ⟨['d', 'ı'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "kal"⟩]
    paperFeatures := [("suffix", "PF")] }

def dustu : Datum :=
  { id := "gokselkerslake2005_dustu"
    source := ⟨"goksel-kerslake-2005", "6.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "düştü"
    glossedTokens := [("düş-tü", "")]
    glossedWords := [⟨['d', 'ü', 'ş', '-', 't', 'ü'], [], [⟨['d', 'ü', 'ş'], [], none⟩, ⟨['t', 'ü'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "dus"⟩]
    paperFeatures := [("suffix", "PF")] }

def pulum : Datum :=
  { id := "gokselkerslake2005_pulum"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "pulum"
    glossedTokens := [("pul-um", "")]
    glossedWords := [⟨['p', 'u', 'l', '-', 'u', 'm'], [], [⟨['p', 'u', 'l'], [], none⟩, ⟨['u', 'm'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "pul"⟩]
    paperFeatures := [("suffix", "1SG.POSS")] }

def gorur : Datum :=
  { id := "gokselkerslake2005_gorur"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "görür"
    glossedTokens := [("gör-ür", "")]
    glossedWords := [⟨['g', 'ö', 'r', '-', 'ü', 'r'], [], [⟨['g', 'ö', 'r'], [], none⟩, ⟨['ü', 'r'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "gor"⟩]
    paperFeatures := [("suffix", "AOR")] }

def arar : Datum :=
  { id := "gokselkerslake2005_arar"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "arar"
    glossedTokens := [("ara-r", "")]
    glossedWords := [⟨['a', 'r', 'a', '-', 'r'], [], [⟨['a', 'r', 'a'], [], none⟩, ⟨['r'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ara"⟩]
    paperFeatures := [("suffix", "AOR")] }

def soracak : Datum :=
  { id := "gokselkerslake2005_soracak"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "soracak"
    glossedTokens := [("sor-acak", "")]
    glossedWords := [⟨['s', 'o', 'r', '-', 'a', 'c', 'a', 'k'], [], [⟨['s', 'o', 'r'], [], none⟩, ⟨['a', 'c', 'a', 'k'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "sor"⟩]
    paperFeatures := [("suffix", "FUT")] }

def atlayacak : Datum :=
  { id := "gokselkerslake2005_atlayacak"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "atlayacak"
    glossedTokens := [("atla-yacak", "")]
    glossedWords := [⟨['a', 't', 'l', 'a', '-', 'y', 'a', 'c', 'a', 'k'], [], [⟨['a', 't', 'l', 'a'], [], none⟩, ⟨['y', 'a', 'c', 'a', 'k'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "atla"⟩]
    paperFeatures := [("suffix", "FUT")] }

def sunanin : Datum :=
  { id := "gokselkerslake2005_sunanin"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Sunanın"
    glossedTokens := [("Suna-nın", "")]
    glossedWords := [⟨['S', 'u', 'n', 'a', '-', 'n', 'ı', 'n'], [], [⟨['S', 'u', 'n', 'a'], [], none⟩, ⟨['n', 'ı', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "suna"⟩]
    paperFeatures := [("suffix", "GEN")] }

def betulun : Datum :=
  { id := "gokselkerslake2005_betulun"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Betülün"
    glossedTokens := [("Betül-ün", "")]
    glossedWords := [⟨['B', 'e', 't', 'ü', 'l', '-', 'ü', 'n'], [], [⟨['B', 'e', 't', 'ü', 'l'], [], none⟩, ⟨['ü', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "betul"⟩]
    paperFeatures := [("suffix", "GEN")] }

def eminenin : Datum :=
  { id := "gokselkerslake2005_eminenin"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Eminenin"
    glossedTokens := [("Emine-nin", "")]
    glossedWords := [⟨['E', 'm', 'i', 'n', 'e', '-', 'n', 'i', 'n'], [], [⟨['E', 'm', 'i', 'n', 'e'], [], none⟩, ⟨['n', 'i', 'n'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "emine"⟩]
    paperFeatures := [("suffix", "GEN")] }

def emineye : Datum :=
  { id := "gokselkerslake2005_emineye"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Emineye"
    glossedTokens := [("Emine-ye", "")]
    glossedWords := [⟨['E', 'm', 'i', 'n', 'e', '-', 'y', 'e'], [], [⟨['E', 'm', 'i', 'n', 'e'], [], none⟩, ⟨['y', 'e'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "emine"⟩]
    paperFeatures := [("suffix", "DAT")] }

def evi : Datum :=
  { id := "gokselkerslake2005_evi"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "evi"
    glossedTokens := [("ev-i", "")]
    glossedWords := [⟨['e', 'v', '-', 'i'], [], [⟨['e', 'v'], [], none⟩, ⟨['i'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ev"⟩]
    paperFeatures := [("suffix", "3SG.POSS")] }

def elbisesi : Datum :=
  { id := "gokselkerslake2005_elbisesi"
    source := ⟨"goksel-kerslake-2005", "6.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "elbisesi"
    glossedTokens := [("elbise-si", "")]
    glossedWords := [⟨['e', 'l', 'b', 'i', 's', 'e', '-', 's', 'i'], [], [⟨['e', 'l', 'b', 'i', 's', 'e'], [], none⟩, ⟨['s', 'i'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "elbise"⟩]
    paperFeatures := [("suffix", "3SG.POSS")] }

def evim : Datum :=
  { id := "gokselkerslake2005_evim"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "evim"
    glossedTokens := [("ev-im", "")]
    glossedWords := [⟨['e', 'v', '-', 'i', 'm'], [], [⟨['e', 'v'], [], none⟩, ⟨['i', 'm'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ev"⟩]
    paperFeatures := [("suffix", "1SG.POSS")] }

def arabam : Datum :=
  { id := "gokselkerslake2005_arabam"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "arabam"
    glossedTokens := [("araba-m", "")]
    glossedWords := [⟨['a', 'r', 'a', 'b', 'a', '-', 'm'], [], [⟨['a', 'r', 'a', 'b', 'a'], [], none⟩, ⟨['m'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "araba"⟩]
    paperFeatures := [("suffix", "1SG.POSS")] }

def eviniz : Datum :=
  { id := "gokselkerslake2005_eviniz"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "eviniz"
    glossedTokens := [("ev-iniz", "")]
    glossedWords := [⟨['e', 'v', '-', 'i', 'n', 'i', 'z'], [], [⟨['e', 'v'], [], none⟩, ⟨['i', 'n', 'i', 'z'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ev"⟩]
    paperFeatures := [("suffix", "2PL.POSS")] }

def arabaniz : Datum :=
  { id := "gokselkerslake2005_arabaniz"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "arabanız"
    glossedTokens := [("araba-nız", "")]
    glossedWords := [⟨['a', 'r', 'a', 'b', 'a', '-', 'n', 'ı', 'z'], [], [⟨['a', 'r', 'a', 'b', 'a'], [], none⟩, ⟨['n', 'ı', 'z'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "araba"⟩]
    paperFeatures := [("suffix", "2PL.POSS")] }

def evimiz : Datum :=
  { id := "gokselkerslake2005_evimiz"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "evimiz"
    glossedTokens := [("ev-imiz", "")]
    glossedWords := [⟨['e', 'v', '-', 'i', 'm', 'i', 'z'], [], [⟨['e', 'v'], [], none⟩, ⟨['i', 'm', 'i', 'z'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ev"⟩]
    paperFeatures := [("suffix", "1PL.POSS")] }

def arabamiz : Datum :=
  { id := "gokselkerslake2005_arabamiz"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "arabamız"
    glossedTokens := [("araba-mız", "")]
    glossedWords := [⟨['a', 'r', 'a', 'b', 'a', '-', 'm', 'ı', 'z'], [], [⟨['a', 'r', 'a', 'b', 'a'], [], none⟩, ⟨['m', 'ı', 'z'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "araba"⟩]
    paperFeatures := [("suffix", "1PL.POSS")] }

def arabasi : Datum :=
  { id := "gokselkerslake2005_arabasi"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "arabası"
    glossedTokens := [("araba-sı", "")]
    glossedWords := [⟨['a', 'r', 'a', 'b', 'a', '-', 's', 'ı'], [], [⟨['a', 'r', 'a', 'b', 'a'], [], none⟩, ⟨['s', 'ı'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "araba"⟩]
    paperFeatures := [("suffix", "3SG.POSS")] }

def tepesinde : Datum :=
  { id := "gokselkerslake2005_tepesinde"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "tepesinde"
    glossedTokens := [("tepesinde", "")]
    glossedWords := [⟨['t', 'e', 'p', 'e', 's', 'i', 'n', 'd', 'e'], [], [⟨['t', 'e', 'p', 'e', 's', 'i', 'n', 'd', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "tepe"⟩]
    paperFeatures := [("suffix", "3SG.POSS"), ("suffix", "LOC")] }

def yuzune : Datum :=
  { id := "gokselkerslake2005_yuzune"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "yüzüne"
    glossedTokens := [("yüzüne", "")]
    glossedWords := [⟨['y', 'ü', 'z', 'ü', 'n', 'e'], [], [⟨['y', 'ü', 'z', 'ü', 'n', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "yuz"⟩]
    paperFeatures := [("suffix", "3SG.POSS"), ("suffix", "DAT")] }

def elbiselerine : Datum :=
  { id := "gokselkerslake2005_elbiselerine"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "elbiselerine"
    glossedTokens := [("elbiselerine", "")]
    glossedWords := [⟨['e', 'l', 'b', 'i', 's', 'e', 'l', 'e', 'r', 'i', 'n', 'e'], [], [⟨['e', 'l', 'b', 'i', 's', 'e', 'l', 'e', 'r', 'i', 'n', 'e'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "elbise"⟩]
    paperFeatures := [("suffix", "3PL.POSS"), ("suffix", "DAT")] }

def tepesi : Datum :=
  { id := "gokselkerslake2005_tepesi"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "tepesi"
    glossedTokens := [("tepesi", "")]
    glossedWords := [⟨['t', 'e', 'p', 'e', 's', 'i'], [], [⟨['t', 'e', 'p', 'e', 's', 'i'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "tepe"⟩]
    paperFeatures := [("suffix", "3SG.POSS")] }

def odamda : Datum :=
  { id := "gokselkerslake2005_odamda"
    source := ⟨"goksel-kerslake-2005", "8.1.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "odamda"
    glossedTokens := [("odamda", "")]
    glossedWords := [⟨['o', 'd', 'a', 'm', 'd', 'a'], [], [⟨['o', 'd', 'a', 'm', 'd', 'a'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "oda"⟩]
    paperFeatures := [("suffix", "1SG.POSS"), ("suffix", "LOC")] }

def masaya : Datum :=
  { id := "gokselkerslake2005_masaya"
    source := ⟨"goksel-kerslake-2005", "8.1.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "masaya"
    glossedTokens := [("masaya", "")]
    glossedWords := [⟨['m', 'a', 's', 'a', 'y', 'a'], [], [⟨['m', 'a', 's', 'a', 'y', 'a'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "masa"⟩]
    paperFeatures := [("suffix", "DAT")] }

def okuldayim : Datum :=
  { id := "gokselkerslake2005_okuldayim"
    source := ⟨"goksel-kerslake-2005", "8.4"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "okuldayım"
    glossedTokens := [("okuldayım", "")]
    glossedWords := [⟨['o', 'k', 'u', 'l', 'd', 'a', 'y', 'ı', 'm'], [], [⟨['o', 'k', 'u', 'l', 'd', 'a', 'y', 'ı', 'm'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "okul"⟩]
    paperFeatures := [("suffix", "LOC"), ("suffix", "1SG")] }

def evdeydik : Datum :=
  { id := "gokselkerslake2005_evdeydik"
    source := ⟨"goksel-kerslake-2005", "8.4"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "evdeydik"
    glossedTokens := [("evdeydik", "")]
    glossedWords := [⟨['e', 'v', 'd', 'e', 'y', 'd', 'i', 'k'], [], [⟨['e', 'v', 'd', 'e', 'y', 'd', 'i', 'k'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ev"⟩]
    paperFeatures := [("suffix", "LOC"), ("suffix", "P.COP"), ("suffix", "1PL")] }

def hastaysalar : Datum :=
  { id := "gokselkerslake2005_hastaysalar"
    source := ⟨"goksel-kerslake-2005", "8.4"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "hastaysalar"
    glossedTokens := [("hastaysalar", "")]
    glossedWords := [⟨['h', 'a', 's', 't', 'a', 'y', 's', 'a', 'l', 'a', 'r'], [], [⟨['h', 'a', 's', 't', 'a', 'y', 's', 'a', 'l', 'a', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "hasta"⟩]
    paperFeatures := [("suffix", "COND.COP"), ("suffix", "3PL")] }

def katsaydilar : Datum :=
  { id := "gokselkerslake2005_katsaydilar"
    source := ⟨"goksel-kerslake-2005", "8.4"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "katsaydılar"
    glossedTokens := [("kat-sa-ydı-lar", "")]
    glossedWords := [⟨['k', 'a', 't', '-', 's', 'a', '-', 'y', 'd', 'ı', '-', 'l', 'a', 'r'], [], [⟨['k', 'a', 't'], [], none⟩, ⟨['s', 'a'], [], some '-'⟩, ⟨['y', 'd', 'ı'], [], some '-'⟩, ⟨['l', 'a', 'r'], [], some '-'⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "kat"⟩]
    paperFeatures := [("suffix", "COND"), ("suffix", "P.COP"), ("suffix", "3PL")] }

def anliyor : Datum :=
  { id := "gokselkerslake2005_anliyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "anlıyor"
    glossedTokens := [("anlıyor", "")]
    glossedWords := [⟨['a', 'n', 'l', 'ı', 'y', 'o', 'r'], [], [⟨['a', 'n', 'l', 'ı', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "anla"⟩]
    paperFeatures := [("suffix", "IMPF")] }

def oksuyor : Datum :=
  { id := "gokselkerslake2005_oksuyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "okşuyor"
    glossedTokens := [("okşuyor", "")]
    glossedWords := [⟨['o', 'k', 'ş', 'u', 'y', 'o', 'r'], [], [⟨['o', 'k', 'ş', 'u', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "oksa"⟩]
    paperFeatures := [("suffix", "IMPF")] }

def bekliyor : Datum :=
  { id := "gokselkerslake2005_bekliyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "bekliyor"
    glossedTokens := [("bekliyor", "")]
    glossedWords := [⟨['b', 'e', 'k', 'l', 'i', 'y', 'o', 'r'], [], [⟨['b', 'e', 'k', 'l', 'i', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "bekle"⟩]
    paperFeatures := [("suffix", "IMPF")] }

def ozluyor : Datum :=
  { id := "gokselkerslake2005_ozluyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "özlüyor"
    glossedTokens := [("özlüyor", "")]
    glossedWords := [⟨['ö', 'z', 'l', 'ü', 'y', 'o', 'r'], [], [⟨['ö', 'z', 'l', 'ü', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ozle"⟩]
    paperFeatures := [("suffix", "IMPF")] }

def eriyor : Datum :=
  { id := "gokselkerslake2005_eriyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "eriyor"
    glossedTokens := [("eriyor", "")]
    glossedWords := [⟨['e', 'r', 'i', 'y', 'o', 'r'], [], [⟨['e', 'r', 'i', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "eri"⟩]
    paperFeatures := [("suffix", "IMPF")] }

def kuruyor : Datum :=
  { id := "gokselkerslake2005_kuruyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "kuruyor"
    glossedTokens := [("kuruyor", "")]
    glossedWords := [⟨['k', 'u', 'r', 'u', 'y', 'o', 'r'], [], [⟨['k', 'u', 'r', 'u', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "kuru"⟩]
    paperFeatures := [("suffix", "IMPF")] }

def saklamiyor : Datum :=
  { id := "gokselkerslake2005_saklamiyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "saklamıyor"
    glossedTokens := [("saklamıyor", "")]
    glossedWords := [⟨['s', 'a', 'k', 'l', 'a', 'm', 'ı', 'y', 'o', 'r'], [], [⟨['s', 'a', 'k', 'l', 'a', 'm', 'ı', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "sakla"⟩]
    paperFeatures := [("suffix", "NEG"), ("suffix", "IMPF")] }

def soylemiyor : Datum :=
  { id := "gokselkerslake2005_soylemiyor"
    source := ⟨"goksel-kerslake-2005", "8.2.3.3"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "söylemiyor"
    glossedTokens := [("söylemiyor", "")]
    glossedWords := [⟨['s', 'ö', 'y', 'l', 'e', 'm', 'i', 'y', 'o', 'r'], [], [⟨['s', 'ö', 'y', 'l', 'e', 'm', 'i', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "soyle"⟩]
    paperFeatures := [("suffix", "NEG"), ("suffix", "IMPF")] }

def anlamiyor : Datum :=
  { id := "gokselkerslake2005_anlamiyor"
    source := ⟨"goksel-kerslake-2005", "8.2.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "anlamıyor"
    glossedTokens := [("anlamıyor", "")]
    glossedWords := [⟨['a', 'n', 'l', 'a', 'm', 'ı', 'y', 'o', 'r'], [], [⟨['a', 'n', 'l', 'a', 'm', 'ı', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "anla"⟩]
    paperFeatures := [("suffix", "NEG"), ("suffix", "IMPF")] }

def gormuyor : Datum :=
  { id := "gokselkerslake2005_gormuyor"
    source := ⟨"goksel-kerslake-2005", "8.2.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "görmüyor"
    glossedTokens := [("görmüyor", "")]
    glossedWords := [⟨['g', 'ö', 'r', 'm', 'ü', 'y', 'o', 'r'], [], [⟨['g', 'ö', 'r', 'm', 'ü', 'y', 'o', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "gor"⟩]
    paperFeatures := [("suffix", "NEG"), ("suffix", "IMPF")] }

def evlerimizdeymisler : Datum :=
  { id := "gokselkerslake2005_evlerimizdeymisler"
    source := ⟨"goksel-kerslake-2005", "8.1 (2)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "Evlerimizdeymişler."
    glossedTokens := [("Ev-ler-imiz-de-ymiş-ler.", "home-PL-1PL.POSS-LOC-EV.COP-3PL")]
    glossedWords := [⟨['E', 'v', '-', 'l', 'e', 'r', '-', 'i', 'm', 'i', 'z', '-', 'd', 'e', '-', 'y', 'm', 'i', 'ş', '-', 'l', 'e', 'r', '.'], ['h', 'o', 'm', 'e', '-', 'P', 'L', '-', '1', 'P', 'L', '.', 'P', 'O', 'S', 'S', '-', 'L', 'O', 'C', '-', 'E', 'V', '.', 'C', 'O', 'P', '-', '3', 'P', 'L'], [⟨['E', 'v'], ['h', 'o', 'm', 'e'], none⟩, ⟨['l', 'e', 'r'], ['P', 'L'], some '-'⟩, ⟨['i', 'm', 'i', 'z'], ['1', 'P', 'L', '.', 'P', 'O', 'S', 'S'], some '-'⟩, ⟨['d', 'e'], ['L', 'O', 'C'], some '-'⟩, ⟨['y', 'm', 'i', 'ş'], ['E', 'V', '.', 'C', 'O', 'P'], some '-'⟩, ⟨['l', 'e', 'r'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ev"⟩]
    paperFeatures := [("suffix", "PL"), ("suffix", "1PL.POSS"), ("suffix", "LOC"), ("suffix", "EV.COP"), ("suffix", "3PL")] }

def yaptir : Datum :=
  { id := "gokselkerslake2005_yaptir"
    source := ⟨"goksel-kerslake-2005", "8.2.1.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "yaptır"
    glossedTokens := [("yaptır", "")]
    glossedWords := [⟨['y', 'a', 'p', 't', 'ı', 'r'], [], [⟨['y', 'a', 'p', 't', 'ı', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "yap"⟩]
    paperFeatures := [("suffix", "CAUS")] }

def koydur : Datum :=
  { id := "gokselkerslake2005_koydur"
    source := ⟨"goksel-kerslake-2005", "8.2.1.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "koydur"
    glossedTokens := [("koydur", "")]
    glossedWords := [⟨['k', 'o', 'y', 'd', 'u', 'r'], [], [⟨['k', 'o', 'y', 'd', 'u', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "koy"⟩]
    paperFeatures := [("suffix", "CAUS")] }

def oldur : Datum :=
  { id := "gokselkerslake2005_oldur"
    source := ⟨"goksel-kerslake-2005", "8.2.1.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "öldür"
    glossedTokens := [("öldür", "")]
    glossedWords := [⟨['ö', 'l', 'd', 'ü', 'r'], [], [⟨['ö', 'l', 'd', 'ü', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "ol"⟩]
    paperFeatures := [("suffix", "CAUS")] }

def doldur : Datum :=
  { id := "gokselkerslake2005_doldur"
    source := ⟨"goksel-kerslake-2005", "8.2.1.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1301"
    primaryText := "doldur"
    glossedTokens := [("doldur", "")]
    glossedWords := [⟨['d', 'o', 'l', 'd', 'u', 'r'], [], [⟨['d', 'o', 'l', 'd', 'u', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "stem", some "dol"⟩]
    paperFeatures := [("suffix", "CAUS")] }

def all : List Datum := [kizin, elin, kolun, gozun, otobusler, uzuldunuz, goruyorum, bakmisken, golu, halim, kaldi, dustu, pulum, gorur, arar, soracak, atlayacak, sunanin, betulun, eminenin, emineye, evi, elbisesi, evim, arabam, eviniz, arabaniz, evimiz, arabamiz, arabasi, tepesinde, yuzune, elbiselerine, tepesi, odamda, masaya, okuldayim, evdeydik, hastaysalar, katsaydilar, anliyor, oksuyor, bekliyor, ozluyor, eriyor, kuruyor, saklamiyor, soylemiyor, anlamiyor, gormuyor, evlerimizdeymisler, yaptir, koydur, oldur, doldur]

/-- The suffixes of the word under test, in order. -/
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
  /-- 1PL.POSS: the first-person plural possessive -(I)mIz -/
  | poss1pl
  /-- 2PL.POSS: the second-person plural possessive -(I)nIz -/
  | poss2pl
  /-- 3PL.POSS: the third-person plural possessive -lArI -/
  | poss3pl
  /-- GEN: the genitive -(n)In -/
  | gen
  /-- DAT: the dative -(y)A -/
  | dat
  /-- LOC: the locative -DA -/
  | loc
  /-- AOR: the aorist -(A/I)r -/
  | aor
  /-- FUT: the future -(y)AcAK -/
  | fut
  /-- COND: the conditional -sA -/
  | cond
  /-- NEG: the negative -mA -/
  | neg
  /-- CAUS: the causative -DIr -/
  | caus
  /-- P.COP: the past copula -(y)DI -/
  | pCop
  /-- EV.COP: the evidential copula -(y)mIş -/
  | evCop
  /-- COND.COP: the conditional copula -(y)sA -/
  | condCop
  /-- 1PL: a first-person plural person marker -/
  | p1pl
  /-- 3PL: a third-person plural person marker -/
  | p3pl
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `suffix`. -/
def suffixes (e : Datum) : List Suffix :=
  (e.features "suffix").filterMap (List.lookup · [("1SG.POSS", .poss1sg), ("2SG.POSS", .poss2sg), ("3SG.POSS", .poss3sg), ("PL", .pl),
    ("PASS", .pass), ("PF", .pf), ("EV/PF", .evPf), ("IMPF", .impf), ("CV", .cv),
    ("1SG", .p1sg), ("2PL", .p2pl), ("1PL.POSS", .poss1pl), ("2PL.POSS", .poss2pl),
    ("3PL.POSS", .poss3pl), ("GEN", .gen), ("DAT", .dat), ("LOC", .loc), ("AOR", .aor),
    ("FUT", .fut), ("COND", .cond), ("NEG", .neg), ("CAUS", .caus), ("P.COP", .pCop),
    ("EV.COP", .evCop), ("COND.COP", .condCop), ("1PL", .p1pl), ("3PL", .p3pl)])

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
  /-- kal: kal- 'remain' -/
  | kal
  /-- dus: düş- 'fall' -/
  | dus
  /-- pul: pul 'stamp' -/
  | pul
  /-- ev: ev 'house, home' -/
  | ev
  /-- araba: araba 'car' -/
  | araba
  /-- ara: ara- 'search' -/
  | ara
  /-- sor: sor- 'ask' -/
  | sor
  /-- atla: atla- 'jump' -/
  | atla
  /-- suna: the name Suna -/
  | suna
  /-- betul: the name Betül -/
  | betul
  /-- emine: the name Emine -/
  | emine
  /-- elbise: elbise 'dress' -/
  | elbise
  /-- tepe: tepe 'summit, top' -/
  | tepe
  /-- yuz: yüz 'face' -/
  | yuz
  /-- oda: oda 'room' -/
  | oda
  /-- masa: masa 'table' -/
  | masa
  /-- okul: okul 'school' -/
  | okul
  /-- hasta: hasta 'ill' -/
  | hasta
  /-- kat: kat- 'add' -/
  | kat
  /-- anla: anla- 'understand' -/
  | anla
  /-- oksa: okşa- 'caress' -/
  | oksa
  /-- bekle: bekle- 'wait' -/
  | bekle
  /-- ozle: özle- 'miss' -/
  | ozle
  /-- eri: eri- 'melt' -/
  | eri
  /-- kuru: kuru- 'dry' -/
  | kuru
  /-- sakla: sakla- 'hide' -/
  | sakla
  /-- soyle: söyle- 'tell' -/
  | soyle
  /-- yap: yap- 'do, make' -/
  | yap
  /-- koy: koy- 'put' -/
  | koy
  /-- ol: öl- 'die' -/
  | ol
  /-- dol: dol- 'fill' -/
  | dol
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("kiz", .kiz), ("el", .el), ("kol", .kol), ("goz", .goz), ("otobus", .otobus), ("uz", .uz), ("gor", .gor), ("bak", .bak), ("gol", .gol), ("hal", .hal), ("kal", .kal), ("dus", .dus), ("pul", .pul), ("ev", .ev), ("araba", .araba), ("ara", .ara), ("sor", .sor), ("atla", .atla), ("suna", .suna), ("betul", .betul), ("emine", .emine), ("elbise", .elbise), ("tepe", .tepe), ("yuz", .yuz), ("oda", .oda), ("masa", .masa), ("okul", .okul), ("hasta", .hasta), ("kat", .kat), ("anla", .anla), ("oksa", .oksa), ("bekle", .bekle), ("ozle", .ozle), ("eri", .eri), ("kuru", .kuru), ("sakla", .sakla), ("soyle", .soyle), ("yap", .yap), ("koy", .koy), ("ol", .ol), ("dol", .dol)])

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
  | kaldi
  | dustu
  | pulum
  | gorur
  | arar
  | soracak
  | atlayacak
  | sunanin
  | betulun
  | eminenin
  | emineye
  | evi
  | elbisesi
  | evim
  | arabam
  | eviniz
  | arabaniz
  | evimiz
  | arabamiz
  | arabasi
  | tepesinde
  | yuzune
  | elbiselerine
  | tepesi
  | odamda
  | masaya
  | okuldayim
  | evdeydik
  | hastaysalar
  | katsaydilar
  | anliyor
  | oksuyor
  | bekliyor
  | ozluyor
  | eriyor
  | kuruyor
  | saklamiyor
  | soylemiyor
  | anlamiyor
  | gormuyor
  | evlerimizdeymisler
  | yaptir
  | koydur
  | oldur
  | doldur
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.kizin, .elin, .kolun, .gozun, .otobusler, .uzuldunuz, .goruyorum, .bakmisken, .golu, .halim,
    .kaldi, .dustu, .pulum, .gorur, .arar, .soracak, .atlayacak, .sunanin, .betulun, .eminenin,
    .emineye, .evi, .elbisesi, .evim, .arabam, .eviniz, .arabaniz, .evimiz, .arabamiz, .arabasi,
    .tepesinde, .yuzune, .elbiselerine, .tepesi, .odamda, .masaya, .okuldayim, .evdeydik,
    .hastaysalar, .katsaydilar, .anliyor, .oksuyor, .bekliyor, .ozluyor, .eriyor, .kuruyor,
    .saklamiyor, .soylemiyor, .anlamiyor, .gormuyor, .evlerimizdeymisler, .yaptir, .koydur,
    .oldur, .doldur]

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
  | .kaldi => _root_.GokselKerslake2005.Examples.kaldi
  | .dustu => _root_.GokselKerslake2005.Examples.dustu
  | .pulum => _root_.GokselKerslake2005.Examples.pulum
  | .gorur => _root_.GokselKerslake2005.Examples.gorur
  | .arar => _root_.GokselKerslake2005.Examples.arar
  | .soracak => _root_.GokselKerslake2005.Examples.soracak
  | .atlayacak => _root_.GokselKerslake2005.Examples.atlayacak
  | .sunanin => _root_.GokselKerslake2005.Examples.sunanin
  | .betulun => _root_.GokselKerslake2005.Examples.betulun
  | .eminenin => _root_.GokselKerslake2005.Examples.eminenin
  | .emineye => _root_.GokselKerslake2005.Examples.emineye
  | .evi => _root_.GokselKerslake2005.Examples.evi
  | .elbisesi => _root_.GokselKerslake2005.Examples.elbisesi
  | .evim => _root_.GokselKerslake2005.Examples.evim
  | .arabam => _root_.GokselKerslake2005.Examples.arabam
  | .eviniz => _root_.GokselKerslake2005.Examples.eviniz
  | .arabaniz => _root_.GokselKerslake2005.Examples.arabaniz
  | .evimiz => _root_.GokselKerslake2005.Examples.evimiz
  | .arabamiz => _root_.GokselKerslake2005.Examples.arabamiz
  | .arabasi => _root_.GokselKerslake2005.Examples.arabasi
  | .tepesinde => _root_.GokselKerslake2005.Examples.tepesinde
  | .yuzune => _root_.GokselKerslake2005.Examples.yuzune
  | .elbiselerine => _root_.GokselKerslake2005.Examples.elbiselerine
  | .tepesi => _root_.GokselKerslake2005.Examples.tepesi
  | .odamda => _root_.GokselKerslake2005.Examples.odamda
  | .masaya => _root_.GokselKerslake2005.Examples.masaya
  | .okuldayim => _root_.GokselKerslake2005.Examples.okuldayim
  | .evdeydik => _root_.GokselKerslake2005.Examples.evdeydik
  | .hastaysalar => _root_.GokselKerslake2005.Examples.hastaysalar
  | .katsaydilar => _root_.GokselKerslake2005.Examples.katsaydilar
  | .anliyor => _root_.GokselKerslake2005.Examples.anliyor
  | .oksuyor => _root_.GokselKerslake2005.Examples.oksuyor
  | .bekliyor => _root_.GokselKerslake2005.Examples.bekliyor
  | .ozluyor => _root_.GokselKerslake2005.Examples.ozluyor
  | .eriyor => _root_.GokselKerslake2005.Examples.eriyor
  | .kuruyor => _root_.GokselKerslake2005.Examples.kuruyor
  | .saklamiyor => _root_.GokselKerslake2005.Examples.saklamiyor
  | .soylemiyor => _root_.GokselKerslake2005.Examples.soylemiyor
  | .anlamiyor => _root_.GokselKerslake2005.Examples.anlamiyor
  | .gormuyor => _root_.GokselKerslake2005.Examples.gormuyor
  | .evlerimizdeymisler => _root_.GokselKerslake2005.Examples.evlerimizdeymisler
  | .yaptir => _root_.GokselKerslake2005.Examples.yaptir
  | .koydur => _root_.GokselKerslake2005.Examples.koydur
  | .oldur => _root_.GokselKerslake2005.Examples.oldur
  | .doldur => _root_.GokselKerslake2005.Examples.doldur

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
  | .kaldi => [.pf]
  | .dustu => [.pf]
  | .pulum => [.poss1sg]
  | .gorur => [.aor]
  | .arar => [.aor]
  | .soracak => [.fut]
  | .atlayacak => [.fut]
  | .sunanin => [.gen]
  | .betulun => [.gen]
  | .eminenin => [.gen]
  | .emineye => [.dat]
  | .evi => [.poss3sg]
  | .elbisesi => [.poss3sg]
  | .evim => [.poss1sg]
  | .arabam => [.poss1sg]
  | .eviniz => [.poss2pl]
  | .arabaniz => [.poss2pl]
  | .evimiz => [.poss1pl]
  | .arabamiz => [.poss1pl]
  | .arabasi => [.poss3sg]
  | .tepesinde => [.poss3sg, .loc]
  | .yuzune => [.poss3sg, .dat]
  | .elbiselerine => [.poss3pl, .dat]
  | .tepesi => [.poss3sg]
  | .odamda => [.poss1sg, .loc]
  | .masaya => [.dat]
  | .okuldayim => [.loc, .p1sg]
  | .evdeydik => [.loc, .pCop, .p1pl]
  | .hastaysalar => [.condCop, .p3pl]
  | .katsaydilar => [.cond, .pCop, .p3pl]
  | .anliyor => [.impf]
  | .oksuyor => [.impf]
  | .bekliyor => [.impf]
  | .ozluyor => [.impf]
  | .eriyor => [.impf]
  | .kuruyor => [.impf]
  | .saklamiyor => [.neg, .impf]
  | .soylemiyor => [.neg, .impf]
  | .anlamiyor => [.neg, .impf]
  | .gormuyor => [.neg, .impf]
  | .evlerimizdeymisler => [.pl, .poss1pl, .loc, .evCop, .p3pl]
  | .yaptir => [.caus]
  | .koydur => [.caus]
  | .oldur => [.caus]
  | .doldur => [.caus]

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
  | .kaldi => [(.stem, .kal)]
  | .dustu => [(.stem, .dus)]
  | .pulum => [(.stem, .pul)]
  | .gorur => [(.stem, .gor)]
  | .arar => [(.stem, .ara)]
  | .soracak => [(.stem, .sor)]
  | .atlayacak => [(.stem, .atla)]
  | .sunanin => [(.stem, .suna)]
  | .betulun => [(.stem, .betul)]
  | .eminenin => [(.stem, .emine)]
  | .emineye => [(.stem, .emine)]
  | .evi => [(.stem, .ev)]
  | .elbisesi => [(.stem, .elbise)]
  | .evim => [(.stem, .ev)]
  | .arabam => [(.stem, .araba)]
  | .eviniz => [(.stem, .ev)]
  | .arabaniz => [(.stem, .araba)]
  | .evimiz => [(.stem, .ev)]
  | .arabamiz => [(.stem, .araba)]
  | .arabasi => [(.stem, .araba)]
  | .tepesinde => [(.stem, .tepe)]
  | .yuzune => [(.stem, .yuz)]
  | .elbiselerine => [(.stem, .elbise)]
  | .tepesi => [(.stem, .tepe)]
  | .odamda => [(.stem, .oda)]
  | .masaya => [(.stem, .masa)]
  | .okuldayim => [(.stem, .okul)]
  | .evdeydik => [(.stem, .ev)]
  | .hastaysalar => [(.stem, .hasta)]
  | .katsaydilar => [(.stem, .kat)]
  | .anliyor => [(.stem, .anla)]
  | .oksuyor => [(.stem, .oksa)]
  | .bekliyor => [(.stem, .bekle)]
  | .ozluyor => [(.stem, .ozle)]
  | .eriyor => [(.stem, .eri)]
  | .kuruyor => [(.stem, .kuru)]
  | .saklamiyor => [(.stem, .sakla)]
  | .soylemiyor => [(.stem, .soyle)]
  | .anlamiyor => [(.stem, .anla)]
  | .gormuyor => [(.stem, .gor)]
  | .evlerimizdeymisler => [(.stem, .ev)]
  | .yaptir => [(.stem, .yap)]
  | .koydur => [(.stem, .koy)]
  | .oldur => [(.stem, .ol)]
  | .doldur => [(.stem, .dol)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.GokselKerslake2005.Examples.label? · = some l)).filterMap _root_.GokselKerslake2005.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end GokselKerslake2005.Examples
