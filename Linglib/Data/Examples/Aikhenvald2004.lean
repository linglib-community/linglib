module

public import Linglib.Data.Examples.Schema

/-!
# `Aikhenvald2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Aikhenvald2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aikhenvald2004.Examples`.
-/

@[expose] public section

namespace Aikhenvald2004.Examples

def ex1_1 : Datum :=
  { id := "aikhenvald2004_ex1_1"
    source := ⟨"aikhenvald-2004", "(1.1)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-ka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-ka", "3sgnf-play-REC.P.VIS")]
    glossedWords := [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], none⟩]⟩, ⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], [⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], none⟩]⟩, ⟨['d', 'i', '-', 'm', 'a', 'n', 'i', 'k', 'a', '-', 'k', 'a'], ['3', 's', 'g', 'n', 'f', '-', 'p', 'l', 'a', 'y', '-', 'R', 'E', 'C', '.', 'P', '.', 'V', 'I', 'S'], [⟨['d', 'i'], ['3', 's', 'g', 'n', 'f'], none⟩, ⟨['m', 'a', 'n', 'i', 'k', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩, ⟨['k', 'a'], ['R', 'E', 'C', '.', 'P', '.', 'V', 'I', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker saw José play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "visual"), ("source", "visual")] }

def ex1_2 : Datum :=
  { id := "aikhenvald2004_ex1_2"
    source := ⟨"aikhenvald-2004", "(1.2)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-mahka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-mahka", "3sgnf-play-REC.P.NONVIS")]
    glossedWords := [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], none⟩]⟩, ⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], [⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], none⟩]⟩, ⟨['d', 'i', '-', 'm', 'a', 'n', 'i', 'k', 'a', '-', 'm', 'a', 'h', 'k', 'a'], ['3', 's', 'g', 'n', 'f', '-', 'p', 'l', 'a', 'y', '-', 'R', 'E', 'C', '.', 'P', '.', 'N', 'O', 'N', 'V', 'I', 'S'], [⟨['d', 'i'], ['3', 's', 'g', 'n', 'f'], none⟩, ⟨['m', 'a', 'n', 'i', 'k', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩, ⟨['m', 'a', 'h', 'k', 'a'], ['R', 'E', 'C', '.', 'P', '.', 'N', 'O', 'N', 'V', 'I', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker heard the noise of a game but could not see it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "nonvisual"), ("source", "nonvisual")] }

def ex1_3 : Datum :=
  { id := "aikhenvald2004_ex1_3"
    source := ⟨"aikhenvald-2004", "(1.3)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-nihka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-nihka", "3sgnf-play-REC.P.INFR")]
    glossedWords := [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], none⟩]⟩, ⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], [⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], none⟩]⟩, ⟨['d', 'i', '-', 'm', 'a', 'n', 'i', 'k', 'a', '-', 'n', 'i', 'h', 'k', 'a'], ['3', 's', 'g', 'n', 'f', '-', 'p', 'l', 'a', 'y', '-', 'R', 'E', 'C', '.', 'P', '.', 'I', 'N', 'F', 'R'], [⟨['d', 'i'], ['3', 's', 'g', 'n', 'f'], none⟩, ⟨['m', 'a', 'n', 'i', 'k', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩, ⟨['n', 'i', 'h', 'k', 'a'], ['R', 'E', 'C', '.', 'P', '.', 'I', 'N', 'F', 'R'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The football and José's boots are gone and crowds return from the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "inferred"), ("source", "inference")] }

def ex1_4 : Datum :=
  { id := "aikhenvald2004_ex1_4"
    source := ⟨"aikhenvald-2004", "(1.4)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-sika"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-sika", "3sgnf-play-REC.P.ASSUM")]
    glossedWords := [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], none⟩]⟩, ⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], [⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], none⟩]⟩, ⟨['d', 'i', '-', 'm', 'a', 'n', 'i', 'k', 'a', '-', 's', 'i', 'k', 'a'], ['3', 's', 'g', 'n', 'f', '-', 'p', 'l', 'a', 'y', '-', 'R', 'E', 'C', '.', 'P', '.', 'A', 'S', 'S', 'U', 'M'], [⟨['d', 'i'], ['3', 's', 'g', 'n', 'f'], none⟩, ⟨['m', 'a', 'n', 'i', 'k', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩, ⟨['s', 'i', 'k', 'a'], ['R', 'E', 'C', '.', 'P', '.', 'A', 'S', 'S', 'U', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "José is out on a Sunday afternoon, when he usually plays."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "assumed"), ("source", "assumption")] }

def ex1_5 : Datum :=
  { id := "aikhenvald2004_ex1_5"
    source := ⟨"aikhenvald-2004", "(1.5)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-pidaka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-pidaka", "3sgnf-play-REC.P.REP")]
    glossedWords := [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], [⟨['J', 'u', 's', 'e'], ['J', 'o', 's', 'é'], none⟩]⟩, ⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], [⟨['i', 'ɾ', 'i', 'd', 'a'], ['f', 'o', 'o', 't', 'b', 'a', 'l', 'l'], none⟩]⟩, ⟨['d', 'i', '-', 'm', 'a', 'n', 'i', 'k', 'a', '-', 'p', 'i', 'd', 'a', 'k', 'a'], ['3', 's', 'g', 'n', 'f', '-', 'p', 'l', 'a', 'y', '-', 'R', 'E', 'C', '.', 'P', '.', 'R', 'E', 'P'], [⟨['d', 'i'], ['3', 's', 'g', 'n', 'f'], none⟩, ⟨['m', 'a', 'n', 'i', 'k', 'a'], ['p', 'l', 'a', 'y'], some '-'⟩, ⟨['p', 'i', 'd', 'a', 'k', 'a'], ['R', 'E', 'C', '.', 'P', '.', 'R', 'E', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Someone told the speaker."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "reported"), ("source", "report")] }

def ex2_16 : Datum :=
  { id := "aikhenvald2004_ex2_16"
    source := ⟨"aikhenvald-2004", "(2.16)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "bakan hasta-ymış"
    glossedTokens := [("bakan", "minister"), ("hasta-ymış", "sick-NONFIRSTH.COP")]
    glossedWords := [⟨['b', 'a', 'k', 'a', 'n'], ['m', 'i', 'n', 'i', 's', 't', 'e', 'r'], [⟨['b', 'a', 'k', 'a', 'n'], ['m', 'i', 'n', 'i', 's', 't', 'e', 'r'], none⟩]⟩, ⟨['h', 'a', 's', 't', 'a', '-', 'y', 'm', 'ı', 'ş'], ['s', 'i', 'c', 'k', '-', 'N', 'O', 'N', 'F', 'I', 'R', 'S', 'T', 'H', '.', 'C', 'O', 'P'], [⟨['h', 'a', 's', 't', 'a'], ['s', 'i', 'c', 'k'], none⟩, ⟨['y', 'm', 'ı', 'ş'], ['N', 'O', 'N', 'F', 'I', 'R', 'S', 'T', 'H', '.', 'C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Said by somebody told about the sickness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "report")] }

def ex2_17 : Datum :=
  { id := "aikhenvald2004_ex2_17"
    source := ⟨"aikhenvald-2004", "(2.17)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "uyu-muş-um"
    glossedTokens := [("uyu-muş-um", "sleep-NONFIRSTH.PAST-1sg")]
    glossedWords := [⟨['u', 'y', 'u', '-', 'm', 'u', 'ş', '-', 'u', 'm'], ['s', 'l', 'e', 'e', 'p', '-', 'N', 'O', 'N', 'F', 'I', 'R', 'S', 'T', 'H', '.', 'P', 'A', 'S', 'T', '-', '1', 's', 'g'], [⟨['u', 'y', 'u'], ['s', 'l', 'e', 'e', 'p'], none⟩, ⟨['m', 'u', 'ş'], ['N', 'O', 'N', 'F', 'I', 'R', 'S', 'T', 'H', '.', 'P', 'A', 'S', 'T'], some '-'⟩, ⟨['u', 'm'], ['1', 's', 'g'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Said by somebody who has just woken up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "inference")] }

def ex2_18 : Datum :=
  { id := "aikhenvald2004_ex2_18"
    source := ⟨"aikhenvald-2004", "(2.18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "iyi çal-Iyor-muş"
    glossedTokens := [("iyi", "good"), ("çal-Iyor-muş", "play-INTRATERM.ASP-NONFIRSTH.COP")]
    glossedWords := [⟨['i', 'y', 'i'], ['g', 'o', 'o', 'd'], [⟨['i', 'y', 'i'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['ç', 'a', 'l', '-', 'I', 'y', 'o', 'r', '-', 'm', 'u', 'ş'], ['p', 'l', 'a', 'y', '-', 'I', 'N', 'T', 'R', 'A', 'T', 'E', 'R', 'M', '.', 'A', 'S', 'P', '-', 'N', 'O', 'N', 'F', 'I', 'R', 'S', 'T', 'H', '.', 'C', 'O', 'P'], [⟨['ç', 'a', 'l'], ['p', 'l', 'a', 'y'], none⟩, ⟨['I', 'y', 'o', 'r'], ['I', 'N', 'T', 'R', 'A', 'T', 'E', 'R', 'M', '.', 'A', 'S', 'P'], some '-'⟩, ⟨['m', 'u', 'ş'], ['N', 'O', 'N', 'F', 'I', 'R', 'S', 'T', 'H', '.', 'C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Said by somebody listening to her play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "nonvisual")] }

def ex2_40 : Datum :=
  { id := "aikhenvald2004_ex2_40"
    source := ⟨"aikhenvald-2004", "(2.40)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Chay-chruu-mi achka wamla-pis walashr-pis alma-ku-lkaa-ña"
    glossedTokens := [("Chay-chruu-mi", "this-LOC-DIR.EV"), ("achka", "many"), ("wamla-pis", "girl-TOO"), ("walashr-pis", "boy-TOO"), ("alma-ku-lkaa-ña", "bathe-REFL-IMPF.PL-NARR.PAST")]
    glossedWords := [⟨['C', 'h', 'a', 'y', '-', 'c', 'h', 'r', 'u', 'u', '-', 'm', 'i'], ['t', 'h', 'i', 's', '-', 'L', 'O', 'C', '-', 'D', 'I', 'R', '.', 'E', 'V'], [⟨['C', 'h', 'a', 'y'], ['t', 'h', 'i', 's'], none⟩, ⟨['c', 'h', 'r', 'u', 'u'], ['L', 'O', 'C'], some '-'⟩, ⟨['m', 'i'], ['D', 'I', 'R', '.', 'E', 'V'], some '-'⟩]⟩, ⟨['a', 'c', 'h', 'k', 'a'], ['m', 'a', 'n', 'y'], [⟨['a', 'c', 'h', 'k', 'a'], ['m', 'a', 'n', 'y'], none⟩]⟩, ⟨['w', 'a', 'm', 'l', 'a', '-', 'p', 'i', 's'], ['g', 'i', 'r', 'l', '-', 'T', 'O', 'O'], [⟨['w', 'a', 'm', 'l', 'a'], ['g', 'i', 'r', 'l'], none⟩, ⟨['p', 'i', 's'], ['T', 'O', 'O'], some '-'⟩]⟩, ⟨['w', 'a', 'l', 'a', 's', 'h', 'r', '-', 'p', 'i', 's'], ['b', 'o', 'y', '-', 'T', 'O', 'O'], [⟨['w', 'a', 'l', 'a', 's', 'h', 'r'], ['b', 'o', 'y'], none⟩, ⟨['p', 'i', 's'], ['T', 'O', 'O'], some '-'⟩]⟩, ⟨['a', 'l', 'm', 'a', '-', 'k', 'u', '-', 'l', 'k', 'a', 'a', '-', 'ñ', 'a'], ['b', 'a', 't', 'h', 'e', '-', 'R', 'E', 'F', 'L', '-', 'I', 'M', 'P', 'F', '.', 'P', 'L', '-', 'N', 'A', 'R', 'R', '.', 'P', 'A', 'S', 'T'], [⟨['a', 'l', 'm', 'a'], ['b', 'a', 't', 'h', 'e'], none⟩, ⟨['k', 'u'], ['R', 'E', 'F', 'L'], some '-'⟩, ⟨['l', 'k', 'a', 'a'], ['I', 'M', 'P', 'F', '.', 'P', 'L'], some '-'⟩, ⟨['ñ', 'a'], ['N', 'A', 'R', 'R', '.', 'P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker saw them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "direct"), ("source", "visual")] }

def ex2_41 : Datum :=
  { id := "aikhenvald2004_ex2_41"
    source := ⟨"aikhenvald-2004", "(2.41)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Daañu pawa-shra-si ka-ya-n-chr-ari"
    glossedTokens := [("Daañu", "field"), ("pawa-shra-si", "finish-PART-EVEN"), ("ka-ya-n-chr-ari", "be-IMPF-3-INFR-EMPH")]
    glossedWords := [⟨['D', 'a', 'a', 'ñ', 'u'], ['f', 'i', 'e', 'l', 'd'], [⟨['D', 'a', 'a', 'ñ', 'u'], ['f', 'i', 'e', 'l', 'd'], none⟩]⟩, ⟨['p', 'a', 'w', 'a', '-', 's', 'h', 'r', 'a', '-', 's', 'i'], ['f', 'i', 'n', 'i', 's', 'h', '-', 'P', 'A', 'R', 'T', '-', 'E', 'V', 'E', 'N'], [⟨['p', 'a', 'w', 'a'], ['f', 'i', 'n', 'i', 's', 'h'], none⟩, ⟨['s', 'h', 'r', 'a'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['s', 'i'], ['E', 'V', 'E', 'N'], some '-'⟩]⟩, ⟨['k', 'a', '-', 'y', 'a', '-', 'n', '-', 'c', 'h', 'r', '-', 'a', 'r', 'i'], ['b', 'e', '-', 'I', 'M', 'P', 'F', '-', '3', '-', 'I', 'N', 'F', 'R', '-', 'E', 'M', 'P', 'H'], [⟨['k', 'a'], ['b', 'e'], none⟩, ⟨['y', 'a'], ['I', 'M', 'P', 'F'], some '-'⟩, ⟨['n'], ['3'], some '-'⟩, ⟨['c', 'h', 'r'], ['I', 'N', 'F', 'R'], some '-'⟩, ⟨['a', 'r', 'i'], ['E', 'M', 'P', 'H'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker infers it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "inferred"), ("source", "inference")] }

def ex2_42 : Datum :=
  { id := "aikhenvald2004_ex2_42"
    source := ⟨"aikhenvald-2004", "(2.42)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Ancha-p-shi wa'a-chi-nki wamla-a-ta"
    glossedTokens := [("Ancha-p-shi", "too.much-GEN-REP"), ("wa'a-chi-nki", "cry-CAUS-2"), ("wamla-a-ta", "girl-1p-ACC")]
    glossedWords := [⟨['A', 'n', 'c', 'h', 'a', '-', 'p', '-', 's', 'h', 'i'], ['t', 'o', 'o', '.', 'm', 'u', 'c', 'h', '-', 'G', 'E', 'N', '-', 'R', 'E', 'P'], [⟨['A', 'n', 'c', 'h', 'a'], ['t', 'o', 'o', '.', 'm', 'u', 'c', 'h'], none⟩, ⟨['p'], ['G', 'E', 'N'], some '-'⟩, ⟨['s', 'h', 'i'], ['R', 'E', 'P'], some '-'⟩]⟩, ⟨['w', 'a', '\'', 'a', '-', 'c', 'h', 'i', '-', 'n', 'k', 'i'], ['c', 'r', 'y', '-', 'C', 'A', 'U', 'S', '-', '2'], [⟨['w', 'a', '\'', 'a'], ['c', 'r', 'y'], none⟩, ⟨['c', 'h', 'i'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['n', 'k', 'i'], ['2'], some '-'⟩]⟩, ⟨['w', 'a', 'm', 'l', 'a', '-', 'a', '-', 't', 'a'], ['g', 'i', 'r', 'l', '-', '1', 'p', '-', 'A', 'C', 'C'], [⟨['w', 'a', 'm', 'l', 'a'], ['g', 'i', 'r', 'l'], none⟩, ⟨['a'], ['1', 'p'], some '-'⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker was told."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "reported"), ("source", "report")] }

def ex4_7 : Datum :=
  { id := "aikhenvald2004_ex4_7"
    source := ⟨"aikhenvald-2004", "(4.7)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "varsken-s ianvr-is rva-s p'irvel-ad (ø-)u-c'am-eb-i-a šušanik'-i"
    glossedTokens := [("varsken-s", "Varsken-DAT"), ("ianvr-is", "January-GEN"), ("rva-s", "8-DAT"), ("p'irvel-ad", "first-ADV"), ("(ø-)u-c'am-eb-i-a", "(he-)OV-torture-TS-PERF-her"), ("šušanik'-i", "Shushanik'-NOM")]
    glossedWords := [⟨['v', 'a', 'r', 's', 'k', 'e', 'n', '-', 's'], ['V', 'a', 'r', 's', 'k', 'e', 'n', '-', 'D', 'A', 'T'], [⟨['v', 'a', 'r', 's', 'k', 'e', 'n'], ['V', 'a', 'r', 's', 'k', 'e', 'n'], none⟩, ⟨['s'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['i', 'a', 'n', 'v', 'r', '-', 'i', 's'], ['J', 'a', 'n', 'u', 'a', 'r', 'y', '-', 'G', 'E', 'N'], [⟨['i', 'a', 'n', 'v', 'r'], ['J', 'a', 'n', 'u', 'a', 'r', 'y'], none⟩, ⟨['i', 's'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['r', 'v', 'a', '-', 's'], ['8', '-', 'D', 'A', 'T'], [⟨['r', 'v', 'a'], ['8'], none⟩, ⟨['s'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['p', '\'', 'i', 'r', 'v', 'e', 'l', '-', 'a', 'd'], ['f', 'i', 'r', 's', 't', '-', 'A', 'D', 'V'], [⟨['p', '\'', 'i', 'r', 'v', 'e', 'l'], ['f', 'i', 'r', 's', 't'], none⟩, ⟨['a', 'd'], ['A', 'D', 'V'], some '-'⟩]⟩, ⟨['(', 'ø', '-', ')', 'u', '-', 'c', '\'', 'a', 'm', '-', 'e', 'b', '-', 'i', '-', 'a'], ['(', 'h', 'e', '-', ')', 'O', 'V', '-', 't', 'o', 'r', 't', 'u', 'r', 'e', '-', 'T', 'S', '-', 'P', 'E', 'R', 'F', '-', 'h', 'e', 'r'], [⟨['ø'], ['(', 'h', 'e'], none⟩, ⟨['u'], [')', 'O', 'V'], some '-'⟩, ⟨['c', '\'', 'a', 'm'], ['t', 'o', 'r', 't', 'u', 'r', 'e'], some '-'⟩, ⟨['e', 'b'], ['T', 'S'], some '-'⟩, ⟨['i'], ['P', 'E', 'R', 'F'], some '-'⟩, ⟨['a'], ['h', 'e', 'r'], some '-'⟩]⟩, ⟨['š', 'u', 'š', 'a', 'n', 'i', 'k', '\'', '-', 'i'], ['S', 'h', 'u', 's', 'h', 'a', 'n', 'i', 'k', '\'', '-', 'N', 'O', 'M'], [⟨['š', 'u', 'š', 'a', 'n', 'i', 'k', '\''], ['S', 'h', 'u', 's', 'h', 'a', 'n', 'i', 'k', '\''], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A past action the speaker did not witness but assumes from a present result or a report."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "perfect"), ("source", "nonfirsthand")] }

def ex4_55 : Datum :=
  { id := "aikhenvald2004_ex4_55"
    source := ⟨"aikhenvald-2004", "(4.55)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Dumat, zmejat sljazăl v našata niva"
    glossedTokens := [("Dumat", "think.PRES.3PL"), ("zmejat", "dragon"), ("sljazăl", "come.down.REPORTIVE.SG"), ("v", "into"), ("našata", "our"), ("niva", "field")]
    glossedWords := [⟨['D', 'u', 'm', 'a', 't'], ['t', 'h', 'i', 'n', 'k', '.', 'P', 'R', 'E', 'S', '.', '3', 'P', 'L'], [⟨['D', 'u', 'm', 'a', 't'], ['t', 'h', 'i', 'n', 'k', '.', 'P', 'R', 'E', 'S', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['z', 'm', 'e', 'j', 'a', 't'], ['d', 'r', 'a', 'g', 'o', 'n'], [⟨['z', 'm', 'e', 'j', 'a', 't'], ['d', 'r', 'a', 'g', 'o', 'n'], none⟩]⟩, ⟨['s', 'l', 'j', 'a', 'z', 'ă', 'l'], ['c', 'o', 'm', 'e', '.', 'd', 'o', 'w', 'n', '.', 'R', 'E', 'P', 'O', 'R', 'T', 'I', 'V', 'E', '.', 'S', 'G'], [⟨['s', 'l', 'j', 'a', 'z', 'ă', 'l'], ['c', 'o', 'm', 'e', '.', 'd', 'o', 'w', 'n', '.', 'R', 'E', 'P', 'O', 'R', 'T', 'I', 'V', 'E', '.', 'S', 'G'], none⟩]⟩, ⟨['v'], ['i', 'n', 't', 'o'], [⟨['v'], ['i', 'n', 't', 'o'], none⟩]⟩, ⟨['n', 'a', 'š', 'a', 't', 'a'], ['o', 'u', 'r'], [⟨['n', 'a', 'š', 'a', 't', 'a'], ['o', 'u', 'r'], none⟩]⟩, ⟨['n', 'i', 'v', 'a'], ['f', 'i', 'e', 'l', 'd'], [⟨['n', 'i', 'v', 'a'], ['f', 'i', 'e', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Reported information the speaker distances themself from."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "report"), ("extension", "epistemic")] }

def all : List Datum := [ex1_1, ex1_2, ex1_3, ex1_4, ex1_5, ex2_16, ex2_17, ex2_18, ex2_40, ex2_41, ex2_42, ex4_7, ex4_55]

end Aikhenvald2004.Examples
