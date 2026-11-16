module

public import Linglib.Data.Examples.Schema

/-!
# `Matthewson2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Matthewson2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Matthewson2006.Examples`.
-/

@[expose] public section

namespace Matthewson2006.Examples

def ex_5a : Datum :=
  { id := "matthewson2006_5a"
    source := ⟨"matthewson-2006", "(5a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "lill1248"
    primaryText := "táyt-kan lhkúnsa"
    glossedTokens := [("táyt-kan", "hungry-1SG.SUBJ"), ("lhkúnsa", "now")]
    glossedWords := [⟨['t', 'á', 'y', 't', '-', 'k', 'a', 'n'], ['h', 'u', 'n', 'g', 'r', 'y', '-', '1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], [⟨['t', 'á', 'y', 't'], ['h', 'u', 'n', 'g', 'r', 'y'], none⟩, ⟨['k', 'a', 'n'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩, ⟨['l', 'h', 'k', 'ú', 'n', 's', 'a'], ['n', 'o', 'w'], [⟨['l', 'h', 'k', 'ú', 'n', 's', 'a'], ['n', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "present")] }

def ex_5b : Datum :=
  { id := "matthewson2006_5b"
    source := ⟨"matthewson-2006", "(5b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "lill1248"
    primaryText := "k'ác-an'-lhkan i-nátcw-as"
    glossedTokens := [("k'ác-an'-lhkan", "dry-DIR-1SG.SUBJ"), ("i-nátcw-as", "when.PAST-one.day.away-3CONJ")]
    glossedWords := [⟨['k', '\'', 'á', 'c', '-', 'a', 'n', '\'', '-', 'l', 'h', 'k', 'a', 'n'], ['d', 'r', 'y', '-', 'D', 'I', 'R', '-', '1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], [⟨['k', '\'', 'á', 'c'], ['d', 'r', 'y'], none⟩, ⟨['a', 'n', '\''], ['D', 'I', 'R'], some '-'⟩, ⟨['l', 'h', 'k', 'a', 'n'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩, ⟨['i', '-', 'n', 'á', 't', 'c', 'w', '-', 'a', 's'], ['w', 'h', 'e', 'n', '.', 'P', 'A', 'S', 'T', '-', 'o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y', '-', '3', 'C', 'O', 'N', 'J'], [⟨['i'], ['w', 'h', 'e', 'n', '.', 'P', 'A', 'S', 'T'], none⟩, ⟨['n', 'á', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], some '-'⟩, ⟨['a', 's'], ['3', 'C', 'O', 'N', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "past")] }

def ex_5c : Datum :=
  { id := "matthewson2006_5c"
    source := ⟨"matthewson-2006", "(5c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "lill1248"
    primaryText := "sáy'sez'-lhkan i-tsilkstásq'et-as"
    glossedTokens := [("sáy'sez'-lhkan", "play-DIR-1SG.SUBJ"), ("i-tsilkstásq'et-as", "when.PAST-Friday-3CONJ")]
    glossedWords := [⟨['s', 'á', 'y', '\'', 's', 'e', 'z', '\'', '-', 'l', 'h', 'k', 'a', 'n'], ['p', 'l', 'a', 'y', '-', 'D', 'I', 'R', '-', '1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], []⟩, ⟨['i', '-', 't', 's', 'i', 'l', 'k', 's', 't', 'á', 's', 'q', '\'', 'e', 't', '-', 'a', 's'], ['w', 'h', 'e', 'n', '.', 'P', 'A', 'S', 'T', '-', 'F', 'r', 'i', 'd', 'a', 'y', '-', '3', 'C', 'O', 'N', 'J'], [⟨['i'], ['w', 'h', 'e', 'n', '.', 'P', 'A', 'S', 'T'], none⟩, ⟨['t', 's', 'i', 'l', 'k', 's', 't', 'á', 's', 'q', '\'', 'e', 't'], ['F', 'r', 'i', 'd', 'a', 'y'], some '-'⟩, ⟨['a', 's'], ['3', 'C', 'O', 'N', 'J'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "past")] }

def ex_6a : Datum :=
  { id := "matthewson2006_6a"
    source := ⟨"matthewson-2006", "(6a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "lill1248"
    primaryText := "táyt-kan natcw"
    glossedTokens := [("táyt-kan", "hungry-1SG.SUBJ"), ("natcw", "one.day.away")]
    glossedWords := [⟨['t', 'á', 'y', 't', '-', 'k', 'a', 'n'], ['h', 'u', 'n', 'g', 'r', 'y', '-', '1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], [⟨['t', 'á', 'y', 't'], ['h', 'u', 'n', 'g', 'r', 'y'], none⟩, ⟨['k', 'a', 'n'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩, ⟨['n', 'a', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], [⟨['n', 'a', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "future")] }

def ex_6b : Datum :=
  { id := "matthewson2006_6b"
    source := ⟨"matthewson-2006", "(6b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "lill1248"
    primaryText := "k'ác-an'-lhkan natcw"
    glossedTokens := [("k'ác-an'-lhkan", "dry-DIR-1SG.SUBJ"), ("natcw", "one.day.away")]
    glossedWords := [⟨['k', '\'', 'á', 'c', '-', 'a', 'n', '\'', '-', 'l', 'h', 'k', 'a', 'n'], ['d', 'r', 'y', '-', 'D', 'I', 'R', '-', '1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], [⟨['k', '\'', 'á', 'c'], ['d', 'r', 'y'], none⟩, ⟨['a', 'n', '\''], ['D', 'I', 'R'], some '-'⟩, ⟨['l', 'h', 'k', 'a', 'n'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩, ⟨['n', 'a', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], [⟨['n', 'a', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "future")] }

def ex_6c : Datum :=
  { id := "matthewson2006_6c"
    source := ⟨"matthewson-2006", "(6c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "lill1248"
    primaryText := "sáy'sez'-lhkan natcw"
    glossedTokens := [("sáy'sez'-lhkan", "play-1SG.SUBJ"), ("natcw", "one.day.away")]
    glossedWords := [⟨['s', 'á', 'y', '\'', 's', 'e', 'z', '\'', '-', 'l', 'h', 'k', 'a', 'n'], ['p', 'l', 'a', 'y', '-', '1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], [⟨['s', 'á', 'y', '\'', 's', 'e', 'z', '\''], ['p', 'l', 'a', 'y'], none⟩, ⟨['l', 'h', 'k', 'a', 'n'], ['1', 'S', 'G', '.', 'S', 'U', 'B', 'J'], some '-'⟩]⟩, ⟨['n', 'a', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], [⟨['n', 'a', 't', 'c', 'w'], ['o', 'n', 'e', '.', 'd', 'a', 'y', '.', 'a', 'w', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "future")] }

def all : List Datum := [ex_5a, ex_5b, ex_5c, ex_6a, ex_6b, ex_6c]

end Matthewson2006.Examples
