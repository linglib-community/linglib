module

public import Linglib.Data.Examples.Schema

/-!
# `Stankova2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Stankova2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Stankova2026.Examples`.
-/

@[expose] public section

namespace Stankova2026.Examples

def ex6a : Datum :=
  { id := "stankova2026_ex6a"
    source := ⟨"stankova-2026", "ex. 6a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr si nekoupil žádný časopis?"
    glossedTokens := [("Petr", "Petr"), ("si", "REFL"), ("nekoupil", "NEG.bought"), ("žádný", "DET.NCI"), ("časopis", "magazine")]
    glossedWords := [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], [⟨['n', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'ý'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'ý'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['č', 'a', 's', 'o', 'p', 'i', 's'], ['m', 'a', 'g', 'a', 'z', 'i', 'n', 'e'], [⟨['č', 'a', 's', 'o', 'p', 'i', 's'], ['m', 'a', 'g', 'a', 'z', 'i', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "inner"), ("diagnostic", "nciLicensed")] }

def ex6b : Datum :=
  { id := "stankova2026_ex6b"
    source := ⟨"stankova-2026", "ex. 6b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nekoupil si Petr žádný časopis?"
    glossedTokens := [("Nekoupil", "NEG.bought"), ("si", "REFL"), ("Petr", "Petr"), ("žádný", "DET.NCI"), ("časopis", "magazine")]
    glossedWords := [⟨['N', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], [⟨['N', 'e', 'k', 'o', 'u', 'p', 'i', 'l'], ['N', 'E', 'G', '.', 'b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'ý'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'ý'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['č', 'a', 's', 'o', 'p', 'i', 's'], ['m', 'a', 'g', 'a', 'z', 'i', 'n', 'e'], [⟨['č', 'a', 's', 'o', 'p', 'i', 's'], ['m', 'a', 'g', 'a', 'z', 'i', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "nciLicensed")] }

def ex7a : Datum :=
  { id := "stankova2026_ex7a"
    source := ⟨"stankova-2026", "ex. 7a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Eva si neobjednala nějaký burger?"
    glossedTokens := [("Eva", "Eva"), ("si", "REFL"), ("neobjednala", "NEG.ordered"), ("nějaký", "DET.PPI"), ("burger", "burger")]
    glossedWords := [⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['n', 'e', 'o', 'b', 'j', 'e', 'd', 'n', 'a', 'l', 'a'], ['N', 'E', 'G', '.', 'o', 'r', 'd', 'e', 'r', 'e', 'd'], [⟨['n', 'e', 'o', 'b', 'j', 'e', 'd', 'n', 'a', 'l', 'a'], ['N', 'E', 'G', '.', 'o', 'r', 'd', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'ý'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'ý'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['b', 'u', 'r', 'g', 'e', 'r'], ['b', 'u', 'r', 'g', 'e', 'r'], [⟨['b', 'u', 'r', 'g', 'e', 'r'], ['b', 'u', 'r', 'g', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Eva and her colleagues from the office ordered take-out food for lunch. The delivery guy brings only pizzas. One of the colleagues asks."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "medial"), ("diagnostic", "ppiOutscoping")] }

def ex7b : Datum :=
  { id := "stankova2026_ex7b"
    source := ⟨"stankova-2026", "ex. 7b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neobjednala si Eva nějaký burger?"
    glossedTokens := [("Neobjednala", "NEG.ordered"), ("si", "REFL"), ("Eva", "Eva"), ("nějaký", "DET.PPI"), ("burger", "burger")]
    glossedWords := [⟨['N', 'e', 'o', 'b', 'j', 'e', 'd', 'n', 'a', 'l', 'a'], ['N', 'E', 'G', '.', 'o', 'r', 'd', 'e', 'r', 'e', 'd'], [⟨['N', 'e', 'o', 'b', 'j', 'e', 'd', 'n', 'a', 'l', 'a'], ['N', 'E', 'G', '.', 'o', 'r', 'd', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'ý'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'ý'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['b', 'u', 'r', 'g', 'e', 'r'], ['b', 'u', 'r', 'g', 'e', 'r'], [⟨['b', 'u', 'r', 'g', 'e', 'r'], ['b', 'u', 'r', 'g', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Eva and her colleagues from the office ordered take-out food for lunch. The delivery guy brings only pizzas. One of the colleagues asks."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "ppiOutscoping")] }

def ex11 : Datum :=
  { id := "stankova2026_ex11"
    source := ⟨"stankova-2026", "ex. 11"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nepůjčila si tam Eva náhodou nějakou encyklopedii?"
    glossedTokens := [("Nepůjčila", "NEG.borrowed"), ("si", "REFL"), ("tam", "there"), ("Eva", "Eva"), ("náhodou", "NÁHODOU"), ("nějakou", "DET.PPI"), ("encyklopedii", "encyclopedia")]
    glossedWords := [⟨['N', 'e', 'p', 'ů', 'j', 'č', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'b', 'o', 'r', 'r', 'o', 'w', 'e', 'd'], [⟨['N', 'e', 'p', 'ů', 'j', 'č', 'i', 'l', 'a'], ['N', 'E', 'G', '.', 'b', 'o', 'r', 'r', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['s', 'i'], ['R', 'E', 'F', 'L'], [⟨['s', 'i'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], [⟨['t', 'a', 'm'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], [⟨['n', 'á', 'h', 'o', 'd', 'o', 'u'], ['N', 'Á', 'H', 'O', 'D', 'O', 'U'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'o', 'u'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['e', 'n', 'c', 'y', 'k', 'l', 'o', 'p', 'e', 'd', 'i', 'i'], ['e', 'n', 'c', 'y', 'c', 'l', 'o', 'p', 'e', 'd', 'i', 'a'], [⟨['e', 'n', 'c', 'y', 'k', 'l', 'o', 'p', 'e', 'd', 'i', 'i'], ['e', 'n', 'c', 'y', 'c', 'l', 'o', 'p', 'e', 'd', 'i', 'a'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Eva is doing research for a school presentation. Yesterday she went to the school library. The speaker knows all this from before and asks."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "nahodou")] }

def ex15a : Datum :=
  { id := "stankova2026_ex15a"
    source := ⟨"stankova-2026", "ex. 15a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Eva fakt neviděla žádný Tarantinův film?"
    glossedTokens := [("Eva", "Eva"), ("fakt", "FAKT"), ("neviděla", "NEG.saw"), ("žádný", "DET.NCI"), ("Tarantinův", "Tarantino's"), ("film", "film")]
    glossedWords := [⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['f', 'a', 'k', 't'], ['F', 'A', 'K', 'T'], [⟨['f', 'a', 'k', 't'], ['F', 'A', 'K', 'T'], none⟩]⟩, ⟨['n', 'e', 'v', 'i', 'd', 'ě', 'l', 'a'], ['N', 'E', 'G', '.', 's', 'a', 'w'], [⟨['n', 'e', 'v', 'i', 'd', 'ě', 'l', 'a'], ['N', 'E', 'G', '.', 's', 'a', 'w'], none⟩]⟩, ⟨['ž', 'á', 'd', 'n', 'ý'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], [⟨['ž', 'á', 'd', 'n', 'ý'], ['D', 'E', 'T', '.', 'N', 'C', 'I'], none⟩]⟩, ⟨['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'ů', 'v'], ['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'o', '\'', 's'], [⟨['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'ů', 'v'], ['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'o', '\'', 's'], none⟩]⟩, ⟨['f', 'i', 'l', 'm'], ['f', 'i', 'l', 'm'], [⟨['f', 'i', 'l', 'm'], ['f', 'i', 'l', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "inner"), ("diagnostic", "fakt")] }

def ex15d : Datum :=
  { id := "stankova2026_ex15d"
    source := ⟨"stankova-2026", "ex. 15d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neviděla Eva fakt nějaký Tarantinův film?"
    glossedTokens := [("Neviděla", "NEG.saw"), ("Eva", "Eva"), ("fakt", "FAKT"), ("nějaký", "DET.PPI"), ("Tarantinův", "Tarantino's"), ("film", "film")]
    glossedWords := [⟨['N', 'e', 'v', 'i', 'd', 'ě', 'l', 'a'], ['N', 'E', 'G', '.', 's', 'a', 'w'], [⟨['N', 'e', 'v', 'i', 'd', 'ě', 'l', 'a'], ['N', 'E', 'G', '.', 's', 'a', 'w'], none⟩]⟩, ⟨['E', 'v', 'a'], ['E', 'v', 'a'], [⟨['E', 'v', 'a'], ['E', 'v', 'a'], none⟩]⟩, ⟨['f', 'a', 'k', 't'], ['F', 'A', 'K', 'T'], [⟨['f', 'a', 'k', 't'], ['F', 'A', 'K', 'T'], none⟩]⟩, ⟨['n', 'ě', 'j', 'a', 'k', 'ý'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], [⟨['n', 'ě', 'j', 'a', 'k', 'ý'], ['D', 'E', 'T', '.', 'P', 'P', 'I'], none⟩]⟩, ⟨['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'ů', 'v'], ['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'o', '\'', 's'], [⟨['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'ů', 'v'], ['T', 'a', 'r', 'a', 'n', 't', 'i', 'n', 'o', '\'', 's'], none⟩]⟩, ⟨['f', 'i', 'l', 'm'], ['f', 'i', 'l', 'm'], [⟨['f', 'i', 'l', 'm'], ['f', 'i', 'l', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "fakt")] }

def all : List Datum := [ex6a, ex6b, ex7a, ex7b, ex11, ex15a, ex15d]

end Stankova2026.Examples
