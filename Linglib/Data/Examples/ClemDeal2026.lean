module

public import Linglib.Data.Examples.Schema

/-!
# `ClemDeal2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ClemDeal2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ClemDeal2026.Examples`.
-/

@[expose] public section

namespace ClemDeal2026.Examples

def ex_4a : Datum :=
  { id := "clemdeal2026_4a"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka yunka-w."
    glossedTokens := [("Ka", "1"), ("yunka-w", "swim-1")]
    glossedWords := [⟨['K', 'a'], ['1'], [⟨['K', 'a'], ['1'], none⟩]⟩, ⟨['y', 'u', 'n', 'k', 'a', '-', 'w'], ['s', 'w', 'i', 'm', '-', '1'], [⟨['y', 'u', 'n', 'k', 'a'], ['s', 'w', 'i', 'm'], none⟩, ⟨['w'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("objectSyntax", "absent")] }

def ex_4a_ri : Datum :=
  { id := "clemdeal2026_4a_ri"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka-ri yunka-w."
    glossedTokens := [("Ka-ri", "1-ERG"), ("yunka-w", "swim-1")]
    glossedWords := [⟨['K', 'a', '-', 'r', 'i'], ['1', '-', 'E', 'R', 'G'], [⟨['K', 'a'], ['1'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['y', 'u', 'n', 'k', 'a', '-', 'w'], ['s', 'w', 'i', 'm', '-', '1'], [⟨['y', 'u', 'n', 'k', 'a'], ['s', 'w', 'i', 'm'], none⟩, ⟨['w'], ['1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("objectSyntax", "absent"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_4b : Datum :=
  { id := "clemdeal2026_4b"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Wi'nawe chiwe-r-in tanan-ke."
    glossedTokens := [("Wi'nawe", "my.son"), ("chiwe-r-in", "get.lost-IND-3"), ("tanan-ke", "forest-LOC")]
    glossedWords := [⟨['W', 'i', '\'', 'n', 'a', 'w', 'e'], ['m', 'y', '.', 's', 'o', 'n'], [⟨['W', 'i', '\'', 'n', 'a', 'w', 'e'], ['m', 'y', '.', 's', 'o', 'n'], none⟩]⟩, ⟨['c', 'h', 'i', 'w', 'e', '-', 'r', '-', 'i', 'n'], ['g', 'e', 't', '.', 'l', 'o', 's', 't', '-', 'I', 'N', 'D', '-', '3'], [⟨['c', 'h', 'i', 'w', 'e'], ['g', 'e', 't', '.', 'l', 'o', 's', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩, ⟨['t', 'a', 'n', 'a', 'n', '-', 'k', 'e'], ['f', 'o', 'r', 'e', 's', 't', '-', 'L', 'O', 'C'], [⟨['t', 'a', 'n', 'a', 'n'], ['f', 'o', 'r', 'e', 's', 't'], none⟩, ⟨['k', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("objectSyntax", "absent")] }

def ex_4b_ri : Datum :=
  { id := "clemdeal2026_4b_ri"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Wi'nawe-ri chiwe-r-in tanan-ke."
    glossedTokens := [("Wi'nawe-ri", "my.son-ERG"), ("chiwe-r-in", "get.lost-IND-3"), ("tanan-ke", "forest-LOC")]
    glossedWords := [⟨['W', 'i', '\'', 'n', 'a', 'w', 'e', '-', 'r', 'i'], ['m', 'y', '.', 's', 'o', 'n', '-', 'E', 'R', 'G'], [⟨['W', 'i', '\'', 'n', 'a', 'w', 'e'], ['m', 'y', '.', 's', 'o', 'n'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['c', 'h', 'i', 'w', 'e', '-', 'r', '-', 'i', 'n'], ['g', 'e', 't', '.', 'l', 'o', 's', 't', '-', 'I', 'N', 'D', '-', '3'], [⟨['c', 'h', 'i', 'w', 'e'], ['g', 'e', 't', '.', 'l', 'o', 's', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩, ⟨['t', 'a', 'n', 'a', 'n', '-', 'k', 'e'], ['f', 'o', 'r', 'e', 's', 't', '-', 'L', 'O', 'C'], [⟨['t', 'a', 'n', 'a', 'n'], ['f', 'o', 'r', 'e', 's', 't'], none⟩, ⟨['k', 'e'], ['L', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("objectSyntax", "absent"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_6a : Datum :=
  { id := "clemdeal2026_6a"
    source := ⟨"bourdeau-2015", "p. 24"⟩
    reportedIn := some ⟨"clem-deal-2026", "(6a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "I'wara ka-ri-nke pera-ra-w-nke."
    glossedTokens := [("I'wara", "yesterday"), ("ka-ri-nke", "1-ERG-2.O"), ("pera-ra-w-nke", "call-IND-1-2.O")]
    glossedWords := [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['k', 'a', '-', 'r', 'i', '-', 'n', 'k', 'e'], ['1', '-', 'E', 'R', 'G', '-', '2', '.', 'O'], [⟨['k', 'a'], ['1'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩, ⟨['n', 'k', 'e'], ['2', '.', 'O'], some '-'⟩]⟩, ⟨['p', 'e', 'r', 'a', '-', 'r', 'a', '-', 'w', '-', 'n', 'k', 'e'], ['c', 'a', 'l', 'l', '-', 'I', 'N', 'D', '-', '1', '-', '2', '.', 'O'], [⟨['p', 'e', 'r', 'a'], ['c', 'a', 'l', 'l'], none⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['w'], ['1'], some '-'⟩, ⟨['n', 'k', 'e'], ['2', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("I'wara ka-ri-nke pera-ra-nke.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("object", "2"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject"), ("oagrOnS", "-(n)ken")] }

def ex_6b : Datum :=
  { id := "clemdeal2026_6b"
    source := ⟨"bourdeau-2015", "p. 24"⟩
    reportedIn := some ⟨"clem-deal-2026", "(6b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya-ri-nkema au-ra-i-nkema kampita."
    glossedTokens := [("Kiya-ri-nkema", "1PL.EXCL-ERG-2PL.O"), ("au-ra-i-nkema", "hit-IND-1PL.EXCL-2PL.O"), ("kampita", "2PL")]
    glossedWords := [⟨['K', 'i', 'y', 'a', '-', 'r', 'i', '-', 'n', 'k', 'e', 'm', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '-', 'E', 'R', 'G', '-', '2', 'P', 'L', '.', 'O'], [⟨['K', 'i', 'y', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩, ⟨['n', 'k', 'e', 'm', 'a'], ['2', 'P', 'L', '.', 'O'], some '-'⟩]⟩, ⟨['a', 'u', '-', 'r', 'a', '-', 'i', '-', 'n', 'k', 'e', 'm', 'a'], ['h', 'i', 't', '-', 'I', 'N', 'D', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '-', '2', 'P', 'L', '.', 'O'], [⟨['a', 'u'], ['h', 'i', 't'], none⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], some '-'⟩, ⟨['n', 'k', 'e', 'm', 'a'], ['2', 'P', 'L', '.', 'O'], some '-'⟩]⟩, ⟨['k', 'a', 'm', 'p', 'i', 't', 'a'], ['2', 'P', 'L'], [⟨['k', 'a', 'm', 'p', 'i', 't', 'a'], ['2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "2"), ("objectNumber", "aug"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject"), ("oagrOnS", "-((n)ke)ma'")] }

def ex_6b_nke : Datum :=
  { id := "clemdeal2026_6b_nke"
    source := ⟨"bourdeau-2015", "p. 24"⟩
    reportedIn := some ⟨"clem-deal-2026", "(6b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya-ri-nke au-ra-i-nkema kampita."
    glossedTokens := [("Kiya-ri-nke", "1PL.EXCL-ERG-2PL.O"), ("au-ra-i-nkema", "hit-IND-1PL.EXCL-2PL.O"), ("kampita", "2PL")]
    glossedWords := [⟨['K', 'i', 'y', 'a', '-', 'r', 'i', '-', 'n', 'k', 'e'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '-', 'E', 'R', 'G', '-', '2', 'P', 'L', '.', 'O'], [⟨['K', 'i', 'y', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩, ⟨['n', 'k', 'e'], ['2', 'P', 'L', '.', 'O'], some '-'⟩]⟩, ⟨['a', 'u', '-', 'r', 'a', '-', 'i', '-', 'n', 'k', 'e', 'm', 'a'], ['h', 'i', 't', '-', 'I', 'N', 'D', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '-', '2', 'P', 'L', '.', 'O'], [⟨['a', 'u'], ['h', 'i', 't'], none⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], some '-'⟩, ⟨['n', 'k', 'e', 'm', 'a'], ['2', 'P', 'L', '.', 'O'], some '-'⟩]⟩, ⟨['k', 'a', 'm', 'p', 'i', 't', 'a'], ['2', 'P', 'L'], [⟨['k', 'a', 'm', 'p', 'i', 't', 'a'], ['2', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "2"), ("objectNumber", "aug"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject"), ("oagrOnS", "-(n)ken")] }

def ex_7a : Datum :=
  { id := "clemdeal2026_7a"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "I'wara kema nu'wi-r-an-ku."
    glossedTokens := [("I'wara", "yesterday"), ("kema", "2"), ("nu'wi-r-an-ku", "tell.off-IND-2-1.O")]
    glossedWords := [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['k', 'e', 'm', 'a'], ['2'], [⟨['k', 'e', 'm', 'a'], ['2'], none⟩]⟩, ⟨['n', 'u', '\'', 'w', 'i', '-', 'r', '-', 'a', 'n', '-', 'k', 'u'], ['t', 'e', 'l', 'l', '.', 'o', 'f', 'f', '-', 'I', 'N', 'D', '-', '2', '-', '1', '.', 'O'], [⟨['n', 'u', '\'', 'w', 'i'], ['t', 'e', 'l', 'l', '.', 'o', 'f', 'f'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['a', 'n'], ['2'], some '-'⟩, ⟨['k', 'u'], ['1', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "1"), ("objectNumber", "min"), ("objectSyntax", "dropped")] }

def ex_7a_ri : Datum :=
  { id := "clemdeal2026_7a_ri"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "I'wara kema-ri nu'wi-r-an-ku."
    glossedTokens := [("I'wara", "yesterday"), ("kema-ri", "2-ERG"), ("nu'wi-r-an-ku", "tell.off-IND-2-1.O")]
    glossedWords := [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['k', 'e', 'm', 'a', '-', 'r', 'i'], ['2', '-', 'E', 'R', 'G'], [⟨['k', 'e', 'm', 'a'], ['2'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['n', 'u', '\'', 'w', 'i', '-', 'r', '-', 'a', 'n', '-', 'k', 'u'], ['t', 'e', 'l', 'l', '.', 'o', 'f', 'f', '-', 'I', 'N', 'D', '-', '2', '-', '1', '.', 'O'], [⟨['n', 'u', '\'', 'w', 'i'], ['t', 'e', 'l', 'l', '.', 'o', 'f', 'f'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['a', 'n'], ['2'], some '-'⟩, ⟨['k', 'u'], ['1', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "1"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_7b : Datum :=
  { id := "clemdeal2026_7b"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ya'wan-rusa kete-r-in-kui."
    glossedTokens := [("Ya'wan-rusa", "snake-PL"), ("kete-r-in-kui", "bite-IND-3-1PL.EXCL.O")]
    glossedWords := [⟨['Y', 'a', '\'', 'w', 'a', 'n', '-', 'r', 'u', 's', 'a'], ['s', 'n', 'a', 'k', 'e', '-', 'P', 'L'], [⟨['Y', 'a', '\'', 'w', 'a', 'n'], ['s', 'n', 'a', 'k', 'e'], none⟩, ⟨['r', 'u', 's', 'a'], ['P', 'L'], some '-'⟩]⟩, ⟨['k', 'e', 't', 'e', '-', 'r', '-', 'i', 'n', '-', 'k', 'u', 'i'], ['b', 'i', 't', 'e', '-', 'I', 'N', 'D', '-', '3', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '.', 'O'], [⟨['k', 'e', 't', 'e'], ['b', 'i', 't', 'e'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩, ⟨['k', 'u', 'i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ya'wan-usa kete-r-in-kui.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "aug"), ("object", "1excl"), ("objectNumber", "aug"), ("objectSyntax", "dropped")] }

def ex_7b_ri : Datum :=
  { id := "clemdeal2026_7b_ri"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ya'wan-rusa-ri kete-r-in-kui."
    glossedTokens := [("Ya'wan-rusa-ri", "snake-PL-ERG"), ("kete-r-in-kui", "bite-IND-3-1PL.EXCL.O")]
    glossedWords := [⟨['Y', 'a', '\'', 'w', 'a', 'n', '-', 'r', 'u', 's', 'a', '-', 'r', 'i'], ['s', 'n', 'a', 'k', 'e', '-', 'P', 'L', '-', 'E', 'R', 'G'], [⟨['Y', 'a', '\'', 'w', 'a', 'n'], ['s', 'n', 'a', 'k', 'e'], none⟩, ⟨['r', 'u', 's', 'a'], ['P', 'L'], some '-'⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'e', 't', 'e', '-', 'r', '-', 'i', 'n', '-', 'k', 'u', 'i'], ['b', 'i', 't', 'e', '-', 'I', 'N', 'D', '-', '3', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '.', 'O'], [⟨['k', 'e', 't', 'e'], ['b', 'i', 't', 'e'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩, ⟨['k', 'u', 'i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "aug"), ("object", "1excl"), ("objectNumber", "aug"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_7c : Datum :=
  { id := "clemdeal2026_7c"
    source := ⟨"bourdeau-2015", "p. 28"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru nate-r-in-ke."
    glossedTokens := [("Pitru", "Peter"), ("nate-r-in-ke", "trust-IND-3-2.O")]
    glossedWords := [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['n', 'a', 't', 'e', '-', 'r', '-', 'i', 'n', '-', 'k', 'e'], ['t', 'r', 'u', 's', 't', '-', 'I', 'N', 'D', '-', '3', '-', '2', '.', 'O'], [⟨['n', 'a', 't', 'e'], ['t', 'r', 'u', 's', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩, ⟨['k', 'e'], ['2', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Pitru nate-r-in-nke.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "2"), ("objectNumber", "min"), ("objectSyntax", "dropped")] }

def ex_7c_ri : Datum :=
  { id := "clemdeal2026_7c_ri"
    source := ⟨"bourdeau-2015", "p. 28"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru-ri nate-r-in-ke."
    glossedTokens := [("Pitru-ri", "Peter-ERG"), ("nate-r-in-ke", "trust-IND-3-2.O")]
    glossedWords := [⟨['P', 'i', 't', 'r', 'u', '-', 'r', 'i'], ['P', 'e', 't', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['n', 'a', 't', 'e', '-', 'r', '-', 'i', 'n', '-', 'k', 'e'], ['t', 'r', 'u', 's', 't', '-', 'I', 'N', 'D', '-', '3', '-', '2', '.', 'O'], [⟨['n', 'a', 't', 'e'], ['t', 'r', 'u', 's', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩, ⟨['k', 'e'], ['2', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "2"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_8a : Datum :=
  { id := "clemdeal2026_8a"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya na'wan-ra-i Pitru."
    glossedTokens := [("Kiya", "1PL.EXCL"), ("na'wan-ra-i", "miss-IND-1PL.EXCL"), ("Pitru", "Peter")]
    glossedWords := [⟨['K', 'i', 'y', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], [⟨['K', 'i', 'y', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], none⟩]⟩, ⟨['n', 'a', '\'', 'w', 'a', 'n', '-', 'r', 'a', '-', 'i'], ['m', 'i', 's', 's', '-', 'I', 'N', 'D', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], [⟨['n', 'a', '\'', 'w', 'a', 'n'], ['m', 'i', 's', 's'], none⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], some '-'⟩]⟩, ⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Kiya na'wan-a-i Pitru.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_8a_ri : Datum :=
  { id := "clemdeal2026_8a_ri"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya-ri na'wan-ra-i Pitru."
    glossedTokens := [("Kiya-ri", "1PL.EXCL-ERG"), ("na'wan-ra-i", "miss-IND-1PL.EXCL"), ("Pitru", "Peter")]
    glossedWords := [⟨['K', 'i', 'y', 'a', '-', 'r', 'i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '-', 'E', 'R', 'G'], [⟨['K', 'i', 'y', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['n', 'a', '\'', 'w', 'a', 'n', '-', 'r', 'a', '-', 'i'], ['m', 'i', 's', 's', '-', 'I', 'N', 'D', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], [⟨['n', 'a', '\'', 'w', 'a', 'n'], ['m', 'i', 's', 's'], none⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['i'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], some '-'⟩]⟩, ⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Kiya-ri na'wan-a-i Pitru.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_8b : Datum :=
  { id := "clemdeal2026_8b"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kema paki-r-an mi'ne."
    glossedTokens := [("Kema", "2"), ("paki-r-an", "break-IND-2"), ("mi'ne", "mocahua")]
    glossedWords := [⟨['K', 'e', 'm', 'a'], ['2'], [⟨['K', 'e', 'm', 'a'], ['2'], none⟩]⟩, ⟨['p', 'a', 'k', 'i', '-', 'r', '-', 'a', 'n'], ['b', 'r', 'e', 'a', 'k', '-', 'I', 'N', 'D', '-', '2'], [⟨['p', 'a', 'k', 'i'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['a', 'n'], ['2'], some '-'⟩]⟩, ⟨['m', 'i', '\'', 'n', 'e'], ['m', 'o', 'c', 'a', 'h', 'u', 'a'], [⟨['m', 'i', '\'', 'n', 'e'], ['m', 'o', 'c', 'a', 'h', 'u', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_8b_ri : Datum :=
  { id := "clemdeal2026_8b_ri"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kema-ri paki-r-an mi'ne."
    glossedTokens := [("Kema-ri", "2-ERG"), ("paki-r-an", "break-IND-2"), ("mi'ne", "mocahua")]
    glossedWords := [⟨['K', 'e', 'm', 'a', '-', 'r', 'i'], ['2', '-', 'E', 'R', 'G'], [⟨['K', 'e', 'm', 'a'], ['2'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'a', 'k', 'i', '-', 'r', '-', 'a', 'n'], ['b', 'r', 'e', 'a', 'k', '-', 'I', 'N', 'D', '-', '2'], [⟨['p', 'a', 'k', 'i'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['a', 'n'], ['2'], some '-'⟩]⟩, ⟨['m', 'i', '\'', 'n', 'e'], ['m', 'o', 'c', 'a', 'h', 'u', 'a'], [⟨['m', 'i', '\'', 'n', 'e'], ['m', 'o', 'c', 'a', 'h', 'u', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_8c : Datum :=
  { id := "clemdeal2026_8c"
    source := ⟨"bourdeau-2015", "p. 33"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru iwa-r-in pepekunu."
    glossedTokens := [("Pitru", "Peter"), ("iwa-r-in", "steal-IND-3"), ("pepekunu", "necklace")]
    glossedWords := [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['i', 'w', 'a', '-', 'r', '-', 'i', 'n'], ['s', 't', 'e', 'a', 'l', '-', 'I', 'N', 'D', '-', '3'], [⟨['i', 'w', 'a'], ['s', 't', 'e', 'a', 'l'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩, ⟨['p', 'e', 'p', 'e', 'k', 'u', 'n', 'u'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e'], [⟨['p', 'e', 'p', 'e', 'k', 'u', 'n', 'u'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_8c_ri : Datum :=
  { id := "clemdeal2026_8c_ri"
    source := ⟨"bourdeau-2015", "p. 33"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru-ri iwa-r-in pepekunu."
    glossedTokens := [("Pitru-ri", "Peter-ERG"), ("iwa-r-in", "steal-IND-3"), ("pepekunu", "necklace")]
    glossedWords := [⟨['P', 'i', 't', 'r', 'u', '-', 'r', 'i'], ['P', 'e', 't', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['i', 'w', 'a', '-', 'r', '-', 'i', 'n'], ['s', 't', 'e', 'a', 'l', '-', 'I', 'N', 'D', '-', '3'], [⟨['i', 'w', 'a'], ['s', 't', 'e', 'a', 'l'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩, ⟨['p', 'e', 'p', 'e', 'k', 'u', 'n', 'u'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e'], [⟨['p', 'e', 'p', 'e', 'k', 'u', 'n', 'u'], ['n', 'e', 'c', 'k', 'l', 'a', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_9a : Datum :=
  { id := "clemdeal2026_9a"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pituru Kusi awe-r-in."
    glossedTokens := [("Pituru", "Pedro"), ("Kusi", "Jose"), ("awe-r-in", "hit-IND-3")]
    glossedWords := [⟨['P', 'i', 't', 'u', 'r', 'u'], ['P', 'e', 'd', 'r', 'o'], [⟨['P', 'i', 't', 'u', 'r', 'u'], ['P', 'e', 'd', 'r', 'o'], none⟩]⟩, ⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], [⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], none⟩]⟩, ⟨['a', 'w', 'e', '-', 'r', '-', 'i', 'n'], ['h', 'i', 't', '-', 'I', 'N', 'D', '-', '3'], [⟨['a', 'w', 'e'], ['h', 'i', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_9a_ri : Datum :=
  { id := "clemdeal2026_9a_ri"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pituru-ri Kusi awe-r-in."
    glossedTokens := [("Pituru-ri", "Pedro-ERG"), ("Kusi", "Jose"), ("awe-r-in", "hit-IND-3")]
    glossedWords := [⟨['P', 'i', 't', 'u', 'r', 'u', '-', 'r', 'i'], ['P', 'e', 'd', 'r', 'o', '-', 'E', 'R', 'G'], [⟨['P', 'i', 't', 'u', 'r', 'u'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], [⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], none⟩]⟩, ⟨['a', 'w', 'e', '-', 'r', '-', 'i', 'n'], ['h', 'i', 't', '-', 'I', 'N', 'D', '-', '3'], [⟨['a', 'w', 'e'], ['h', 'i', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_9b : Datum :=
  { id := "clemdeal2026_9b"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kusi Pituru awe-r-in."
    glossedTokens := [("Kusi", "Jose"), ("Pituru", "Pedro"), ("awe-r-in", "hit-IND-3")]
    glossedWords := [⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], [⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], none⟩]⟩, ⟨['P', 'i', 't', 'u', 'r', 'u'], ['P', 'e', 'd', 'r', 'o'], [⟨['P', 'i', 't', 'u', 'r', 'u'], ['P', 'e', 'd', 'r', 'o'], none⟩]⟩, ⟨['a', 'w', 'e', '-', 'r', '-', 'i', 'n'], ['h', 'i', 't', '-', 'I', 'N', 'D', '-', '3'], [⟨['a', 'w', 'e'], ['h', 'i', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "fronted")] }

def ex_9b_ri : Datum :=
  { id := "clemdeal2026_9b_ri"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kusi Pituru-ri awe-r-in."
    glossedTokens := [("Kusi", "Jose"), ("Pituru-ri", "Pedro-ERG"), ("awe-r-in", "hit-IND-3")]
    glossedWords := [⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], [⟨['K', 'u', 's', 'i'], ['J', 'o', 's', 'e'], none⟩]⟩, ⟨['P', 'i', 't', 'u', 'r', 'u', '-', 'r', 'i'], ['P', 'e', 'd', 'r', 'o', '-', 'E', 'R', 'G'], [⟨['P', 'i', 't', 'u', 'r', 'u'], ['P', 'e', 'd', 'r', 'o'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['a', 'w', 'e', '-', 'r', '-', 'i', 'n'], ['h', 'i', 't', '-', 'I', 'N', 'D', '-', '3'], [⟨['a', 'w', 'e'], ['h', 'i', 't'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "fronted"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_11 : Datum :=
  { id := "clemdeal2026_11"
    source := ⟨"clem-deal-2026", "(11)"⟩
    reportedIn := none
    method := some .elicitation
    language := "chay1248"
    primaryText := "I'wara kema-ku nu'wi-r-an-ku."
    glossedTokens := [("I'wara", "yesterday"), ("kema-ku", "2-1.O"), ("nu'wi-r-an-ku", "tell.off-IND-2-1.O")]
    glossedWords := [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', '\'', 'w', 'a', 'r', 'a'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['k', 'e', 'm', 'a', '-', 'k', 'u'], ['2', '-', '1', '.', 'O'], [⟨['k', 'e', 'm', 'a'], ['2'], none⟩, ⟨['k', 'u'], ['1', '.', 'O'], some '-'⟩]⟩, ⟨['n', 'u', '\'', 'w', 'i', '-', 'r', '-', 'a', 'n', '-', 'k', 'u'], ['t', 'e', 'l', 'l', '.', 'o', 'f', 'f', '-', 'I', 'N', 'D', '-', '2', '-', '1', '.', 'O'], [⟨['n', 'u', '\'', 'w', 'i'], ['t', 'e', 'l', 'l', '.', 'o', 'f', 'f'], none⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['a', 'n'], ['2'], some '-'⟩, ⟨['k', 'u'], ['1', '.', 'O'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "1"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("oagrOnS", "-ku")] }

def ex_21a : Datum :=
  { id := "clemdeal2026_21a"
    source := ⟨"barraza-de-garcia-2005", "p. 161"⟩
    reportedIn := some ⟨"clem-deal-2026", "(21a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Sanapi i-te-r-in."
    glossedTokens := [("Sanapi", "woman"), ("i-te-r-in", "say-VAL-IND-3")]
    glossedWords := [⟨['S', 'a', 'n', 'a', 'p', 'i'], ['w', 'o', 'm', 'a', 'n'], [⟨['S', 'a', 'n', 'a', 'p', 'i'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['i', '-', 't', 'e', '-', 'r', '-', 'i', 'n'], ['s', 'a', 'y', '-', 'V', 'A', 'L', '-', 'I', 'N', 'D', '-', '3'], [⟨['i'], ['s', 'a', 'y'], none⟩, ⟨['t', 'e'], ['V', 'A', 'L'], some '-'⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "dropped")] }

def ex_21a_ri : Datum :=
  { id := "clemdeal2026_21a_ri"
    source := ⟨"barraza-de-garcia-2005", "p. 161"⟩
    reportedIn := some ⟨"clem-deal-2026", "(21a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Sanapi-ri i-te-r-in."
    glossedTokens := [("Sanapi-ri", "woman-ERG"), ("i-te-r-in", "say-VAL-IND-3")]
    glossedWords := [⟨['S', 'a', 'n', 'a', 'p', 'i', '-', 'r', 'i'], ['w', 'o', 'm', 'a', 'n', '-', 'E', 'R', 'G'], [⟨['S', 'a', 'n', 'a', 'p', 'i'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['i', '-', 't', 'e', '-', 'r', '-', 'i', 'n'], ['s', 'a', 'y', '-', 'V', 'A', 'L', '-', 'I', 'N', 'D', '-', '3'], [⟨['i'], ['s', 'a', 'y'], none⟩, ⟨['t', 'e'], ['V', 'A', 'L'], some '-'⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_21b : Datum :=
  { id := "clemdeal2026_21b"
    source := ⟨"barraza-de-garcia-2005", "p. 162"⟩
    reportedIn := some ⟨"clem-deal-2026", "(21b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Sanapi i-te-r-in."
    glossedTokens := [("Sanapi", "woman"), ("i-te-r-in", "say-VAL-IND-3")]
    glossedWords := [⟨['S', 'a', 'n', 'a', 'p', 'i'], ['w', 'o', 'm', 'a', 'n'], [⟨['S', 'a', 'n', 'a', 'p', 'i'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['i', '-', 't', 'e', '-', 'r', '-', 'i', 'n'], ['s', 'a', 'y', '-', 'V', 'A', 'L', '-', 'I', 'N', 'D', '-', '3'], [⟨['i'], ['s', 'a', 'y'], none⟩, ⟨['t', 'e'], ['V', 'A', 'L'], some '-'⟩, ⟨['r'], ['I', 'N', 'D'], some '-'⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_27 : Datum :=
  { id := "clemdeal2026_27"
    source := ⟨"bourdeau-2015", "p. 32"⟩
    reportedIn := some ⟨"clem-deal-2026", "(27)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru na'wan-in sa'-in."
    glossedTokens := [("Pitru", "Peter"), ("na'wan-in", "miss-3"), ("sa'-in", "spouse-3")]
    glossedWords := [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['n', 'a', '\'', 'w', 'a', 'n', '-', 'i', 'n'], ['m', 'i', 's', 's', '-', '3'], [⟨['n', 'a', '\'', 'w', 'a', 'n'], ['m', 'i', 's', 's'], none⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩, ⟨['s', 'a', '\'', '-', 'i', 'n'], ['s', 'p', 'o', 'u', 's', 'e', '-', '3'], [⟨['s', 'a', '\''], ['s', 'p', 'o', 'u', 's', 'e'], none⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_27_ri : Datum :=
  { id := "clemdeal2026_27_ri"
    source := ⟨"bourdeau-2015", "p. 32"⟩
    reportedIn := some ⟨"clem-deal-2026", "(27)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru-ri na'wan-in sa'-in."
    glossedTokens := [("Pitru-ri", "Peter-ERG"), ("na'wan-in", "miss-3"), ("sa'-in", "spouse-3")]
    glossedWords := [⟨['P', 'i', 't', 'r', 'u', '-', 'r', 'i'], ['P', 'e', 't', 'e', 'r', '-', 'E', 'R', 'G'], [⟨['P', 'i', 't', 'r', 'u'], ['P', 'e', 't', 'e', 'r'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['n', 'a', '\'', 'w', 'a', 'n', '-', 'i', 'n'], ['m', 'i', 's', 's', '-', '3'], [⟨['n', 'a', '\'', 'w', 'a', 'n'], ['m', 'i', 's', 's'], none⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩, ⟨['s', 'a', '\'', '-', 'i', 'n'], ['s', 'p', 'o', 'u', 's', 'e', '-', '3'], [⟨['s', 'a', '\''], ['s', 'p', 'o', 'u', 's', 'e'], none⟩, ⟨['i', 'n'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_28 : Datum :=
  { id := "clemdeal2026_28"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(28)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka mapa-te-ra-we kara kayu atari kayu."
    glossedTokens := [("Ka", "1"), ("mapa-te-ra-we", "receive-VAL-IND-1"), ("kara", "three"), ("kayu", "egg"), ("atari", "hen"), ("kayu", "egg")]
    glossedWords := [⟨['K', 'a'], ['1'], [⟨['K', 'a'], ['1'], none⟩]⟩, ⟨['m', 'a', 'p', 'a', '-', 't', 'e', '-', 'r', 'a', '-', 'w', 'e'], ['r', 'e', 'c', 'e', 'i', 'v', 'e', '-', 'V', 'A', 'L', '-', 'I', 'N', 'D', '-', '1'], [⟨['m', 'a', 'p', 'a'], ['r', 'e', 'c', 'e', 'i', 'v', 'e'], none⟩, ⟨['t', 'e'], ['V', 'A', 'L'], some '-'⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['w', 'e'], ['1'], some '-'⟩]⟩, ⟨['k', 'a', 'r', 'a'], ['t', 'h', 'r', 'e', 'e'], [⟨['k', 'a', 'r', 'a'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], [⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], none⟩]⟩, ⟨['a', 't', 'a', 'r', 'i'], ['h', 'e', 'n'], [⟨['a', 't', 'a', 'r', 'i'], ['h', 'e', 'n'], none⟩]⟩, ⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], [⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "aug"), ("objectSyntax", "inSitu")] }

def ex_28_ri : Datum :=
  { id := "clemdeal2026_28_ri"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(28)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka-ri mapa-te-ra-we kara kayu atari kayu."
    glossedTokens := [("Ka-ri", "1-ERG"), ("mapa-te-ra-we", "receive-VAL-IND-1"), ("kara", "three"), ("kayu", "egg"), ("atari", "hen"), ("kayu", "egg")]
    glossedWords := [⟨['K', 'a', '-', 'r', 'i'], ['1', '-', 'E', 'R', 'G'], [⟨['K', 'a'], ['1'], none⟩, ⟨['r', 'i'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'p', 'a', '-', 't', 'e', '-', 'r', 'a', '-', 'w', 'e'], ['r', 'e', 'c', 'e', 'i', 'v', 'e', '-', 'V', 'A', 'L', '-', 'I', 'N', 'D', '-', '1'], [⟨['m', 'a', 'p', 'a'], ['r', 'e', 'c', 'e', 'i', 'v', 'e'], none⟩, ⟨['t', 'e'], ['V', 'A', 'L'], some '-'⟩, ⟨['r', 'a'], ['I', 'N', 'D'], some '-'⟩, ⟨['w', 'e'], ['1'], some '-'⟩]⟩, ⟨['k', 'a', 'r', 'a'], ['t', 'h', 'r', 'e', 'e'], [⟨['k', 'a', 'r', 'a'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], [⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], none⟩]⟩, ⟨['a', 't', 'a', 'r', 'i'], ['h', 'e', 'n'], [⟨['a', 't', 'a', 'r', 'i'], ['h', 'e', 'n'], none⟩]⟩, ⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], [⟨['k', 'a', 'y', 'u'], ['e', 'g', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "aug"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_42a : Datum :=
  { id := "clemdeal2026_42a"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42a)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha salamat türgennik sie-te."
    glossedTokens := [("Masha", "Masha"), ("salamat", "porridge"), ("türgennik", "quickly"), ("sie-te", "eat-PST.3SG")]
    glossedWords := [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩]⟩, ⟨['s', 'a', 'l', 'a', 'm', 'a', 't'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e'], [⟨['s', 'a', 'l', 'a', 'm', 'a', 't'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e'], none⟩]⟩, ⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], [⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], none⟩]⟩, ⟨['s', 'i', 'e', '-', 't', 'e'], ['e', 'a', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['s', 'i', 'e'], ['e', 'a', 't'], none⟩, ⟨['t', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "fronted")] }

def ex_42a_y : Datum :=
  { id := "clemdeal2026_42a_y"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42a)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha salamat-y türgennik sie-te."
    glossedTokens := [("Masha", "Masha"), ("salamat-y", "porridge-ACC"), ("türgennik", "quickly"), ("sie-te", "eat-PST.3SG")]
    glossedWords := [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩]⟩, ⟨['s', 'a', 'l', 'a', 'm', 'a', 't', '-', 'y'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'l', 'a', 'm', 'a', 't'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e'], none⟩, ⟨['y'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], [⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], none⟩]⟩, ⟨['s', 'i', 'e', '-', 't', 'e'], ['e', 'a', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['s', 'i', 'e'], ['e', 'a', 't'], none⟩, ⟨['t', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "fronted"), ("case", "-y"), ("caseOn", "object")] }

def ex_42b : Datum :=
  { id := "clemdeal2026_42b"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42b)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha türgennik salamat sie-te."
    glossedTokens := [("Masha", "Masha"), ("türgennik", "quickly"), ("salamat", "porridge"), ("sie-te", "eat-PST.3SG")]
    glossedWords := [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩]⟩, ⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], [⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], none⟩]⟩, ⟨['s', 'a', 'l', 'a', 'm', 'a', 't'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e'], [⟨['s', 'a', 'l', 'a', 'm', 'a', 't'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e'], none⟩]⟩, ⟨['s', 'i', 'e', '-', 't', 'e'], ['e', 'a', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['s', 'i', 'e'], ['e', 'a', 't'], none⟩, ⟨['t', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "belowAdverb")] }

def ex_42b_y : Datum :=
  { id := "clemdeal2026_42b_y"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42b)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha türgennik salamat-y sie-te."
    glossedTokens := [("Masha", "Masha"), ("türgennik", "quickly"), ("salamat-y", "porridge-ACC"), ("sie-te", "eat-PST.3SG")]
    glossedWords := [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩]⟩, ⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], [⟨['t', 'ü', 'r', 'g', 'e', 'n', 'n', 'i', 'k'], ['q', 'u', 'i', 'c', 'k', 'l', 'y'], none⟩]⟩, ⟨['s', 'a', 'l', 'a', 'm', 'a', 't', '-', 'y'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e', '-', 'A', 'C', 'C'], [⟨['s', 'a', 'l', 'a', 'm', 'a', 't'], ['p', 'o', 'r', 'r', 'i', 'd', 'g', 'e'], none⟩, ⟨['y'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'i', 'e', '-', 't', 'e'], ['e', 'a', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['s', 'i', 'e'], ['e', 'a', 't'], none⟩, ⟨['t', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "belowAdverb"), ("case", "-y"), ("caseOn", "object")] }

def ex_45a : Datum :=
  { id := "clemdeal2026_45a"
    source := ⟨"valenzuela-2011", "p. 100"⟩
    reportedIn := some ⟨"clem-deal-2026", "(45a)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kwa tek-susu-llen."
    glossedTokens := [("Kwa", "1SG"), ("tek-susu-llen", "CAUS-grow.up-1SG>2SG")]
    glossedWords := [⟨['K', 'w', 'a'], ['1', 'S', 'G'], [⟨['K', 'w', 'a'], ['1', 'S', 'G'], none⟩]⟩, ⟨['t', 'e', 'k', '-', 's', 'u', 's', 'u', '-', 'l', 'l', 'e', 'n'], ['C', 'A', 'U', 'S', '-', 'g', 'r', 'o', 'w', '.', 'u', 'p', '-', '1', 'S', 'G', '>', '2', 'S', 'G'], [⟨['t', 'e', 'k'], ['C', 'A', 'U', 'S'], none⟩, ⟨['s', 'u', 's', 'u'], ['g', 'r', 'o', 'w', '.', 'u', 'p'], some '-'⟩, ⟨['l', 'l', 'e', 'n'], ['1', 'S', 'G', '>', '2', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "sg"), ("object", "2"), ("objectNumber", "sg"), ("objectSyntax", "dropped")] }

def ex_45b : Datum :=
  { id := "clemdeal2026_45b"
    source := ⟨"valenzuela-2011", "p. 100"⟩
    reportedIn := some ⟨"clem-deal-2026", "(45b)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Ma'ki'na kenmama' lumer-lama'u'ku?"
    glossedTokens := [("Ma'ki'na", "why"), ("kenmama'", "2PL"), ("lumer-lama'u'ku", "laugh.at-NFUT.2PL>1SG")]
    glossedWords := [⟨['M', 'a', '\'', 'k', 'i', '\'', 'n', 'a'], ['w', 'h', 'y'], [⟨['M', 'a', '\'', 'k', 'i', '\'', 'n', 'a'], ['w', 'h', 'y'], none⟩]⟩, ⟨['k', 'e', 'n', 'm', 'a', 'm', 'a', '\''], ['2', 'P', 'L'], [⟨['k', 'e', 'n', 'm', 'a', 'm', 'a', '\''], ['2', 'P', 'L'], none⟩]⟩, ⟨['l', 'u', 'm', 'e', 'r', '-', 'l', 'a', 'm', 'a', '\'', 'u', '\'', 'k', 'u'], ['l', 'a', 'u', 'g', 'h', '.', 'a', 't', '-', 'N', 'F', 'U', 'T', '.', '2', 'P', 'L', '>', '1', 'S', 'G'], [⟨['l', 'u', 'm', 'e', 'r'], ['l', 'a', 'u', 'g', 'h', '.', 'a', 't'], none⟩, ⟨['l', 'a', 'm', 'a', '\'', 'u', '\'', 'k', 'u'], ['N', 'F', 'U', 'T', '.', '2', 'P', 'L', '>', '1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "pl"), ("object", "1"), ("objectNumber", "sg"), ("objectSyntax", "dropped")] }

def ex_46a : Datum :=
  { id := "clemdeal2026_46a"
    source := ⟨"valenzuela-2011", "p. 100"⟩
    reportedIn := some ⟨"clem-deal-2026", "(46a)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kuda=ler aperku-tu-dek-llidek pu'yek."
    glossedTokens := [("Kuda=ler", "1PL.EXCL=ERG"), ("aperku-tu-dek-llidek", "not.share-VAL-3PL.O-1PL.EXCL>3PL"), ("pu'yek", "fishing")]
    glossedWords := [⟨['K', 'u', 'd', 'a', '=', 'l', 'e', 'r'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '=', 'E', 'R', 'G'], [⟨['K', 'u', 'd', 'a'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L'], none⟩, ⟨['l', 'e', 'r'], ['E', 'R', 'G'], some '='⟩]⟩, ⟨['a', 'p', 'e', 'r', 'k', 'u', '-', 't', 'u', '-', 'd', 'e', 'k', '-', 'l', 'l', 'i', 'd', 'e', 'k'], ['n', 'o', 't', '.', 's', 'h', 'a', 'r', 'e', '-', 'V', 'A', 'L', '-', '3', 'P', 'L', '.', 'O', '-', '1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '>', '3', 'P', 'L'], [⟨['a', 'p', 'e', 'r', 'k', 'u'], ['n', 'o', 't', '.', 's', 'h', 'a', 'r', 'e'], none⟩, ⟨['t', 'u'], ['V', 'A', 'L'], some '-'⟩, ⟨['d', 'e', 'k'], ['3', 'P', 'L', '.', 'O'], some '-'⟩, ⟨['l', 'l', 'i', 'd', 'e', 'k'], ['1', 'P', 'L', '.', 'E', 'X', 'C', 'L', '>', '3', 'P', 'L'], some '-'⟩]⟩, ⟨['p', 'u', '\'', 'y', 'e', 'k'], ['f', 'i', 's', 'h', 'i', 'n', 'g'], [⟨['p', 'u', '\'', 'y', 'e', 'k'], ['f', 'i', 's', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "pl"), ("object", "3"), ("objectNumber", "pl"), ("objectSyntax", "dropped"), ("case", "=ler"), ("caseOn", "subject")] }

def ex_46b : Datum :=
  { id := "clemdeal2026_46b"
    source := ⟨"valenzuela-2011", "p. 105"⟩
    reportedIn := some ⟨"clem-deal-2026", "(46b)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kishu ka'-lli nana isha."
    glossedTokens := [("Kishu", "Jesús"), ("ka'-lli", "eat-NFUT.3SG"), ("nana", "that"), ("isha", "paujil")]
    glossedWords := [⟨['K', 'i', 's', 'h', 'u'], ['J', 'e', 's', 'ú', 's'], [⟨['K', 'i', 's', 'h', 'u'], ['J', 'e', 's', 'ú', 's'], none⟩]⟩, ⟨['k', 'a', '\'', '-', 'l', 'l', 'i'], ['e', 'a', 't', '-', 'N', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['k', 'a', '\''], ['e', 'a', 't'], none⟩, ⟨['l', 'l', 'i'], ['N', 'F', 'U', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['n', 'a', 'n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a', 'n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['i', 's', 'h', 'a'], ['p', 'a', 'u', 'j', 'i', 'l'], [⟨['i', 's', 'h', 'a'], ['p', 'a', 'u', 'j', 'i', 'l'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "inSitu")] }

def ex_46b_ler : Datum :=
  { id := "clemdeal2026_46b_ler"
    source := ⟨"valenzuela-2011", "p. 105"⟩
    reportedIn := some ⟨"clem-deal-2026", "(46b)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kishu=ler ka'-lli nana isha."
    glossedTokens := [("Kishu=ler", "Jesús=ERG"), ("ka'-lli", "eat-NFUT.3SG"), ("nana", "that"), ("isha", "paujil")]
    glossedWords := [⟨['K', 'i', 's', 'h', 'u', '=', 'l', 'e', 'r'], ['J', 'e', 's', 'ú', 's', '=', 'E', 'R', 'G'], [⟨['K', 'i', 's', 'h', 'u'], ['J', 'e', 's', 'ú', 's'], none⟩, ⟨['l', 'e', 'r'], ['E', 'R', 'G'], some '='⟩]⟩, ⟨['k', 'a', '\'', '-', 'l', 'l', 'i'], ['e', 'a', 't', '-', 'N', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['k', 'a', '\''], ['e', 'a', 't'], none⟩, ⟨['l', 'l', 'i'], ['N', 'F', 'U', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['n', 'a', 'n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a', 'n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['i', 's', 'h', 'a'], ['p', 'a', 'u', 'j', 'i', 'l'], [⟨['i', 's', 'h', 'a'], ['p', 'a', 'u', 'j', 'i', 'l'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "inSitu"), ("case", "=ler"), ("caseOn", "subject")] }

def ex_49a : Datum :=
  { id := "clemdeal2026_49a"
    source := ⟨"maslova-2003", "p. 93"⟩
    reportedIn := some ⟨"clem-deal-2026", "(49a)"⟩
    method := some .description
    language := "sout2750"
    primaryText := "Tet kimnī met-kele kudede-m."
    glossedTokens := [("Tet", "your"), ("kimnī", "whip"), ("met-kele", "me-ACC"), ("kudede-m", "kill-TR.3SG")]
    glossedWords := [⟨['T', 'e', 't'], ['y', 'o', 'u', 'r'], [⟨['T', 'e', 't'], ['y', 'o', 'u', 'r'], none⟩]⟩, ⟨['k', 'i', 'm', 'n', 'ī'], ['w', 'h', 'i', 'p'], [⟨['k', 'i', 'm', 'n', 'ī'], ['w', 'h', 'i', 'p'], none⟩]⟩, ⟨['m', 'e', 't', '-', 'k', 'e', 'l', 'e'], ['m', 'e', '-', 'A', 'C', 'C'], [⟨['m', 'e', 't'], ['m', 'e'], none⟩, ⟨['k', 'e', 'l', 'e'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'u', 'd', 'e', 'd', 'e', '-', 'm'], ['k', 'i', 'l', 'l', '-', 'T', 'R', '.', '3', 'S', 'G'], [⟨['k', 'u', 'd', 'e', 'd', 'e'], ['k', 'i', 'l', 'l'], none⟩, ⟨['m'], ['T', 'R', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "1"), ("objectNumber", "sg"), ("objectSyntax", "inSitu"), ("case", "-gele"), ("caseOn", "object")] }

def ex_49b : Datum :=
  { id := "clemdeal2026_49b"
    source := ⟨"maslova-2003", "p. 95"⟩
    reportedIn := some ⟨"clem-deal-2026", "(49b)"⟩
    method := some .description
    language := "sout2750"
    primaryText := "Met tet-ul kudede-t."
    glossedTokens := [("Met", "I"), ("tet-ul", "you-ACC"), ("kudede-t", "kill-FUT(TR.1SG)")]
    glossedWords := [⟨['M', 'e', 't'], ['I'], [⟨['M', 'e', 't'], ['I'], none⟩]⟩, ⟨['t', 'e', 't', '-', 'u', 'l'], ['y', 'o', 'u', '-', 'A', 'C', 'C'], [⟨['t', 'e', 't'], ['y', 'o', 'u'], none⟩, ⟨['u', 'l'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'u', 'd', 'e', 'd', 'e', '-', 't'], ['k', 'i', 'l', 'l', '-', 'F', 'U', 'T', '(', 'T', 'R', '.', '1', 'S', 'G', ')'], [⟨['k', 'u', 'd', 'e', 'd', 'e'], ['k', 'i', 'l', 'l'], none⟩, ⟨['t'], ['F', 'U', 'T', '(', 'T', 'R', '.', '1', 'S', 'G', ')'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "sg"), ("object", "2"), ("objectNumber", "sg"), ("objectSyntax", "inSitu"), ("case", "-ul"), ("caseOn", "object")] }

def ex_49c : Datum :=
  { id := "clemdeal2026_49c"
    source := ⟨"maslova-2003", "p. 89"⟩
    reportedIn := some ⟨"clem-deal-2026", "(49c)"⟩
    method := some .description
    language := "sout2750"
    primaryText := "Met mēmē iŋī."
    glossedTokens := [("Met", "I"), ("mēmē", "bear"), ("iŋī", "be.afraid(TR.1SG)")]
    glossedWords := [⟨['M', 'e', 't'], ['I'], [⟨['M', 'e', 't'], ['I'], none⟩]⟩, ⟨['m', 'ē', 'm', 'ē'], ['b', 'e', 'a', 'r'], [⟨['m', 'ē', 'm', 'ē'], ['b', 'e', 'a', 'r'], none⟩]⟩, ⟨['i', 'ŋ', 'ī'], ['b', 'e', '.', 'a', 'f', 'r', 'a', 'i', 'd', '(', 'T', 'R', '.', '1', 'S', 'G', ')'], [⟨['i', 'ŋ', 'ī'], ['b', 'e', '.', 'a', 'f', 'r', 'a', 'i', 'd', '(', 'T', 'R', '.', '1', 'S', 'G', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "inSitu")] }

def all : List Datum := [ex_4a, ex_4a_ri, ex_4b, ex_4b_ri, ex_6a, ex_6b, ex_6b_nke, ex_7a, ex_7a_ri, ex_7b, ex_7b_ri, ex_7c, ex_7c_ri, ex_8a, ex_8a_ri, ex_8b, ex_8b_ri, ex_8c, ex_8c_ri, ex_9a, ex_9a_ri, ex_9b, ex_9b_ri, ex_11, ex_21a, ex_21a_ri, ex_21b, ex_27, ex_27_ri, ex_28, ex_28_ri, ex_42a, ex_42a_y, ex_42b, ex_42b_y, ex_45a, ex_45b, ex_46a, ex_46b, ex_46b_ler, ex_49a, ex_49b, ex_49c]

end ClemDeal2026.Examples
