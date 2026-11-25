module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Huumo2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Huumo2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Huumo2020.Examples`.
-/

@[expose] public section

namespace Huumo2020.Examples

def ex_17 : Datum :=
  { id := "huumo2020_17"
    source := ⟨"huumo-2020", "(17)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin lehden tunnissa."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("lehde-n", "paper-ACC"), ("tunni-ssa", "hour-INE")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['l', 'e', 'h', 'd', 'e', '-', 'n'], ['p', 'a', 'p', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['l', 'e', 'h', 'd', 'e'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 's', 's', 'a'], ['h', 'o', 'u', 'r', '-', 'I', 'N', 'E'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['s', 's', 'a'], ['I', 'N', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "acc"), ("adverbial", "timeFrame")] }

def ex_17_for : Datum :=
  { id := "huumo2020_17_for"
    source := ⟨"huumo-2020", "(17)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin lehden tunnin."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("lehde-n", "paper-ACC"), ("tunni-n", "hour-ACC")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['l', 'e', 'h', 'd', 'e', '-', 'n'], ['p', 'a', 'p', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['l', 'e', 'h', 'd', 'e'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 'n'], ['h', 'o', 'u', 'r', '-', 'A', 'C', 'C'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "acc"), ("adverbial", "measure")] }

def ex_18 : Datum :=
  { id := "huumo2020_18"
    source := ⟨"huumo-2020", "(18)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Katsoin televisiota tunnin."
    glossedTokens := [("Katso-i-n", "watch-PST-1SG"), ("televisio-ta", "television-PAR"), ("tunni-n", "hour-ACC")]
    glossedWords := [⟨['K', 'a', 't', 's', 'o', '-', 'i', '-', 'n'], ['w', 'a', 't', 'c', 'h', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['K', 'a', 't', 's', 'o'], ['w', 'a', 't', 'c', 'h'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', '-', 't', 'a'], ['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n', '-', 'P', 'A', 'R'], [⟨['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o'], ['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n'], none⟩, ⟨['t', 'a'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 'n'], ['h', 'o', 'u', 'r', '-', 'A', 'C', 'C'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "measure")] }

def ex_18_in : Datum :=
  { id := "huumo2020_18_in"
    source := ⟨"huumo-2020", "(18)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Katsoin televisiota tunnissa."
    glossedTokens := [("Katso-i-n", "watch-PST-1SG"), ("televisio-ta", "television-PAR"), ("tunni-ssa", "hour-INE")]
    glossedWords := [⟨['K', 'a', 't', 's', 'o', '-', 'i', '-', 'n'], ['w', 'a', 't', 'c', 'h', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['K', 'a', 't', 's', 'o'], ['w', 'a', 't', 'c', 'h'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', '-', 't', 'a'], ['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n', '-', 'P', 'A', 'R'], [⟨['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o'], ['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n'], none⟩, ⟨['t', 'a'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 's', 's', 'a'], ['h', 'o', 'u', 'r', '-', 'I', 'N', 'E'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['s', 's', 'a'], ['I', 'N', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_19 : Datum :=
  { id := "huumo2020_19"
    source := ⟨"huumo-2020", "(19)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin lehteä tunnin."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("lehte-ä", "paper-PAR"), ("tunni-n", "hour-ACC")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['l', 'e', 'h', 't', 'e', '-', 'ä'], ['p', 'a', 'p', 'e', 'r', '-', 'P', 'A', 'R'], [⟨['l', 'e', 'h', 't', 'e'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['ä'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 'n'], ['h', 'o', 'u', 'r', '-', 'A', 'C', 'C'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "measure")] }

def ex_27 : Datum :=
  { id := "huumo2020_27"
    source := ⟨"huumo-2020", "(27)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin paljon omenoita tunnissa."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("paljon", "a.lot.of"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-ssa", "hour-INE")]
    glossedWords := [⟨['S', 'ö', '-', 'i', '-', 'n'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['S', 'ö'], ['e', 'a', 't'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['p', 'a', 'l', 'j', 'o', 'n'], ['a', '.', 'l', 'o', 't', '.', 'o', 'f'], [⟨['p', 'a', 'l', 'j', 'o', 'n'], ['a', '.', 'l', 'o', 't', '.', 'o', 'f'], none⟩]⟩, ⟨['o', 'm', 'e', 'n', 'o', '-', 'i', '-', 't', 'a'], ['a', 'p', 'p', 'l', 'e', '-', 'P', 'L', '-', 'P', 'A', 'R'], [⟨['o', 'm', 'e', 'n', 'o'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['P', 'L'], some '-'⟩, ⟨['t', 'a'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 's', 's', 'a'], ['h', 'o', 'u', 'r', '-', 'I', 'N', 'E'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['s', 's', 'a'], ['I', 'N', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "mass"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_27_for : Datum :=
  { id := "huumo2020_27_for"
    source := ⟨"huumo-2020", "(27)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin paljon omenoita tunnin."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("paljon", "a.lot.of"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-n", "hour-ACC")]
    glossedWords := [⟨['S', 'ö', '-', 'i', '-', 'n'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['S', 'ö'], ['e', 'a', 't'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['p', 'a', 'l', 'j', 'o', 'n'], ['a', '.', 'l', 'o', 't', '.', 'o', 'f'], [⟨['p', 'a', 'l', 'j', 'o', 'n'], ['a', '.', 'l', 'o', 't', '.', 'o', 'f'], none⟩]⟩, ⟨['o', 'm', 'e', 'n', 'o', '-', 'i', '-', 't', 'a'], ['a', 'p', 'p', 'l', 'e', '-', 'P', 'L', '-', 'P', 'A', 'R'], [⟨['o', 'm', 'e', 'n', 'o'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['P', 'L'], some '-'⟩, ⟨['t', 'a'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 'n'], ['h', 'o', 'u', 'r', '-', 'A', 'C', 'C'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "mass"), ("case", "part"), ("adverbial", "measure")] }

def ex_28 : Datum :=
  { id := "huumo2020_28"
    source := ⟨"huumo-2020", "(28)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin omenoita tunnin."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-n", "hour-ACC")]
    glossedWords := [⟨['S', 'ö', '-', 'i', '-', 'n'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['S', 'ö'], ['e', 'a', 't'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 'm', 'e', 'n', 'o', '-', 'i', '-', 't', 'a'], ['a', 'p', 'p', 'l', 'e', '-', 'P', 'L', '-', 'P', 'A', 'R'], [⟨['o', 'm', 'e', 'n', 'o'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['P', 'L'], some '-'⟩, ⟨['t', 'a'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 'n'], ['h', 'o', 'u', 'r', '-', 'A', 'C', 'C'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "measure")] }

def ex_28_in : Datum :=
  { id := "huumo2020_28_in"
    source := ⟨"huumo-2020", "(28)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin omenoita tunnissa."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-ssa", "hour-INE")]
    glossedWords := [⟨['S', 'ö', '-', 'i', '-', 'n'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['S', 'ö'], ['e', 'a', 't'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 'm', 'e', 'n', 'o', '-', 'i', '-', 't', 'a'], ['a', 'p', 'p', 'l', 'e', '-', 'P', 'L', '-', 'P', 'A', 'R'], [⟨['o', 'm', 'e', 'n', 'o'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['P', 'L'], some '-'⟩, ⟨['t', 'a'], ['P', 'A', 'R'], some '-'⟩]⟩, ⟨['t', 'u', 'n', 'n', 'i', '-', 's', 's', 'a'], ['h', 'o', 'u', 'r', '-', 'I', 'N', 'E'], [⟨['t', 'u', 'n', 'n', 'i'], ['h', 'o', 'u', 'r'], none⟩, ⟨['s', 's', 'a'], ['I', 'N', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_34 : Datum :=
  { id := "huumo2020_34"
    source := ⟨"huumo-2020", "(34)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin useaa kirjaa päivässä."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("usea-a", "a.number.of-SG.PAR"), ("kirja-a", "book-SG.PAR"), ("päivä-ssä", "day-INE")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['u', 's', 'e', 'a', '-', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f', '-', 'S', 'G', '.', 'P', 'A', 'R'], [⟨['u', 's', 'e', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f'], none⟩, ⟨['a'], ['S', 'G', '.', 'P', 'A', 'R'], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '-', 'a'], ['b', 'o', 'o', 'k', '-', 'S', 'G', '.', 'P', 'A', 'R'], [⟨['k', 'i', 'r', 'j', 'a'], ['b', 'o', 'o', 'k'], none⟩, ⟨['a'], ['S', 'G', '.', 'P', 'A', 'R'], some '-'⟩]⟩, ⟨['p', 'ä', 'i', 'v', 'ä', '-', 's', 's', 'ä'], ['d', 'a', 'y', '-', 'I', 'N', 'E'], [⟨['p', 'ä', 'i', 'v', 'ä'], ['d', 'a', 'y'], none⟩, ⟨['s', 's', 'ä'], ['I', 'N', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_35 : Datum :=
  { id := "huumo2020_35"
    source := ⟨"huumo-2020", "(35)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin useaa kirjaa päivän."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("useaa", "a.number.of-SG.PAR"), ("kirja-a", "book-SG.PAR"), ("päivä-n", "day-ACC")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['u', 's', 'e', 'a', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f', '-', 'S', 'G', '.', 'P', 'A', 'R'], []⟩, ⟨['k', 'i', 'r', 'j', 'a', '-', 'a'], ['b', 'o', 'o', 'k', '-', 'S', 'G', '.', 'P', 'A', 'R'], [⟨['k', 'i', 'r', 'j', 'a'], ['b', 'o', 'o', 'k'], none⟩, ⟨['a'], ['S', 'G', '.', 'P', 'A', 'R'], some '-'⟩]⟩, ⟨['p', 'ä', 'i', 'v', 'ä', '-', 'n'], ['d', 'a', 'y', '-', 'A', 'C', 'C'], [⟨['p', 'ä', 'i', 'v', 'ä'], ['d', 'a', 'y'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "part"), ("adverbial", "measure")] }

def ex_36 : Datum :=
  { id := "huumo2020_36"
    source := ⟨"huumo-2020", "(36)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin usean kirjan päivän."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("usea-n", "a.number.of-SG.ACC"), ("kirja-n", "book-SG.ACC"), ("päivä-n", "day-ACC")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['u', 's', 'e', 'a', '-', 'n'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f', '-', 'S', 'G', '.', 'A', 'C', 'C'], [⟨['u', 's', 'e', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f'], none⟩, ⟨['n'], ['S', 'G', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '-', 'n'], ['b', 'o', 'o', 'k', '-', 'S', 'G', '.', 'A', 'C', 'C'], [⟨['k', 'i', 'r', 'j', 'a'], ['b', 'o', 'o', 'k'], none⟩, ⟨['n'], ['S', 'G', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'ä', 'i', 'v', 'ä', '-', 'n'], ['d', 'a', 'y', '-', 'A', 'C', 'C'], [⟨['p', 'ä', 'i', 'v', 'ä'], ['d', 'a', 'y'], none⟩, ⟨['n'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "acc"), ("adverbial", "measure")] }

def ex_37 : Datum :=
  { id := "huumo2020_37"
    source := ⟨"huumo-2020", "(37)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin usean kirjan päivässä."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("usea-n", "a.number.of-SG.ACC"), ("kirja-n", "book-SG.ACC"), ("päivä-ssä", "day-INE")]
    glossedWords := [⟨['L', 'u', '-', 'i', '-', 'n'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['L', 'u'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T'], some '-'⟩, ⟨['n'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['u', 's', 'e', 'a', '-', 'n'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f', '-', 'S', 'G', '.', 'A', 'C', 'C'], [⟨['u', 's', 'e', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f'], none⟩, ⟨['n'], ['S', 'G', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'r', 'j', 'a', '-', 'n'], ['b', 'o', 'o', 'k', '-', 'S', 'G', '.', 'A', 'C', 'C'], [⟨['k', 'i', 'r', 'j', 'a'], ['b', 'o', 'o', 'k'], none⟩, ⟨['n'], ['S', 'G', '.', 'A', 'C', 'C'], some '-'⟩]⟩, ⟨['p', 'ä', 'i', 'v', 'ä', '-', 's', 's', 'ä'], ['d', 'a', 'y', '-', 'I', 'N', 'E'], [⟨['p', 'ä', 'i', 'v', 'ä'], ['d', 'a', 'y'], none⟩, ⟨['s', 's', 'ä'], ['I', 'N', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "acc"), ("adverbial", "timeFrame")] }

def ex_38 : Datum :=
  { id := "huumo2020_38"
    source := ⟨"huumo-2020", "(38)"⟩
    reportedIn := none
    method := some .corpus
    language := "finn1318"
    primaryText := "selailen päivässä useaa blogia"
    glossedTokens := [("selaile-n", "browse-PRES.1SG"), ("päivä-ssä", "day-INE"), ("usea-a", "a.number.of-SG.PAR"), ("blogi-a", "blog-SG.PAR")]
    glossedWords := [⟨['s', 'e', 'l', 'a', 'i', 'l', 'e', '-', 'n'], ['b', 'r', 'o', 'w', 's', 'e', '-', 'P', 'R', 'E', 'S', '.', '1', 'S', 'G'], [⟨['s', 'e', 'l', 'a', 'i', 'l', 'e'], ['b', 'r', 'o', 'w', 's', 'e'], none⟩, ⟨['n'], ['P', 'R', 'E', 'S', '.', '1', 'S', 'G'], some '-'⟩]⟩, ⟨['p', 'ä', 'i', 'v', 'ä', '-', 's', 's', 'ä'], ['d', 'a', 'y', '-', 'I', 'N', 'E'], [⟨['p', 'ä', 'i', 'v', 'ä'], ['d', 'a', 'y'], none⟩, ⟨['s', 's', 'ä'], ['I', 'N', 'E'], some '-'⟩]⟩, ⟨['u', 's', 'e', 'a', '-', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f', '-', 'S', 'G', '.', 'P', 'A', 'R'], [⟨['u', 's', 'e', 'a'], ['a', '.', 'n', 'u', 'm', 'b', 'e', 'r', '.', 'o', 'f'], none⟩, ⟨['a'], ['S', 'G', '.', 'P', 'A', 'R'], some '-'⟩]⟩, ⟨['b', 'l', 'o', 'g', 'i', '-', 'a'], ['b', 'l', 'o', 'g', '-', 'S', 'G', '.', 'P', 'A', 'R'], [⟨['b', 'l', 'o', 'g', 'i'], ['b', 'l', 'o', 'g'], none⟩, ⟨['a'], ['S', 'G', '.', 'P', 'A', 'R'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "part"), ("adverbial", "timeFrame")] }

def all : List Datum := [ex_17, ex_17_for, ex_18, ex_18_in, ex_19, ex_27, ex_27_for, ex_28, ex_28_in, ex_34, ex_35, ex_36, ex_37, ex_38]

/-- The time adverbial of a clause: a time-frame adverbial in the inessive, 'in an hour', or a temporal measure phrase in the accusative, 'for an hour'. -/
inductive Adverbial where
  /-- timeFrame: timeFrame -/
  | timeFrame
  /-- measure: measure -/
  | measure
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `adverbial`. -/
def adverbial (e : Datum) : Option Adverbial :=
  e.parse? "adverbial" [("timeFrame", .timeFrame), ("measure", .measure)]

/-- The quantifier of an object: none, a mass quantifier such as *paljon* 'a lot of', or a number quantifier such as *usea* 'a number of'. -/
inductive Quantifier where
  /-- none: none -/
  | none
  /-- mass: mass -/
  | mass
  /-- number: number -/
  | number
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `quantifier`. -/
def quantifier (e : Datum) : Option Quantifier :=
  e.parse? "quantifier" [("none", .none), ("mass", .mass), ("number", .number)]

end Huumo2020.Examples
