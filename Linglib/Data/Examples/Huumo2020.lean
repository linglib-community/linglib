module

public import Linglib.Data.Examples.Schema

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
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "acc"), ("adverbial", "timeFrame")] }

def ex_17_for : Datum :=
  { id := "huumo2020_17_for"
    source := ⟨"huumo-2020", "(17)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin lehden tunnin."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("lehde-n", "paper-ACC"), ("tunni-n", "hour-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "acc"), ("adverbial", "measure")] }

def ex_18 : Datum :=
  { id := "huumo2020_18"
    source := ⟨"huumo-2020", "(18)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Katsoin televisiota tunnin."
    glossedTokens := [("Katso-i-n", "watch-PST-1SG"), ("televisio-ta", "television-PAR"), ("tunni-n", "hour-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "measure")] }

def ex_18_in : Datum :=
  { id := "huumo2020_18_in"
    source := ⟨"huumo-2020", "(18)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Katsoin televisiota tunnissa."
    glossedTokens := [("Katso-i-n", "watch-PST-1SG"), ("televisio-ta", "television-PAR"), ("tunni-ssa", "hour-INE")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_19 : Datum :=
  { id := "huumo2020_19"
    source := ⟨"huumo-2020", "(19)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin lehteä tunnin."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("lehte-ä", "paper-PAR"), ("tunni-n", "hour-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "measure")] }

def ex_27 : Datum :=
  { id := "huumo2020_27"
    source := ⟨"huumo-2020", "(27)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin paljon omenoita tunnissa."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("paljon", "a.lot.of"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-ssa", "hour-INE")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "mass"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_27_for : Datum :=
  { id := "huumo2020_27_for"
    source := ⟨"huumo-2020", "(27)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin paljon omenoita tunnin."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("paljon", "a.lot.of"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-n", "hour-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "mass"), ("case", "part"), ("adverbial", "measure")] }

def ex_28 : Datum :=
  { id := "huumo2020_28"
    source := ⟨"huumo-2020", "(28)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin omenoita tunnin."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-n", "hour-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "measure")] }

def ex_28_in : Datum :=
  { id := "huumo2020_28_in"
    source := ⟨"huumo-2020", "(28)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Söin omenoita tunnissa."
    glossedTokens := [("Sö-i-n", "eat-PST-1SG"), ("omeno-i-ta", "apple-PL-PAR"), ("tunni-ssa", "hour-INE")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "none"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_34 : Datum :=
  { id := "huumo2020_34"
    source := ⟨"huumo-2020", "(34)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin useaa kirjaa päivässä."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("usea-a", "a.number.of-SG.PAR"), ("kirja-a", "book-SG.PAR"), ("päivä-ssä", "day-INE")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "part"), ("adverbial", "timeFrame")] }

def ex_35 : Datum :=
  { id := "huumo2020_35"
    source := ⟨"huumo-2020", "(35)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin useaa kirjaa päivän."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("useaa", "a.number.of-SG.PAR"), ("kirja-a", "book-SG.PAR"), ("päivä-n", "day-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "part"), ("adverbial", "measure")] }

def ex_36 : Datum :=
  { id := "huumo2020_36"
    source := ⟨"huumo-2020", "(36)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin usean kirjan päivän."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("usea-n", "a.number.of-SG.ACC"), ("kirja-n", "book-SG.ACC"), ("päivä-n", "day-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "acc"), ("adverbial", "measure")] }

def ex_37 : Datum :=
  { id := "huumo2020_37"
    source := ⟨"huumo-2020", "(37)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Luin usean kirjan päivässä."
    glossedTokens := [("Lu-i-n", "read-PST-1SG"), ("usea-n", "a.number.of-SG.ACC"), ("kirja-n", "book-SG.ACC"), ("päivä-ssä", "day-INE")]
    context := ""
    judgment := .acceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "number"), ("case", "part"), ("adverbial", "timeFrame")] }

def all : List Datum := [ex_17, ex_17_for, ex_18, ex_18_in, ex_19, ex_27, ex_27_for, ex_28, ex_28_in, ex_34, ex_35, ex_36, ex_37, ex_38]

end Huumo2020.Examples
