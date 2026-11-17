module

public import Linglib.Data.Examples.Schema

/-!
# `GoldwaterJohnson2003` — typed example data

Auto-generated from `Linglib/Data/Examples/GoldwaterJohnson2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GoldwaterJohnson2003.Examples`.
-/

@[expose] public section

namespace GoldwaterJohnson2003.Examples

def gj2003_kala : Datum :=
  { id := "gj2003_kala"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "ká.lo.jen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("ká.loi.den", .ungrammatical)]
    readings := []
    paperFeatures := [("stem", "kala"), ("loser", "ká.loi.den"), ("winnerViolations", "11000001011"), ("loserViolations", "12000001101")] }

def gj2003_naapuri : Datum :=
  { id := "gj2003_naapuri"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "náa.pu.ri.en"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("náa.pu.rèi.den", .acceptable)]
    readings := []
    paperFeatures := [("stem", "naapuri"), ("loser", "náa.pu.rèi.den"), ("winnerViolations", "01000100012"), ("loserViolations", "01100000100")] }

def gj2003_ministeri : Datum :=
  { id := "gj2003_ministeri"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "mí.nis.te.ri.en"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("stem", "ministeri"), ("loser", "mí.nis.te.rèi.den"), ("winnerViolations", "12000100013"), ("loserViolations", "12100000101")] }

def gj2003_maailma : Datum :=
  { id := "gj2003_maailma"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "máa.il.mo.jen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("stem", "maailma"), ("loser", "máa.il.mòi.den"), ("winnerViolations", "02000001102"), ("loserViolations", "02001000300")] }

def all : List Datum := [gj2003_kala, gj2003_naapuri, gj2003_ministeri, gj2003_maailma]

end GoldwaterJohnson2003.Examples
