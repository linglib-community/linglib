module

public import Linglib.Data.Examples.Schema

/-!
# `BobaljikHarley2017` — typed example data

Auto-generated from `Linglib/Data/Examples/BobaljikHarley2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BobaljikHarley2017.Examples`.
-/

@[expose] public section

namespace BobaljikHarley2017.Examples

def ex15a : Datum :=
  { id := "bobaljikharley2017_ex15a"
    source := ⟨"bobaljik-harley-2017", "(15a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "U'u maaso uusi-m yi'i-ria-k"
    glossedTokens := [("U'u", "The"), ("maaso", "deer.dancer"), ("uusi-m", "children-PL"), ("yi'i-ria-k", "dance-APPL-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative"), ("verbClass", "unergative"), ("applicative", "suffixed")] }

def ex15b : Datum :=
  { id := "bobaljikharley2017_ex15b"
    source := ⟨"bobaljik-harley-2017", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Inepo Hose-ta pueta-ta eta-ria-k"
    glossedTokens := [("Inepo", "1SG"), ("Hose-ta", "Jose-ACC"), ("pueta-ta", "door-ACC"), ("eta-ria-k", "close-APPL-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative"), ("verbClass", "transitive"), ("applicative", "suffixed")] }

def ex15c : Datum :=
  { id := "bobaljikharley2017_ex15c"
    source := ⟨"bobaljik-harley-2017", "(15c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Uu tasa Maria-ta hamte-ria-k"
    glossedTokens := [("Uu", "The"), ("tasa", "cup"), ("Maria-ta", "Maria-ACC"), ("hamte-ria-k", "break.INTR-APPL-PRF")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative"), ("verbClass", "unaccusative"), ("applicative", "suffixed")] }

def ex16 : Datum :=
  { id := "bobaljikharley2017_ex16"
    source := ⟨"bobaljik-harley-2017", "(16)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Santos Maria-ta San Xavierle-u weye-ria"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weye-ria", "go.SG-APPL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative"), ("verbClass", "suppletiveIntransitive"), ("applicative", "suffixed")] }

def ex17 : Datum :=
  { id := "bobaljikharley2017_ex17"
    source := ⟨"bobaljik-harley-2017", "(17)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Santos Maria-ta vetchi'ivo San Xavierle-u weeye"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("vetchi'ivo", "for"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weeye", "go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative"), ("verbClass", "suppletiveIntransitive"), ("applicative", "periphrastic")] }

def ex18 : Datum :=
  { id := "bobaljikharley2017_ex18"
    source := ⟨"bobaljik-harley-2017", "(18)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Santos Jose-ta koowi-ta/koowi-m mea/sua-ria-k"
    glossedTokens := [("Santos", "Santos"), ("Jose-ta", "Jose-ACC"), ("koowi-ta/koowi-m", "pig-ACC/pig-PL"), ("mea/sua-ria-k", "kill.SG/kill.PL-APPL-PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative"), ("verbClass", "suppletiveTransitive"), ("applicative", "suffixed")] }

def all : List Datum := [ex15a, ex15b, ex15c, ex16, ex17, ex18]

end BobaljikHarley2017.Examples
