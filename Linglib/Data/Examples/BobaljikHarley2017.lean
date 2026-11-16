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
    glossedWords := [⟨[['U', '\'', 'u']], [['T', 'h', 'e']]⟩, ⟨[['m', 'a', 'a', 's', 'o']], [['d', 'e', 'e', 'r', '.', 'd', 'a', 'n', 'c', 'e', 'r']]⟩, ⟨[['u', 'u', 's', 'i'], ['m']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], ['P', 'L']]⟩, ⟨[['y', 'i', '\'', 'i'], ['r', 'i', 'a'], ['k']], [['d', 'a', 'n', 'c', 'e'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative")] }

def ex15b : Datum :=
  { id := "bobaljikharley2017_ex15b"
    source := ⟨"bobaljik-harley-2017", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Inepo Hose-ta pueta-ta eta-ria-k"
    glossedTokens := [("Inepo", "1SG"), ("Hose-ta", "Jose-ACC"), ("pueta-ta", "door-ACC"), ("eta-ria-k", "close-APPL-PRF")]
    glossedWords := [⟨[['I', 'n', 'e', 'p', 'o']], [['1', 'S', 'G']]⟩, ⟨[['H', 'o', 's', 'e'], ['t', 'a']], [['J', 'o', 's', 'e'], ['A', 'C', 'C']]⟩, ⟨[['p', 'u', 'e', 't', 'a'], ['t', 'a']], [['d', 'o', 'o', 'r'], ['A', 'C', 'C']]⟩, ⟨[['e', 't', 'a'], ['r', 'i', 'a'], ['k']], [['c', 'l', 'o', 's', 'e'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative")] }

def ex15c : Datum :=
  { id := "bobaljikharley2017_ex15c"
    source := ⟨"bobaljik-harley-2017", "(15c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Uu tasa Maria-ta hamte-ria-k"
    glossedTokens := [("Uu", "The"), ("tasa", "cup"), ("Maria-ta", "Maria-ACC"), ("hamte-ria-k", "break.INTR-APPL-PRF")]
    glossedWords := [⟨[['U', 'u']], [['T', 'h', 'e']]⟩, ⟨[['t', 'a', 's', 'a']], [['c', 'u', 'p']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'm', 't', 'e'], ['r', 'i', 'a'], ['k']], [['b', 'r', 'e', 'a', 'k', '.', 'I', 'N', 'T', 'R'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative")] }

def ex16 : Datum :=
  { id := "bobaljikharley2017_ex16"
    source := ⟨"bobaljik-harley-2017", "(16)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Santos Maria-ta San Xavierle-u weye-ria"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weye-ria", "go.SG-APPL")]
    glossedWords := [⟨[['S', 'a', 'n', 't', 'o', 's']], [['S', 'a', 'n', 't', 'o', 's']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['A', 'C', 'C']]⟩, ⟨[['S', 'a', 'n']], [['S', 'a', 'n']]⟩, ⟨[['X', 'a', 'v', 'i', 'e', 'r', 'l', 'e'], ['u']], [['X', 'a', 'v', 'i', 'e', 'r'], ['t', 'o']]⟩, ⟨[['w', 'e', 'y', 'e'], ['r', 'i', 'a']], [['g', 'o', '.', 'S', 'G'], ['A', 'P', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative")] }

def ex17 : Datum :=
  { id := "bobaljikharley2017_ex17"
    source := ⟨"bobaljik-harley-2017", "(17)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Santos Maria-ta vetchi'ivo San Xavierle-u weeye"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("vetchi'ivo", "for"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weeye", "go")]
    glossedWords := [⟨[['S', 'a', 'n', 't', 'o', 's']], [['S', 'a', 'n', 't', 'o', 's']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['A', 'C', 'C']]⟩, ⟨[['v', 'e', 't', 'c', 'h', 'i', '\'', 'i', 'v', 'o']], [['f', 'o', 'r']]⟩, ⟨[['S', 'a', 'n']], [['S', 'a', 'n']]⟩, ⟨[['X', 'a', 'v', 'i', 'e', 'r', 'l', 'e'], ['u']], [['X', 'a', 'v', 'i', 'e', 'r'], ['t', 'o']]⟩, ⟨[['w', 'e', 'e', 'y', 'e']], [['g', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative")] }

def ex18 : Datum :=
  { id := "bobaljikharley2017_ex18"
    source := ⟨"bobaljik-harley-2017", "(18)"⟩
    reportedIn := none
    method := some .elicitation
    language := "yaqu1251"
    primaryText := "Santos Jose-ta koowi-ta/koowi-m mea/sua-ria-k"
    glossedTokens := [("Santos", "Santos"), ("Jose-ta", "Jose-ACC"), ("koowi-ta/koowi-m", "pig-ACC/pig-PL"), ("mea/sua-ria-k", "kill.SG/kill.PL-APPL-PRF")]
    glossedWords := [⟨[['S', 'a', 'n', 't', 'o', 's']], [['S', 'a', 'n', 't', 'o', 's']]⟩, ⟨[['J', 'o', 's', 'e'], ['t', 'a']], [['J', 'o', 's', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'o', 'o', 'w', 'i'], ['t', 'a', '/', 'k', 'o', 'o', 'w', 'i'], ['m']], [['p', 'i', 'g'], ['A', 'C', 'C', '/', 'p', 'i', 'g'], ['P', 'L']]⟩, ⟨[['m', 'e', 'a', '/', 's', 'u', 'a'], ['r', 'i', 'a'], ['k']], [['k', 'i', 'l', 'l', '.', 'S', 'G', '/', 'k', 'i', 'l', 'l', '.', 'P', 'L'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2.1"), ("phenomenon", "applicative")] }

def all : List Datum := [ex15a, ex15b, ex15c, ex16, ex17, ex18]

end BobaljikHarley2017.Examples
