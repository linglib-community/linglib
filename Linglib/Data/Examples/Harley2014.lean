module

public import Linglib.Data.Examples.Schema

/-!
# `Harley2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Harley2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Harley2014.Examples`.
-/

@[expose] public section

namespace Harley2014.Examples

def ex3a : Datum :=
  { id := "harley2014_ex3a"
    source := ⟨"harley-2014", "(3a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "vuite~tenne"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "vuite"), ("pluralForm", "tenne"), ("conditioner", "subject")] }

def ex3b : Datum :=
  { id := "harley2014_ex3b"
    source := ⟨"harley-2014", "(3b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "siika~saka"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "siika"), ("pluralForm", "saka"), ("conditioner", "subject")] }

def ex3c : Datum :=
  { id := "harley2014_ex3c"
    source := ⟨"harley-2014", "(3c)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "weama~rehte"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "weama"), ("pluralForm", "rehte"), ("conditioner", "subject")] }

def ex3d : Datum :=
  { id := "harley2014_ex3d"
    source := ⟨"harley-2014", "(3d)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "kivake~kiime"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "kivake"), ("pluralForm", "kiime"), ("conditioner", "subject")] }

def ex3e : Datum :=
  { id := "harley2014_ex3e"
    source := ⟨"harley-2014", "(3e)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "vo'e~to'e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "vo'e"), ("pluralForm", "to'e"), ("conditioner", "subject")] }

def ex3f : Datum :=
  { id := "harley2014_ex3f"
    source := ⟨"harley-2014", "(3f)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "weye~kaate"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "weye"), ("pluralForm", "kaate"), ("conditioner", "subject")] }

def ex3g : Datum :=
  { id := "harley2014_ex3g"
    source := ⟨"harley-2014", "(3g)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "mea~sua"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("singularForm", "mea"), ("pluralForm", "sua"), ("conditioner", "object")] }

def ex6a : Datum :=
  { id := "harley2014_ex6a"
    source := ⟨"harley-2014", "(6a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo aman vuite-k."
    glossedTokens := [("Aapo", "3sg"), ("aman", "there"), ("vuite-k.", "run.sg-prf")]
    glossedWords := [⟨[['A', 'a', 'p', 'o']], [['3', 's', 'g']]⟩, ⟨[['a', 'm', 'a', 'n']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['v', 'u', 'i', 't', 'e'], ['k']], [['r', 'u', 'n', '.', 's', 'g'], ['p', 'r', 'f']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Vempo aman vuite-k.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "singular")] }

def ex6b : Datum :=
  { id := "harley2014_ex6b"
    source := ⟨"harley-2014", "(6b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Vempo aman tenne-k"
    glossedTokens := [("Vempo", "3pl"), ("aman", "there"), ("tenne-k", "run.pl-prf")]
    glossedWords := [⟨[['V', 'e', 'm', 'p', 'o']], [['3', 'p', 'l']]⟩, ⟨[['a', 'm', 'a', 'n']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['t', 'e', 'n', 'n', 'e'], ['k']], [['r', 'u', 'n', '.', 'p', 'l'], ['p', 'r', 'f']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Aapo aman tenne-k.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "plural")] }

def ex18a : Datum :=
  { id := "harley2014_ex18a"
    source := ⟨"harley-2014", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This student of chemistry and that one of physics sit together"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "oneReplacement"), ("stranded", "argument")] }

def ex18b : Datum :=
  { id := "harley2014_ex18b"
    source := ⟨"harley-2014", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That student with short hair and this one with long hair sit together"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "oneReplacement"), ("stranded", "adjunct")] }

def ex26a : Datum :=
  { id := "harley2014_ex26a"
    source := ⟨"harley-2014", "(26a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo weye"
    glossedTokens := [("Aapo", "3sg"), ("weye", "walk.sg")]
    glossedWords := [⟨[['A', 'a', 'p', 'o']], [['3', 's', 'g']]⟩, ⟨[['w', 'e', 'y', 'e']], [['w', 'a', 'l', 'k', '.', 's', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "singular")] }

def ex26b : Datum :=
  { id := "harley2014_ex26b"
    source := ⟨"harley-2014", "(26b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Vempo kaate"
    glossedTokens := [("Vempo", "3pl"), ("kaate", "walk.pl")]
    glossedWords := [⟨[['V', 'e', 'm', 'p', 'o']], [['3', 'p', 'l']]⟩, ⟨[['k', 'a', 'a', 't', 'e']], [['w', 'a', 'l', 'k', '.', 'p', 'l']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("subjectNumber", "plural")] }

def ex27a : Datum :=
  { id := "harley2014_ex27a"
    source := ⟨"harley-2014", "(27a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo/Vempo uka koowi-ta mea-k"
    glossedTokens := [("Aapo/Vempo", "3sg/3pl"), ("uka", "the.sg"), ("koowi-ta", "pig-ACC.sg"), ("mea-k", "kill.sg-PRF")]
    glossedWords := [⟨[['A', 'a', 'p', 'o', '/', 'V', 'e', 'm', 'p', 'o']], [['3', 's', 'g', '/', '3', 'p', 'l']]⟩, ⟨[['u', 'k', 'a']], [['t', 'h', 'e', '.', 's', 'g']]⟩, ⟨[['k', 'o', 'o', 'w', 'i'], ['t', 'a']], [['p', 'i', 'g'], ['A', 'C', 'C', '.', 's', 'g']]⟩, ⟨[['m', 'e', 'a'], ['k']], [['k', 'i', 'l', 'l', '.', 's', 'g'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("objectNumber", "singular")] }

def ex27b : Datum :=
  { id := "harley2014_ex27b"
    source := ⟨"harley-2014", "(27b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Aapo/Vempo ume kowi-m sua-k"
    glossedTokens := [("Aapo/Vempo", "3sg/3pl"), ("ume", "the.pl"), ("kowi-m", "pig-pl"), ("sua-k", "kill.pl-PRF")]
    glossedWords := [⟨[['A', 'a', 'p', 'o', '/', 'V', 'e', 'm', 'p', 'o']], [['3', 's', 'g', '/', '3', 'p', 'l']]⟩, ⟨[['u', 'm', 'e']], [['t', 'h', 'e', '.', 'p', 'l']]⟩, ⟨[['k', 'o', 'w', 'i'], ['m']], [['p', 'i', 'g'], ['p', 'l']]⟩, ⟨[['s', 'u', 'a'], ['k']], [['k', 'i', 'l', 'l', '.', 'p', 'l'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "rootSuppletion"), ("objectNumber", "plural")] }

def ex29a : Datum :=
  { id := "harley2014_ex29a"
    source := ⟨"harley-2014", "(29a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Hoan Maria-ta vicha-k"
    glossedTokens := [("Hoan", "Juan.nom"), ("Maria-ta", "Maria-acc"), ("vicha-k", "see-prf")]
    glossedWords := [⟨[['H', 'o', 'a', 'n']], [['J', 'u', 'a', 'n', '.', 'n', 'o', 'm']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['a', 'c', 'c']]⟩, ⟨[['v', 'i', 'c', 'h', 'a'], ['k']], [['s', 'e', 'e'], ['p', 'r', 'f']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "case")] }

def ex29b : Datum :=
  { id := "harley2014_ex29b"
    source := ⟨"harley-2014", "(29b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Maria aman vicha-wa-k"
    glossedTokens := [("Maria", "Maria.nom"), ("aman", "there"), ("vicha-wa-k", "see-pass-prf")]
    glossedWords := [⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a', '.', 'n', 'o', 'm']]⟩, ⟨[['a', 'm', 'a', 'n']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['v', 'i', 'c', 'h', 'a'], ['w', 'a'], ['k']], [['s', 'e', 'e'], ['p', 'a', 's', 's'], ['p', 'r', 'f']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "case")] }

def ex30a : Datum :=
  { id := "harley2014_ex30a"
    source := ⟨"harley-2014", "(30a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "U'u maaso uusi-m yi'i-ria-k"
    glossedTokens := [("U'u", "the"), ("maaso", "deer.dancer"), ("uusi-m", "children-pl"), ("yi'i-ria-k", "dance-APPL-PRF")]
    glossedWords := [⟨[['U', '\'', 'u']], [['t', 'h', 'e']]⟩, ⟨[['m', 'a', 'a', 's', 'o']], [['d', 'e', 'e', 'r', '.', 'd', 'a', 'n', 'c', 'e', 'r']]⟩, ⟨[['u', 'u', 's', 'i'], ['m']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], ['p', 'l']]⟩, ⟨[['y', 'i', '\'', 'i'], ['r', 'i', 'a'], ['k']], [['d', 'a', 'n', 'c', 'e'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "unergative"), ("applicative", "suffixed")] }

def ex30b : Datum :=
  { id := "harley2014_ex30b"
    source := ⟨"harley-2014", "(30b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Inepo Hose-ta pueta-ta eta-ria-k"
    glossedTokens := [("Inepo", "1sg"), ("Hose-ta", "Jose-ACC"), ("pueta-ta", "door-ACC"), ("eta-ria-k", "close-APPL-PRF")]
    glossedWords := [⟨[['I', 'n', 'e', 'p', 'o']], [['1', 's', 'g']]⟩, ⟨[['H', 'o', 's', 'e'], ['t', 'a']], [['J', 'o', 's', 'e'], ['A', 'C', 'C']]⟩, ⟨[['p', 'u', 'e', 't', 'a'], ['t', 'a']], [['d', 'o', 'o', 'r'], ['A', 'C', 'C']]⟩, ⟨[['e', 't', 'a'], ['r', 'i', 'a'], ['k']], [['c', 'l', 'o', 's', 'e'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "transitive"), ("applicative", "suffixed")] }

def ex31 : Datum :=
  { id := "harley2014_ex31"
    source := ⟨"harley-2014", "(31)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Uu tasa Maria-ta hamte-ria-k"
    glossedTokens := [("Uu", "the"), ("tasa", "cup.nom"), ("Maria-ta", "Maria-ACC"), ("hamte-ria-k", "break.intr-APPL-PRF")]
    glossedWords := [⟨[['U', 'u']], [['t', 'h', 'e']]⟩, ⟨[['t', 'a', 's', 'a']], [['c', 'u', 'p', '.', 'n', 'o', 'm']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'm', 't', 'e'], ['r', 'i', 'a'], ['k']], [['b', 'r', 'e', 'a', 'k', '.', 'i', 'n', 't', 'r'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "unaccusative"), ("applicative", "suffixed")] }

def ex32a : Datum :=
  { id := "harley2014_ex32a"
    source := ⟨"harley-2014", "(32a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Santos Maria-ta San Xavierle-u weye-ria"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weye-ria", "go-APPL")]
    glossedWords := [⟨[['S', 'a', 'n', 't', 'o', 's']], [['S', 'a', 'n', 't', 'o', 's']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['A', 'C', 'C']]⟩, ⟨[['S', 'a', 'n']], [['S', 'a', 'n']]⟩, ⟨[['X', 'a', 'v', 'i', 'e', 'r', 'l', 'e'], ['u']], [['X', 'a', 'v', 'i', 'e', 'r'], ['t', 'o']]⟩, ⟨[['w', 'e', 'y', 'e'], ['r', 'i', 'a']], [['g', 'o'], ['A', 'P', 'P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "suppletiveIntransitive"), ("applicative", "suffixed")] }

def ex32b : Datum :=
  { id := "harley2014_ex32b"
    source := ⟨"harley-2014", "(32b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Santos Maria-ta vetchi'ivo San Xavierle-u weye"
    glossedTokens := [("Santos", "Santos"), ("Maria-ta", "Maria-ACC"), ("vetchi'ivo", "for"), ("San", "San"), ("Xavierle-u", "Xavier-to"), ("weye", "go")]
    glossedWords := [⟨[['S', 'a', 'n', 't', 'o', 's']], [['S', 'a', 'n', 't', 'o', 's']]⟩, ⟨[['M', 'a', 'r', 'i', 'a'], ['t', 'a']], [['M', 'a', 'r', 'i', 'a'], ['A', 'C', 'C']]⟩, ⟨[['v', 'e', 't', 'c', 'h', 'i', '\'', 'i', 'v', 'o']], [['f', 'o', 'r']]⟩, ⟨[['S', 'a', 'n']], [['S', 'a', 'n']]⟩, ⟨[['X', 'a', 'v', 'i', 'e', 'r', 'l', 'e'], ['u']], [['X', 'a', 'v', 'i', 'e', 'r'], ['t', 'o']]⟩, ⟨[['w', 'e', 'y', 'e']], [['g', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "suppletiveIntransitive"), ("applicative", "periphrastic")] }

def exfn33_i : Datum :=
  { id := "harley2014_exfn33-i"
    source := ⟨"harley-2014", "(fn33-i)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Santos Hose-ta koowi-ta/koowi-m mea/sua-ria-k."
    glossedTokens := [("Santos", "Santos"), ("Hose-ta", "Jose-ACC"), ("koowi-ta/koowi-m", "pig-ACC/pig-PL"), ("mea/sua-ria-k.", "kill.sg/kill.pl-APPL-PRF")]
    glossedWords := [⟨[['S', 'a', 'n', 't', 'o', 's']], [['S', 'a', 'n', 't', 'o', 's']]⟩, ⟨[['H', 'o', 's', 'e'], ['t', 'a']], [['J', 'o', 's', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'o', 'o', 'w', 'i'], ['t', 'a', '/', 'k', 'o', 'o', 'w', 'i'], ['m']], [['p', 'i', 'g'], ['A', 'C', 'C', '/', 'p', 'i', 'g'], ['P', 'L']]⟩, ⟨[['m', 'e', 'a', '/', 's', 'u', 'a'], ['r', 'i', 'a'], ['k']], [['k', 'i', 'l', 'l', '.', 's', 'g', '/', 'k', 'i', 'l', 'l', '.', 'p', 'l'], ['A', 'P', 'P', 'L'], ['P', 'R', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "applicative"), ("verbClass", "suppletiveTransitive"), ("applicative", "suffixed")] }

def all : List Datum := [ex3a, ex3b, ex3c, ex3d, ex3e, ex3f, ex3g, ex6a, ex6b, ex18a, ex18b, ex26a, ex26b, ex27a, ex27b, ex29a, ex29b, ex30a, ex30b, ex31, ex32a, ex32b, exfn33_i]

end Harley2014.Examples
