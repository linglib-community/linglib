module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Sorace2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Sorace2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sorace2000.Examples`.
-/

@[expose] public section

namespace Sorace2000.Examples

def ex1a : Datum :=
  { id := "sorace2000_ex1a"
    source := ⟨"sorace-2000", "(1a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Maria è venuta alla festa"
    glossedTokens := [("Maria", "Maria"), ("è", "is"), ("venuta", "come"), ("alla", "to.the"), ("festa", "party")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['v', 'e', 'n', 'u', 't', 'a'], ['c', 'o', 'm', 'e'], [⟨['v', 'e', 'n', 'u', 't', 'a'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['a', 'l', 'l', 'a'], ['t', 'o', '.', 't', 'h', 'e'], [⟨['a', 'l', 'l', 'a'], ['t', 'o', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['f', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], [⟨['f', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "venire"⟩]
    paperFeatures := [] }

def ex1b : Datum :=
  { id := "sorace2000_ex1b"
    source := ⟨"sorace-2000", "(1b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie est arrivée en retard"
    glossedTokens := [("Marie", "Marie"), ("est", "is"), ("arrivée", "arrived"), ("en retard", "late")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['a', 'r', 'r', 'i', 'v', 'é', 'e'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['a', 'r', 'r', 'i', 'v', 'é', 'e'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['e', 'n', ' ', 'r', 'e', 't', 'a', 'r', 'd'], ['l', 'a', 't', 'e'], [⟨['e', 'n', ' ', 'r', 'e', 't', 'a', 'r', 'd'], ['l', 'a', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "être"⟩, ⟨2, 1, "participle", some "arriver"⟩]
    paperFeatures := [] }

def ex1c : Datum :=
  { id := "sorace2000_ex1c"
    source := ⟨"sorace-2000", "(1c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De brief is met de tweede post gekomen"
    glossedTokens := [("De", "the"), ("brief", "letter"), ("is", "is"), ("met", "with"), ("de", "the"), ("tweede", "second"), ("post", "post"), ("gekomen", "arrived")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'r', 'i', 'e', 'f'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['b', 'r', 'i', 'e', 'f'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'e', 't'], ['w', 'i', 't', 'h'], [⟨['m', 'e', 't'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'w', 'e', 'e', 'd', 'e'], ['s', 'e', 'c', 'o', 'n', 'd'], [⟨['t', 'w', 'e', 'e', 'd', 'e'], ['s', 'e', 'c', 'o', 'n', 'd'], none⟩]⟩, ⟨['p', 'o', 's', 't'], ['p', 'o', 's', 't'], [⟨['p', 'o', 's', 't'], ['p', 'o', 's', 't'], none⟩]⟩, ⟨['g', 'e', 'k', 'o', 'm', 'e', 'n'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['g', 'e', 'k', 'o', 'm', 'e', 'n'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "zijn"⟩, ⟨7, 1, "participle", some "komen"⟩]
    paperFeatures := [] }

def ex1d : Datum :=
  { id := "sorace2000_ex1d"
    source := ⟨"sorace-2000", "(1d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Zug ist spät angekommen"
    glossedTokens := [("Der", "the"), ("Zug", "train"), ("ist", "is"), ("spät", "late"), ("angekommen", "arrived")]
    glossedWords := [⟨['D', 'e', 'r'], ['t', 'h', 'e'], [⟨['D', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Z', 'u', 'g'], ['t', 'r', 'a', 'i', 'n'], [⟨['Z', 'u', 'g'], ['t', 'r', 'a', 'i', 'n'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['s', 'p', 'ä', 't'], ['l', 'a', 't', 'e'], [⟨['s', 'p', 'ä', 't'], ['l', 'a', 't', 'e'], none⟩]⟩, ⟨['a', 'n', 'g', 'e', 'k', 'o', 'm', 'm', 'e', 'n'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['a', 'n', 'g', 'e', 'k', 'o', 'm', 'm', 'e', 'n'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "sein"⟩, ⟨4, 1, "participle", some "ankommen"⟩]
    paperFeatures := [] }

def ex4 : Datum :=
  { id := "sorace2000_ex4"
    source := ⟨"sorace-2000", "(4)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Sono arrivati ospiti per ore e ore"
    glossedTokens := [("Sono", "are"), ("arrivati", "arrived"), ("ospiti", "guests"), ("per", "for"), ("ore", "hours"), ("e", "and"), ("ore", "hours")]
    glossedWords := [⟨['S', 'o', 'n', 'o'], ['a', 'r', 'e'], [⟨['S', 'o', 'n', 'o'], ['a', 'r', 'e'], none⟩]⟩, ⟨['a', 'r', 'r', 'i', 'v', 'a', 't', 'i'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['a', 'r', 'r', 'i', 'v', 'a', 't', 'i'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['o', 's', 'p', 'i', 't', 'i'], ['g', 'u', 'e', 's', 't', 's'], [⟨['o', 's', 'p', 'i', 't', 'i'], ['g', 'u', 'e', 's', 't', 's'], none⟩]⟩, ⟨['p', 'e', 'r'], ['f', 'o', 'r'], [⟨['p', 'e', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['o', 'r', 'e'], ['h', 'o', 'u', 'r', 's'], [⟨['o', 'r', 'e'], ['h', 'o', 'u', 'r', 's'], none⟩]⟩, ⟨['e'], ['a', 'n', 'd'], [⟨['e'], ['a', 'n', 'd'], none⟩]⟩, ⟨['o', 'r', 'e'], ['h', 'o', 'u', 'r', 's'], [⟨['o', 'r', 'e'], ['h', 'o', 'u', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "auxiliary", some "essere"⟩, ⟨1, 1, "participle", some "arrivare"⟩]
    paperFeatures := [("predicate", "detelicized")] }

def ex5a : Datum :=
  { id := "sorace2000_ex5a"
    source := ⟨"sorace-2000", "(5a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Maria è caduta apposta per farci spaventare"
    glossedTokens := [("Maria", "Maria"), ("è", "is"), ("caduta", "fallen"), ("apposta", "on.purpose"), ("per", "to"), ("farci", "make-us"), ("spaventare", "scare")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['c', 'a', 'd', 'u', 't', 'a'], ['f', 'a', 'l', 'l', 'e', 'n'], [⟨['c', 'a', 'd', 'u', 't', 'a'], ['f', 'a', 'l', 'l', 'e', 'n'], none⟩]⟩, ⟨['a', 'p', 'p', 'o', 's', 't', 'a'], ['o', 'n', '.', 'p', 'u', 'r', 'p', 'o', 's', 'e'], [⟨['a', 'p', 'p', 'o', 's', 't', 'a'], ['o', 'n', '.', 'p', 'u', 'r', 'p', 'o', 's', 'e'], none⟩]⟩, ⟨['p', 'e', 'r'], ['t', 'o'], [⟨['p', 'e', 'r'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'c', 'i'], ['m', 'a', 'k', 'e', '-', 'u', 's'], []⟩, ⟨['s', 'p', 'a', 'v', 'e', 'n', 't', 'a', 'r', 'e'], ['s', 'c', 'a', 'r', 'e'], [⟨['s', 'p', 'a', 'v', 'e', 'n', 't', 'a', 'r', 'e'], ['s', 'c', 'a', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "cadere"⟩]
    paperFeatures := [("subject", "agentive")] }

def ex5b : Datum :=
  { id := "sorace2000_ex5b"
    source := ⟨"sorace-2000", "(5b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il bicchiere è caduto dal tavolo"
    glossedTokens := [("Il", "the"), ("bicchiere", "glass"), ("è", "is"), ("caduto", "fallen"), ("dal", "from.the"), ("tavolo", "table")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'i', 'c', 'c', 'h', 'i', 'e', 'r', 'e'], ['g', 'l', 'a', 's', 's'], [⟨['b', 'i', 'c', 'c', 'h', 'i', 'e', 'r', 'e'], ['g', 'l', 'a', 's', 's'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['c', 'a', 'd', 'u', 't', 'o'], ['f', 'a', 'l', 'l', 'e', 'n'], [⟨['c', 'a', 'd', 'u', 't', 'o'], ['f', 'a', 'l', 'l', 'e', 'n'], none⟩]⟩, ⟨['d', 'a', 'l'], ['f', 'r', 'o', 'm', '.', 't', 'h', 'e'], [⟨['d', 'a', 'l'], ['f', 'r', 'o', 'm', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'v', 'o', 'l', 'o'], ['t', 'a', 'b', 'l', 'e'], [⟨['t', 'a', 'v', 'o', 'l', 'o'], ['t', 'a', 'b', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "cadere"⟩]
    paperFeatures := [] }

def ex30a : Datum :=
  { id := "sorace2000_ex30a"
    source := ⟨"sorace-2000", "(30a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "I bambini hanno arrivato."
    glossedTokens := [("I", "the"), ("bambini", "children"), ("hanno", "have"), ("arrivato", "arrived")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'm', 'b', 'i', 'n', 'i'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['b', 'a', 'm', 'b', 'i', 'n', 'i'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['a', 'r', 'r', 'i', 'v', 'a', 't', 'o'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], [⟨['a', 'r', 'r', 'i', 'v', 'a', 't', 'o'], ['a', 'r', 'r', 'i', 'v', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "arrivare"⟩]
    paperFeatures := [] }

def ex7a : Datum :=
  { id := "sorace2000_ex7a"
    source := ⟨"sorace-2000", "(7a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La temperatura è salita improvvisamente"
    glossedTokens := [("La", "the"), ("temperatura", "temperature"), ("è", "is"), ("salita", "risen"), ("improvvisamente", "suddenly")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'r', 'a'], ['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'r', 'e'], [⟨['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'r', 'a'], ['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'r', 'e'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['s', 'a', 'l', 'i', 't', 'a'], ['r', 'i', 's', 'e', 'n'], [⟨['s', 'a', 'l', 'i', 't', 'a'], ['r', 'i', 's', 'e', 'n'], none⟩]⟩, ⟨['i', 'm', 'p', 'r', 'o', 'v', 'v', 'i', 's', 'a', 'm', 'e', 'n', 't', 'e'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], [⟨['i', 'm', 'p', 'r', 'o', 'v', 'v', 'i', 's', 'a', 'm', 'e', 'n', 't', 'e'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La temperatura ha salito improvvisamente", .nearlyUngrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "salire"⟩]
    paperFeatures := [] }

def ex7b : Datum :=
  { id := "sorace2000_ex7b"
    source := ⟨"sorace-2000", "(7b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Le mele sono marcite al sole"
    glossedTokens := [("Le", "the"), ("mele", "apples"), ("sono", "are"), ("marcite", "rotted"), ("al", "in.the"), ("sole", "sun")]
    glossedWords := [⟨['L', 'e'], ['t', 'h', 'e'], [⟨['L', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'e', 'l', 'e'], ['a', 'p', 'p', 'l', 'e', 's'], [⟨['m', 'e', 'l', 'e'], ['a', 'p', 'p', 'l', 'e', 's'], none⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], [⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], none⟩]⟩, ⟨['m', 'a', 'r', 'c', 'i', 't', 'e'], ['r', 'o', 't', 't', 'e', 'd'], [⟨['m', 'a', 'r', 'c', 'i', 't', 'e'], ['r', 'o', 't', 't', 'e', 'd'], none⟩]⟩, ⟨['a', 'l'], ['i', 'n', '.', 't', 'h', 'e'], [⟨['a', 'l'], ['i', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['s', 'o', 'l', 'e'], ['s', 'u', 'n'], [⟨['s', 'o', 'l', 'e'], ['s', 'u', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Le mele hanno marcito al sole", .marginal)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "marcire"⟩]
    paperFeatures := [] }

def ex8a : Datum :=
  { id := "sorace2000_ex8a"
    source := ⟨"sorace-2000", "(8a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La pianta è fiorita due volte quest'anno"
    glossedTokens := [("La", "the"), ("pianta", "plant"), ("è", "is"), ("fiorita", "blossomed"), ("due volte", "twice"), ("quest'anno", "this.year")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'i', 'a', 'n', 't', 'a'], ['p', 'l', 'a', 'n', 't'], [⟨['p', 'i', 'a', 'n', 't', 'a'], ['p', 'l', 'a', 'n', 't'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['f', 'i', 'o', 'r', 'i', 't', 'a'], ['b', 'l', 'o', 's', 's', 'o', 'm', 'e', 'd'], [⟨['f', 'i', 'o', 'r', 'i', 't', 'a'], ['b', 'l', 'o', 's', 's', 'o', 'm', 'e', 'd'], none⟩]⟩, ⟨['d', 'u', 'e', ' ', 'v', 'o', 'l', 't', 'e'], ['t', 'w', 'i', 'c', 'e'], [⟨['d', 'u', 'e', ' ', 'v', 'o', 'l', 't', 'e'], ['t', 'w', 'i', 'c', 'e'], none⟩]⟩, ⟨['q', 'u', 'e', 's', 't', '\'', 'a', 'n', 'n', 'o'], ['t', 'h', 'i', 's', '.', 'y', 'e', 'a', 'r'], [⟨['q', 'u', 'e', 's', 't', '\'', 'a', 'n', 'n', 'o'], ['t', 'h', 'i', 's', '.', 'y', 'e', 'a', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La pianta ha fiorito due volte quest'anno", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "fiorire"⟩]
    paperFeatures := [] }

def ex9a : Datum :=
  { id := "sorace2000_ex9a"
    source := ⟨"sorace-2000", "(9a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ma fille est née à cinq heures du matin"
    glossedTokens := [("Ma", "my"), ("fille", "daughter"), ("est", "is"), ("née", "born"), ("à", "at"), ("cinq", "five"), ("heures", "hours"), ("du", "of"), ("matin", "morning")]
    glossedWords := [⟨['M', 'a'], ['m', 'y'], [⟨['M', 'a'], ['m', 'y'], none⟩]⟩, ⟨['f', 'i', 'l', 'l', 'e'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], [⟨['f', 'i', 'l', 'l', 'e'], ['d', 'a', 'u', 'g', 'h', 't', 'e', 'r'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['n', 'é', 'e'], ['b', 'o', 'r', 'n'], [⟨['n', 'é', 'e'], ['b', 'o', 'r', 'n'], none⟩]⟩, ⟨['à'], ['a', 't'], [⟨['à'], ['a', 't'], none⟩]⟩, ⟨['c', 'i', 'n', 'q'], ['f', 'i', 'v', 'e'], [⟨['c', 'i', 'n', 'q'], ['f', 'i', 'v', 'e'], none⟩]⟩, ⟨['h', 'e', 'u', 'r', 'e', 's'], ['h', 'o', 'u', 'r', 's'], [⟨['h', 'e', 'u', 'r', 'e', 's'], ['h', 'o', 'u', 'r', 's'], none⟩]⟩, ⟨['d', 'u'], ['o', 'f'], [⟨['d', 'u'], ['o', 'f'], none⟩]⟩, ⟨['m', 'a', 't', 'i', 'n'], ['m', 'o', 'r', 'n', 'i', 'n', 'g'], [⟨['m', 'a', 't', 'i', 'n'], ['m', 'o', 'r', 'n', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "être"⟩, ⟨3, 1, "participle", some "naître"⟩]
    paperFeatures := [] }

def ex9b : Datum :=
  { id := "sorace2000_ex9b"
    source := ⟨"sorace-2000", "(9b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De leraar is plotseling gestorven"
    glossedTokens := [("De", "the"), ("leraar", "teacher"), ("is", "is"), ("plotseling", "suddenly"), ("gestorven", "died")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 'r', 'a', 'a', 'r'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['l', 'e', 'r', 'a', 'a', 'r'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['p', 'l', 'o', 't', 's', 'e', 'l', 'i', 'n', 'g'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], [⟨['p', 'l', 'o', 't', 's', 'e', 'l', 'i', 'n', 'g'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], none⟩]⟩, ⟨['g', 'e', 's', 't', 'o', 'r', 'v', 'e', 'n'], ['d', 'i', 'e', 'd'], [⟨['g', 'e', 's', 't', 'o', 'r', 'v', 'e', 'n'], ['d', 'i', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "zijn"⟩, ⟨4, 1, "participle", some "sterven"⟩]
    paperFeatures := [] }

def ex9c : Datum :=
  { id := "sorace2000_ex9c"
    source := ⟨"sorace-2000", "(9c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Zwillinge sind im April geboren"
    glossedTokens := [("Die", "the"), ("Zwillinge", "twins"), ("sind", "are"), ("im", "in"), ("April", "April"), ("geboren", "born")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Z', 'w', 'i', 'l', 'l', 'i', 'n', 'g', 'e'], ['t', 'w', 'i', 'n', 's'], [⟨['Z', 'w', 'i', 'l', 'l', 'i', 'n', 'g', 'e'], ['t', 'w', 'i', 'n', 's'], none⟩]⟩, ⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], [⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], none⟩]⟩, ⟨['i', 'm'], ['i', 'n'], [⟨['i', 'm'], ['i', 'n'], none⟩]⟩, ⟨['A', 'p', 'r', 'i', 'l'], ['A', 'p', 'r', 'i', 'l'], [⟨['A', 'p', 'r', 'i', 'l'], ['A', 'p', 'r', 'i', 'l'], none⟩]⟩, ⟨['g', 'e', 'b', 'o', 'r', 'e', 'n'], ['b', 'o', 'r', 'n'], [⟨['g', 'e', 'b', 'o', 'r', 'e', 'n'], ['b', 'o', 'r', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "sein"⟩, ⟨5, 1, "participle", some "gebären"⟩]
    paperFeatures := [] }

def ex10a : Datum :=
  { id := "sorace2000_ex10a"
    source := ⟨"sorace-2000", "(10a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Haar baby is deze maand enorm gegroeid"
    glossedTokens := [("Haar", "her"), ("baby", "baby"), ("is", "is"), ("deze", "this"), ("maand", "month"), ("enorm", "enormous"), ("gegroeid", "grown")]
    glossedWords := [⟨['H', 'a', 'a', 'r'], ['h', 'e', 'r'], [⟨['H', 'a', 'a', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['b', 'a', 'b', 'y'], ['b', 'a', 'b', 'y'], [⟨['b', 'a', 'b', 'y'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'z', 'e'], ['t', 'h', 'i', 's'], [⟨['d', 'e', 'z', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['m', 'a', 'a', 'n', 'd'], ['m', 'o', 'n', 't', 'h'], [⟨['m', 'a', 'a', 'n', 'd'], ['m', 'o', 'n', 't', 'h'], none⟩]⟩, ⟨['e', 'n', 'o', 'r', 'm'], ['e', 'n', 'o', 'r', 'm', 'o', 'u', 's'], [⟨['e', 'n', 'o', 'r', 'm'], ['e', 'n', 'o', 'r', 'm', 'o', 'u', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'r', 'o', 'e', 'i', 'd'], ['g', 'r', 'o', 'w', 'n'], [⟨['g', 'e', 'g', 'r', 'o', 'e', 'i', 'd'], ['g', 'r', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Haar baby heeft deze maand enorm gegroeid", .ungrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "zijn"⟩, ⟨6, 1, "participle", some "groeien"⟩]
    paperFeatures := [] }

def ex10b : Datum :=
  { id := "sorace2000_ex10b"
    source := ⟨"sorace-2000", "(10b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Rauch ist in die Höhe gestiegen"
    glossedTokens := [("Der", "the"), ("Rauch", "smoke"), ("ist", "is"), ("in", "in"), ("die", "the"), ("Höhe", "height"), ("gestiegen", "risen")]
    glossedWords := [⟨['D', 'e', 'r'], ['t', 'h', 'e'], [⟨['D', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['R', 'a', 'u', 'c', 'h'], ['s', 'm', 'o', 'k', 'e'], [⟨['R', 'a', 'u', 'c', 'h'], ['s', 'm', 'o', 'k', 'e'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'e'], [⟨['d', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['H', 'ö', 'h', 'e'], ['h', 'e', 'i', 'g', 'h', 't'], [⟨['H', 'ö', 'h', 'e'], ['h', 'e', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['g', 'e', 's', 't', 'i', 'e', 'g', 'e', 'n'], ['r', 'i', 's', 'e', 'n'], [⟨['g', 'e', 's', 't', 'i', 'e', 'g', 'e', 'n'], ['r', 'i', 's', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "sein"⟩, ⟨6, 1, "participle", some "steigen"⟩]
    paperFeatures := [] }

def ex11 : Datum :=
  { id := "sorace2000_ex11"
    source := ⟨"van-hout-1993", "p. 7"⟩
    reportedIn := some ⟨"sorace-2000", "(11)"⟩
    language := "dutc1256"
    primaryText := "De temperatuur is 3 uurlang gestegen, maar is toen weer gezakt."
    glossedTokens := [("De", "the"), ("temperatuur", "temperature"), ("is", "is"), ("3", "3"), ("uurlang", "hours"), ("gestegen", "risen"), ("maar", "but"), ("is", "is"), ("toen", "then"), ("weer", "again"), ("gezakt", "dropped")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'u', 'r'], ['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'r', 'e'], [⟨['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'u', 'r'], ['t', 'e', 'm', 'p', 'e', 'r', 'a', 't', 'u', 'r', 'e'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['3'], ['3'], [⟨['3'], ['3'], none⟩]⟩, ⟨['u', 'u', 'r', 'l', 'a', 'n', 'g'], ['h', 'o', 'u', 'r', 's'], [⟨['u', 'u', 'r', 'l', 'a', 'n', 'g'], ['h', 'o', 'u', 'r', 's'], none⟩]⟩, ⟨['g', 'e', 's', 't', 'e', 'g', 'e', 'n'], ['r', 'i', 's', 'e', 'n'], [⟨['g', 'e', 's', 't', 'e', 'g', 'e', 'n'], ['r', 'i', 's', 'e', 'n'], none⟩]⟩, ⟨['m', 'a', 'a', 'r'], ['b', 'u', 't'], [⟨['m', 'a', 'a', 'r'], ['b', 'u', 't'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['t', 'o', 'e', 'n'], ['t', 'h', 'e', 'n'], [⟨['t', 'o', 'e', 'n'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['w', 'e', 'e', 'r'], ['a', 'g', 'a', 'i', 'n'], [⟨['w', 'e', 'e', 'r'], ['a', 'g', 'a', 'i', 'n'], none⟩]⟩, ⟨['g', 'e', 'z', 'a', 'k', 't'], ['d', 'r', 'o', 'p', 'p', 'e', 'd'], [⟨['g', 'e', 'z', 'a', 'k', 't'], ['d', 'r', 'o', 'p', 'p', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("De temperatuur heeft 3 uurlang gestegen, maar is toen weer gezakt.", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "zijn"⟩, ⟨5, 1, "participle", some "stijgen"⟩]
    paperFeatures := [("predicate", "detelicized")] }

def ex12 : Datum :=
  { id := "sorace2000_ex12"
    source := ⟨"sorace-2000", "(12)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "L'enfant est devenu triste"
    glossedTokens := [("L'enfant", "the.child"), ("est", "is"), ("devenu", "become"), ("triste", "sad")]
    glossedWords := [⟨['L', '\'', 'e', 'n', 'f', 'a', 'n', 't'], ['t', 'h', 'e', '.', 'c', 'h', 'i', 'l', 'd'], [⟨['L', '\'', 'e', 'n', 'f', 'a', 'n', 't'], ['t', 'h', 'e', '.', 'c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'v', 'e', 'n', 'u'], ['b', 'e', 'c', 'o', 'm', 'e'], [⟨['d', 'e', 'v', 'e', 'n', 'u'], ['b', 'e', 'c', 'o', 'm', 'e'], none⟩]⟩, ⟨['t', 'r', 'i', 's', 't', 'e'], ['s', 'a', 'd'], [⟨['t', 'r', 'i', 's', 't', 'e'], ['s', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("L'enfant a devenu triste", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "être"⟩, ⟨2, 1, "participle", some "devenir"⟩]
    paperFeatures := [] }

def ex13 : Datum :=
  { id := "sorace2000_ex13"
    source := ⟨"sorace-2000", "(13)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie a rougi de honte"
    glossedTokens := [("Marie", "Marie"), ("a", "has"), ("rougi", "blushed"), ("de", "of"), ("honte", "shame")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['a'], ['h', 'a', 's'], [⟨['a'], ['h', 'a', 's'], none⟩]⟩, ⟨['r', 'o', 'u', 'g', 'i'], ['b', 'l', 'u', 's', 'h', 'e', 'd'], [⟨['r', 'o', 'u', 'g', 'i'], ['b', 'l', 'u', 's', 'h', 'e', 'd'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['h', 'o', 'n', 't', 'e'], ['s', 'h', 'a', 'm', 'e'], [⟨['h', 'o', 'n', 't', 'e'], ['s', 'h', 'a', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avoir"⟩, ⟨2, 1, "participle", some "rougir"⟩]
    paperFeatures := [] }

def ex14a : Datum :=
  { id := "sorace2000_ex14a"
    source := ⟨"sorace-2000", "(14a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le livre est paru récemment"
    glossedTokens := [("Le", "the"), ("livre", "book"), ("est", "is"), ("paru", "appeared"), ("récemment", "recently")]
    glossedWords := [⟨['L', 'e'], ['t', 'h', 'e'], [⟨['L', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'i', 'v', 'r', 'e'], ['b', 'o', 'o', 'k'], [⟨['l', 'i', 'v', 'r', 'e'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['p', 'a', 'r', 'u'], ['a', 'p', 'p', 'e', 'a', 'r', 'e', 'd'], [⟨['p', 'a', 'r', 'u'], ['a', 'p', 'p', 'e', 'a', 'r', 'e', 'd'], none⟩]⟩, ⟨['r', 'é', 'c', 'e', 'm', 'm', 'e', 'n', 't'], ['r', 'e', 'c', 'e', 'n', 't', 'l', 'y'], [⟨['r', 'é', 'c', 'e', 'm', 'm', 'e', 'n', 't'], ['r', 'e', 'c', 'e', 'n', 't', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Le livre a paru récemment", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "être"⟩, ⟨3, 1, "participle", some "paraître"⟩]
    paperFeatures := [] }

def ex14c : Datum :=
  { id := "sorace2000_ex14c"
    source := ⟨"sorace-2000", "(14c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Son secret lui est échappé"
    glossedTokens := [("Son", "his"), ("secret", "secret"), ("lui", "to-him"), ("est", "is"), ("échappé", "escaped")]
    glossedWords := [⟨['S', 'o', 'n'], ['h', 'i', 's'], [⟨['S', 'o', 'n'], ['h', 'i', 's'], none⟩]⟩, ⟨['s', 'e', 'c', 'r', 'e', 't'], ['s', 'e', 'c', 'r', 'e', 't'], [⟨['s', 'e', 'c', 'r', 'e', 't'], ['s', 'e', 'c', 'r', 'e', 't'], none⟩]⟩, ⟨['l', 'u', 'i'], ['t', 'o', '-', 'h', 'i', 'm'], []⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['é', 'c', 'h', 'a', 'p', 'p', 'é'], ['e', 's', 'c', 'a', 'p', 'e', 'd'], [⟨['é', 'c', 'h', 'a', 'p', 'p', 'é'], ['e', 's', 'c', 'a', 'p', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "auxiliary", some "être"⟩, ⟨4, 1, "participle", some "échapper"⟩]
    paperFeatures := [] }

def ex15a : Datum :=
  { id := "sorace2000_ex15a"
    source := ⟨"sorace-2000", "(15a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ancora una volta sono rimasto solo"
    glossedTokens := [("Ancora", "again"), ("una", "one"), ("volta", "time"), ("sono", "am"), ("rimasto", "remained"), ("solo", "alone")]
    glossedWords := [⟨['A', 'n', 'c', 'o', 'r', 'a'], ['a', 'g', 'a', 'i', 'n'], [⟨['A', 'n', 'c', 'o', 'r', 'a'], ['a', 'g', 'a', 'i', 'n'], none⟩]⟩, ⟨['u', 'n', 'a'], ['o', 'n', 'e'], [⟨['u', 'n', 'a'], ['o', 'n', 'e'], none⟩]⟩, ⟨['v', 'o', 'l', 't', 'a'], ['t', 'i', 'm', 'e'], [⟨['v', 'o', 'l', 't', 'a'], ['t', 'i', 'm', 'e'], none⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['a', 'm'], [⟨['s', 'o', 'n', 'o'], ['a', 'm'], none⟩]⟩, ⟨['r', 'i', 'm', 'a', 's', 't', 'o'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], [⟨['r', 'i', 'm', 'a', 's', 't', 'o'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩, ⟨['s', 'o', 'l', 'o'], ['a', 'l', 'o', 'n', 'e'], [⟨['s', 'o', 'l', 'o'], ['a', 'l', 'o', 'n', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ancora una volta ho rimasto solo", .marginal)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "essere"⟩, ⟨4, 1, "participle", some "rimanere"⟩]
    paperFeatures := [] }

def ex15b : Datum :=
  { id := "sorace2000_ex15b"
    source := ⟨"sorace-2000", "(15b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La guerra è durata a lungo"
    glossedTokens := [("La", "the"), ("guerra", "war"), ("è", "is"), ("durata", "lasted"), ("a", "for"), ("lungo", "long")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'u', 'e', 'r', 'r', 'a'], ['w', 'a', 'r'], [⟨['g', 'u', 'e', 'r', 'r', 'a'], ['w', 'a', 'r'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['d', 'u', 'r', 'a', 't', 'a'], ['l', 'a', 's', 't', 'e', 'd'], [⟨['d', 'u', 'r', 'a', 't', 'a'], ['l', 'a', 's', 't', 'e', 'd'], none⟩]⟩, ⟨['a'], ['f', 'o', 'r'], [⟨['a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['l', 'u', 'n', 'g', 'o'], ['l', 'o', 'n', 'g'], [⟨['l', 'u', 'n', 'g', 'o'], ['l', 'o', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La guerra ha durato a lungo", .marginal)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "durare"⟩]
    paperFeatures := [] }

def ex15c : Datum :=
  { id := "sorace2000_ex15c"
    source := ⟨"sorace-2000", "(15c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il presidente è durato in carica due anni"
    glossedTokens := [("Il", "the"), ("presidente", "president"), ("è", "is"), ("durato", "lasted"), ("in", "in"), ("carica", "post"), ("due", "two"), ("anni", "years")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't', 'e'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't', 'e'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['d', 'u', 'r', 'a', 't', 'o'], ['l', 'a', 's', 't', 'e', 'd'], [⟨['d', 'u', 'r', 'a', 't', 'o'], ['l', 'a', 's', 't', 'e', 'd'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['c', 'a', 'r', 'i', 'c', 'a'], ['p', 'o', 's', 't'], [⟨['c', 'a', 'r', 'i', 'c', 'a'], ['p', 'o', 's', 't'], none⟩]⟩, ⟨['d', 'u', 'e'], ['t', 'w', 'o'], [⟨['d', 'u', 'e'], ['t', 'w', 'o'], none⟩]⟩, ⟨['a', 'n', 'n', 'i'], ['y', 'e', 'a', 'r', 's'], [⟨['a', 'n', 'n', 'i'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il presidente ha durato in carica due anni", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "durare"⟩]
    paperFeatures := [("subject", "agentive")] }

def ex16 : Datum :=
  { id := "sorace2000_ex16"
    source := ⟨"sorace-2000", "(16)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mes parents ont survécu au tremblement de terre"
    glossedTokens := [("Mes", "my"), ("parents", "parents"), ("ont", "have"), ("survécu", "survived"), ("au", "to.the"), ("tremblement de terre", "earthquake")]
    glossedWords := [⟨['M', 'e', 's'], ['m', 'y'], [⟨['M', 'e', 's'], ['m', 'y'], none⟩]⟩, ⟨['p', 'a', 'r', 'e', 'n', 't', 's'], ['p', 'a', 'r', 'e', 'n', 't', 's'], [⟨['p', 'a', 'r', 'e', 'n', 't', 's'], ['p', 'a', 'r', 'e', 'n', 't', 's'], none⟩]⟩, ⟨['o', 'n', 't'], ['h', 'a', 'v', 'e'], [⟨['o', 'n', 't'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['s', 'u', 'r', 'v', 'é', 'c', 'u'], ['s', 'u', 'r', 'v', 'i', 'v', 'e', 'd'], [⟨['s', 'u', 'r', 'v', 'é', 'c', 'u'], ['s', 'u', 'r', 'v', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['a', 'u'], ['t', 'o', '.', 't', 'h', 'e'], [⟨['a', 'u'], ['t', 'o', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['t', 'r', 'e', 'm', 'b', 'l', 'e', 'm', 'e', 'n', 't', ' ', 'd', 'e', ' ', 't', 'e', 'r', 'r', 'e'], ['e', 'a', 'r', 't', 'h', 'q', 'u', 'a', 'k', 'e'], [⟨['t', 'r', 'e', 'm', 'b', 'l', 'e', 'm', 'e', 'n', 't', ' ', 'd', 'e', ' ', 't', 'e', 'r', 'r', 'e'], ['e', 'a', 'r', 't', 'h', 'q', 'u', 'a', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Mes parents sont survécus au tremblement de terre", .ungrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avoir"⟩, ⟨3, 1, "participle", some "survivre"⟩]
    paperFeatures := [] }

def ex17a : Datum :=
  { id := "sorace2000_ex17a"
    source := ⟨"sorace-2000", "(17a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Äpfel haben den ganzen Winter gehalten"
    glossedTokens := [("Die", "the"), ("Äpfel", "apples"), ("haben", "have"), ("den", "the"), ("ganzen", "whole"), ("Winter", "winter"), ("gehalten", "lasted")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['Ä', 'p', 'f', 'e', 'l'], ['a', 'p', 'p', 'l', 'e', 's'], [⟨['Ä', 'p', 'f', 'e', 'l'], ['a', 'p', 'p', 'l', 'e', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], [⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['W', 'i', 'n', 't', 'e', 'r'], ['w', 'i', 'n', 't', 'e', 'r'], [⟨['W', 'i', 'n', 't', 'e', 'r'], ['w', 'i', 'n', 't', 'e', 'r'], none⟩]⟩, ⟨['g', 'e', 'h', 'a', 'l', 't', 'e', 'n'], ['l', 'a', 's', 't', 'e', 'd'], [⟨['g', 'e', 'h', 'a', 'l', 't', 'e', 'n'], ['l', 'a', 's', 't', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Die Äpfel sind den ganzen Winter gehalten", .nearlyUngrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "haben"⟩, ⟨6, 1, "participle", some "halten"⟩]
    paperFeatures := [] }

def ex17b : Datum :=
  { id := "sorace2000_ex17b"
    source := ⟨"sorace-2000", "(17b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Wanderer hat kurz verweilt"
    glossedTokens := [("Der", "the"), ("Wanderer", "hiker"), ("hat", "has"), ("kurz", "briefly"), ("verweilt", "stayed")]
    glossedWords := [⟨['D', 'e', 'r'], ['t', 'h', 'e'], [⟨['D', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['W', 'a', 'n', 'd', 'e', 'r', 'e', 'r'], ['h', 'i', 'k', 'e', 'r'], [⟨['W', 'a', 'n', 'd', 'e', 'r', 'e', 'r'], ['h', 'i', 'k', 'e', 'r'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['k', 'u', 'r', 'z'], ['b', 'r', 'i', 'e', 'f', 'l', 'y'], [⟨['k', 'u', 'r', 'z'], ['b', 'r', 'i', 'e', 'f', 'l', 'y'], none⟩]⟩, ⟨['v', 'e', 'r', 'w', 'e', 'i', 'l', 't'], ['s', 't', 'a', 'y', 'e', 'd'], [⟨['v', 'e', 'r', 'w', 'e', 'i', 'l', 't'], ['s', 't', 'a', 'y', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Der Wanderer ist kurz verweilt", .questionable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "haben"⟩, ⟨4, 1, "participle", some "verweilen"⟩]
    paperFeatures := [] }

def ex18a : Datum :=
  { id := "sorace2000_ex18a"
    source := ⟨"sorace-2000", "(18a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Slechts één kandidaat is uiteindelijk overgebleven"
    glossedTokens := [("Slechts", "only"), ("één", "one"), ("kandidaat", "candidate"), ("is", "is"), ("uiteindelijk", "finally"), ("overgebleven", "remained")]
    glossedWords := [⟨['S', 'l', 'e', 'c', 'h', 't', 's'], ['o', 'n', 'l', 'y'], [⟨['S', 'l', 'e', 'c', 'h', 't', 's'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['é', 'é', 'n'], ['o', 'n', 'e'], [⟨['é', 'é', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'a', 'n', 'd', 'i', 'd', 'a', 'a', 't'], ['c', 'a', 'n', 'd', 'i', 'd', 'a', 't', 'e'], [⟨['k', 'a', 'n', 'd', 'i', 'd', 'a', 'a', 't'], ['c', 'a', 'n', 'd', 'i', 'd', 'a', 't', 'e'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['u', 'i', 't', 'e', 'i', 'n', 'd', 'e', 'l', 'i', 'j', 'k'], ['f', 'i', 'n', 'a', 'l', 'l', 'y'], [⟨['u', 'i', 't', 'e', 'i', 'n', 'd', 'e', 'l', 'i', 'j', 'k'], ['f', 'i', 'n', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['o', 'v', 'e', 'r', 'g', 'e', 'b', 'l', 'e', 'v', 'e', 'n'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], [⟨['o', 'v', 'e', 'r', 'g', 'e', 'b', 'l', 'e', 'v', 'e', 'n'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "auxiliary", some "zijn"⟩, ⟨5, 1, "participle", some "overblijven"⟩]
    paperFeatures := [] }

def ex18b : Datum :=
  { id := "sorace2000_ex18b"
    source := ⟨"sorace-2000", "(18b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het concert heeft een hele tijd geduurd"
    glossedTokens := [("Het", "the"), ("concert", "concert"), ("heeft", "has"), ("een", "a"), ("hele", "whole"), ("tijd", "time"), ("geduurd", "lasted")]
    glossedWords := [⟨['H', 'e', 't'], ['t', 'h', 'e'], [⟨['H', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'o', 'n', 'c', 'e', 'r', 't'], ['c', 'o', 'n', 'c', 'e', 'r', 't'], [⟨['c', 'o', 'n', 'c', 'e', 'r', 't'], ['c', 'o', 'n', 'c', 'e', 'r', 't'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['h', 'e', 'l', 'e'], ['w', 'h', 'o', 'l', 'e'], [⟨['h', 'e', 'l', 'e'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['t', 'i', 'j', 'd'], ['t', 'i', 'm', 'e'], [⟨['t', 'i', 'j', 'd'], ['t', 'i', 'm', 'e'], none⟩]⟩, ⟨['g', 'e', 'd', 'u', 'u', 'r', 'd'], ['l', 'a', 's', 't', 'e', 'd'], [⟨['g', 'e', 'd', 'u', 'u', 'r', 'd'], ['l', 'a', 's', 't', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Het concert is een hele tijd geduurd", .questionable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "hebben"⟩, ⟨6, 1, "participle", some "duren"⟩]
    paperFeatures := [] }

def ex19a : Datum :=
  { id := "sorace2000_ex19a"
    source := ⟨"sorace-2000", "(19a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie est restée à la maison avec les enfants"
    glossedTokens := [("Marie", "Marie"), ("est", "is"), ("restée", "remained"), ("à", "at"), ("la", "the"), ("maison", "house"), ("avec", "with"), ("les", "the"), ("enfants", "children")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['e', 's', 't'], ['i', 's'], [⟨['e', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['r', 'e', 's', 't', 'é', 'e'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], [⟨['r', 'e', 's', 't', 'é', 'e'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩, ⟨['à'], ['a', 't'], [⟨['à'], ['a', 't'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'a', 'i', 's', 'o', 'n'], ['h', 'o', 'u', 's', 'e'], [⟨['m', 'a', 'i', 's', 'o', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['a', 'v', 'e', 'c'], ['w', 'i', 't', 'h'], [⟨['a', 'v', 'e', 'c'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['l', 'e', 's'], ['t', 'h', 'e'], [⟨['l', 'e', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'n', 'f', 'a', 'n', 't', 's'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['e', 'n', 'f', 'a', 'n', 't', 's'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Marie a resté à la maison avec les enfants", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "être"⟩, ⟨2, 1, "participle", some "rester"⟩]
    paperFeatures := [] }

def ex19b : Datum :=
  { id := "sorace2000_ex19b"
    source := ⟨"sorace-2000", "(19b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De onverwachte gast is voor het eten gebleven"
    glossedTokens := [("De", "the"), ("onverwachte", "unexpected"), ("gast", "guest"), ("is", "is"), ("voor", "for"), ("het", "the"), ("eten", "meal"), ("gebleven", "remained")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['o', 'n', 'v', 'e', 'r', 'w', 'a', 'c', 'h', 't', 'e'], ['u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd'], [⟨['o', 'n', 'v', 'e', 'r', 'w', 'a', 'c', 'h', 't', 'e'], ['u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd'], none⟩]⟩, ⟨['g', 'a', 's', 't'], ['g', 'u', 'e', 's', 't'], [⟨['g', 'a', 's', 't'], ['g', 'u', 'e', 's', 't'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['v', 'o', 'o', 'r'], ['f', 'o', 'r'], [⟨['v', 'o', 'o', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['h', 'e', 't'], ['t', 'h', 'e'], [⟨['h', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 't', 'e', 'n'], ['m', 'e', 'a', 'l'], [⟨['e', 't', 'e', 'n'], ['m', 'e', 'a', 'l'], none⟩]⟩, ⟨['g', 'e', 'b', 'l', 'e', 'v', 'e', 'n'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], [⟨['g', 'e', 'b', 'l', 'e', 'v', 'e', 'n'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("De onverwachte gast heeft voor het eten gebleven", .ungrammatical)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "zijn"⟩, ⟨7, 1, "participle", some "blijven"⟩]
    paperFeatures := [] }

def ex19c : Datum :=
  { id := "sorace2000_ex19c"
    source := ⟨"sorace-2000", "(19c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Gäste sind am Tisch sitzen geblieben"
    glossedTokens := [("Die", "the"), ("Gäste", "guests"), ("sind", "are"), ("am", "at.the"), ("Tisch", "table"), ("sitzen", "seated"), ("geblieben", "remained")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'ä', 's', 't', 'e'], ['g', 'u', 'e', 's', 't', 's'], [⟨['G', 'ä', 's', 't', 'e'], ['g', 'u', 'e', 's', 't', 's'], none⟩]⟩, ⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], [⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], none⟩]⟩, ⟨['a', 'm'], ['a', 't', '.', 't', 'h', 'e'], [⟨['a', 'm'], ['a', 't', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['T', 'i', 's', 'c', 'h'], ['t', 'a', 'b', 'l', 'e'], [⟨['T', 'i', 's', 'c', 'h'], ['t', 'a', 'b', 'l', 'e'], none⟩]⟩, ⟨['s', 'i', 't', 'z', 'e', 'n'], ['s', 'e', 'a', 't', 'e', 'd'], [⟨['s', 'i', 't', 'z', 'e', 'n'], ['s', 'e', 'a', 't', 'e', 'd'], none⟩]⟩, ⟨['g', 'e', 'b', 'l', 'i', 'e', 'b', 'e', 'n'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], [⟨['g', 'e', 'b', 'l', 'i', 'e', 'b', 'e', 'n'], ['r', 'e', 'm', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Die Gäste haben am Tisch sitzen geblieben", .ungrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "sein"⟩, ⟨6, 1, "participle", some "bleiben"⟩]
    paperFeatures := [] }

def ex20a : Datum :=
  { id := "sorace2000_ex20a"
    source := ⟨"sorace-2000", "(20a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "I dinosauri sono esistiti 65 milioni di anni fa."
    glossedTokens := [("I", "the"), ("dinosauri", "dinosaurs"), ("sono", "are"), ("esistiti", "existed"), ("65", "65"), ("milioni", "millions"), ("di", "of"), ("anni", "years"), ("fa", "ago")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 'i'], ['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 's'], [⟨['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 'i'], ['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 's'], none⟩]⟩, ⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], [⟨['s', 'o', 'n', 'o'], ['a', 'r', 'e'], none⟩]⟩, ⟨['e', 's', 'i', 's', 't', 'i', 't', 'i'], ['e', 'x', 'i', 's', 't', 'e', 'd'], [⟨['e', 's', 'i', 's', 't', 'i', 't', 'i'], ['e', 'x', 'i', 's', 't', 'e', 'd'], none⟩]⟩, ⟨['6', '5'], ['6', '5'], [⟨['6', '5'], ['6', '5'], none⟩]⟩, ⟨['m', 'i', 'l', 'i', 'o', 'n', 'i'], ['m', 'i', 'l', 'l', 'i', 'o', 'n', 's'], [⟨['m', 'i', 'l', 'i', 'o', 'n', 'i'], ['m', 'i', 'l', 'l', 'i', 'o', 'n', 's'], none⟩]⟩, ⟨['d', 'i'], ['o', 'f'], [⟨['d', 'i'], ['o', 'f'], none⟩]⟩, ⟨['a', 'n', 'n', 'i'], ['y', 'e', 'a', 'r', 's'], [⟨['a', 'n', 'n', 'i'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['f', 'a'], ['a', 'g', 'o'], [⟨['f', 'a'], ['a', 'g', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("I dinosauri hanno esistito 65 milioni di anni fa.", .questionable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "esistere"⟩]
    paperFeatures := [] }

def ex20b : Datum :=
  { id := "sorace2000_ex20b"
    source := ⟨"sorace-2000", "(20b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La farina non è bastata per fare la torta."
    glossedTokens := [("La", "the"), ("farina", "flour"), ("non", "not"), ("è", "is"), ("bastata", "lasted"), ("per", "to"), ("fare", "make"), ("la", "the"), ("torta", "cake")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'a', 'r', 'i', 'n', 'a'], ['f', 'l', 'o', 'u', 'r'], [⟨['f', 'a', 'r', 'i', 'n', 'a'], ['f', 'l', 'o', 'u', 'r'], none⟩]⟩, ⟨['n', 'o', 'n'], ['n', 'o', 't'], [⟨['n', 'o', 'n'], ['n', 'o', 't'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['b', 'a', 's', 't', 'a', 't', 'a'], ['l', 'a', 's', 't', 'e', 'd'], [⟨['b', 'a', 's', 't', 'a', 't', 'a'], ['l', 'a', 's', 't', 'e', 'd'], none⟩]⟩, ⟨['p', 'e', 'r'], ['t', 'o'], [⟨['p', 'e', 'r'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'e'], ['m', 'a', 'k', 'e'], [⟨['f', 'a', 'r', 'e'], ['m', 'a', 'k', 'e'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'o', 'r', 't', 'a'], ['c', 'a', 'k', 'e'], [⟨['t', 'o', 'r', 't', 'a'], ['c', 'a', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La farina non ha bastato per fare la torta.", .questionable)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "essere"⟩, ⟨4, 1, "participle", some "bastare"⟩]
    paperFeatures := [] }

def ex20c : Datum :=
  { id := "sorace2000_ex20c"
    source := ⟨"sorace-2000", "(20c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La commedia è sembrata interessante a tutti"
    glossedTokens := [("La", "the"), ("commedia", "play"), ("è", "is"), ("sembrata", "seemed"), ("interessante", "interesting"), ("a", "to"), ("tutti", "all")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'o', 'm', 'm', 'e', 'd', 'i', 'a'], ['p', 'l', 'a', 'y'], [⟨['c', 'o', 'm', 'm', 'e', 'd', 'i', 'a'], ['p', 'l', 'a', 'y'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['s', 'e', 'm', 'b', 'r', 'a', 't', 'a'], ['s', 'e', 'e', 'm', 'e', 'd'], [⟨['s', 'e', 'm', 'b', 'r', 'a', 't', 'a'], ['s', 'e', 'e', 'm', 'e', 'd'], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'r', 'e', 's', 's', 'a', 'n', 't', 'e'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], [⟨['i', 'n', 't', 'e', 'r', 'e', 's', 's', 'a', 'n', 't', 'e'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['t', 'u', 't', 't', 'i'], ['a', 'l', 'l'], [⟨['t', 'u', 't', 't', 'i'], ['a', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La commedia ha sembrato interessante a tutti", .questionable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "sembrare"⟩]
    paperFeatures := [] }

def ex21a : Datum :=
  { id := "sorace2000_ex21a"
    source := ⟨"sorace-2000", "(21a)"⟩
    reportedIn := none
    method := some .corpus
    language := "ital1282"
    primaryText := "Una lunghissima vita avrebbe appena bastato ad appagare il mio cuore."
    glossedTokens := [("Una", "a"), ("lunghissima", "very.long"), ("vita", "life"), ("avrebbe", "would.have"), ("appena", "just"), ("bastato", "sufficed"), ("ad", "to"), ("appagare", "satisfy"), ("il", "the"), ("mio", "my"), ("cuore", "heart")]
    glossedWords := [⟨['U', 'n', 'a'], ['a'], [⟨['U', 'n', 'a'], ['a'], none⟩]⟩, ⟨['l', 'u', 'n', 'g', 'h', 'i', 's', 's', 'i', 'm', 'a'], ['v', 'e', 'r', 'y', '.', 'l', 'o', 'n', 'g'], [⟨['l', 'u', 'n', 'g', 'h', 'i', 's', 's', 'i', 'm', 'a'], ['v', 'e', 'r', 'y', '.', 'l', 'o', 'n', 'g'], none⟩]⟩, ⟨['v', 'i', 't', 'a'], ['l', 'i', 'f', 'e'], [⟨['v', 'i', 't', 'a'], ['l', 'i', 'f', 'e'], none⟩]⟩, ⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['w', 'o', 'u', 'l', 'd', '.', 'h', 'a', 'v', 'e'], [⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['w', 'o', 'u', 'l', 'd', '.', 'h', 'a', 'v', 'e'], none⟩]⟩, ⟨['a', 'p', 'p', 'e', 'n', 'a'], ['j', 'u', 's', 't'], [⟨['a', 'p', 'p', 'e', 'n', 'a'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['b', 'a', 's', 't', 'a', 't', 'o'], ['s', 'u', 'f', 'f', 'i', 'c', 'e', 'd'], [⟨['b', 'a', 's', 't', 'a', 't', 'o'], ['s', 'u', 'f', 'f', 'i', 'c', 'e', 'd'], none⟩]⟩, ⟨['a', 'd'], ['t', 'o'], [⟨['a', 'd'], ['t', 'o'], none⟩]⟩, ⟨['a', 'p', 'p', 'a', 'g', 'a', 'r', 'e'], ['s', 'a', 't', 'i', 's', 'f', 'y'], [⟨['a', 'p', 'p', 'a', 'g', 'a', 'r', 'e'], ['s', 'a', 't', 'i', 's', 'f', 'y'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'i', 'o'], ['m', 'y'], [⟨['m', 'i', 'o'], ['m', 'y'], none⟩]⟩, ⟨['c', 'u', 'o', 'r', 'e'], ['h', 'e', 'a', 'r', 't'], [⟨['c', 'u', 'o', 'r', 'e'], ['h', 'e', 'a', 'r', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "auxiliary", some "avere"⟩, ⟨5, 1, "participle", some "bastare"⟩]
    paperFeatures := [] }

def ex21b : Datum :=
  { id := "sorace2000_ex21b"
    source := ⟨"sorace-2000", "(21b)"⟩
    reportedIn := none
    method := some .corpus
    language := "ital1282"
    primaryText := "La vita ha appartenuto solo a me."
    glossedTokens := [("La", "the"), ("vita", "life"), ("ha", "has"), ("appartenuto", "belonged"), ("solo", "only"), ("a", "to"), ("me", "me")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 't', 'a'], ['l', 'i', 'f', 'e'], [⟨['v', 'i', 't', 'a'], ['l', 'i', 'f', 'e'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['a', 'p', 'p', 'a', 'r', 't', 'e', 'n', 'u', 't', 'o'], ['b', 'e', 'l', 'o', 'n', 'g', 'e', 'd'], [⟨['a', 'p', 'p', 'a', 'r', 't', 'e', 'n', 'u', 't', 'o'], ['b', 'e', 'l', 'o', 'n', 'g', 'e', 'd'], none⟩]⟩, ⟨['s', 'o', 'l', 'o'], ['o', 'n', 'l', 'y'], [⟨['s', 'o', 'l', 'o'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['m', 'e'], ['m', 'e'], [⟨['m', 'e'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "appartenere"⟩]
    paperFeatures := [] }

def ex21c : Datum :=
  { id := "sorace2000_ex21c"
    source := ⟨"sorace-2000", "(21c)"⟩
    reportedIn := none
    method := some .corpus
    language := "ital1282"
    primaryText := "Il cibo è scarseggiato tra i terremotati."
    glossedTokens := [("Il", "the"), ("cibo", "food"), ("è", "is"), ("scarseggiato", "run.short.supply"), ("tra", "among"), ("i", "the"), ("terremotati", "earthquake.victims")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'i', 'b', 'o'], ['f', 'o', 'o', 'd'], [⟨['c', 'i', 'b', 'o'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['s', 'c', 'a', 'r', 's', 'e', 'g', 'g', 'i', 'a', 't', 'o'], ['r', 'u', 'n', '.', 's', 'h', 'o', 'r', 't', '.', 's', 'u', 'p', 'p', 'l', 'y'], [⟨['s', 'c', 'a', 'r', 's', 'e', 'g', 'g', 'i', 'a', 't', 'o'], ['r', 'u', 'n', '.', 's', 'h', 'o', 'r', 't', '.', 's', 'u', 'p', 'p', 'l', 'y'], none⟩]⟩, ⟨['t', 'r', 'a'], ['a', 'm', 'o', 'n', 'g'], [⟨['t', 'r', 'a'], ['a', 'm', 'o', 'n', 'g'], none⟩]⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 'r', 'r', 'e', 'm', 'o', 't', 'a', 't', 'i'], ['e', 'a', 'r', 't', 'h', 'q', 'u', 'a', 'k', 'e', '.', 'v', 'i', 'c', 't', 'i', 'm', 's'], [⟨['t', 'e', 'r', 'r', 'e', 'm', 'o', 't', 'a', 't', 'i'], ['e', 'a', 'r', 't', 'h', 'q', 'u', 'a', 'k', 'e', '.', 'v', 'i', 'c', 't', 'i', 'm', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il cibo ha scarseggiato tra i terremotati.", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "essere"⟩, ⟨3, 1, "participle", some "scarseggiare"⟩]
    paperFeatures := [] }

def ex22 : Datum :=
  { id := "sorace2000_ex22"
    source := ⟨"sorace-2000", "(22)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les dinosaures ont existé il y a 65 millions d'ans."
    glossedTokens := [("Les", "the"), ("dinosaures", "dinosaurs"), ("ont", "have"), ("existé", "existed"), ("il y a", "there.is"), ("65", "65"), ("millions", "million"), ("d'ans", "of.years")]
    glossedWords := [⟨['L', 'e', 's'], ['t', 'h', 'e'], [⟨['L', 'e', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 'e', 's'], ['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 's'], [⟨['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 'e', 's'], ['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 's'], none⟩]⟩, ⟨['o', 'n', 't'], ['h', 'a', 'v', 'e'], [⟨['o', 'n', 't'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['e', 'x', 'i', 's', 't', 'é'], ['e', 'x', 'i', 's', 't', 'e', 'd'], [⟨['e', 'x', 'i', 's', 't', 'é'], ['e', 'x', 'i', 's', 't', 'e', 'd'], none⟩]⟩, ⟨['i', 'l', ' ', 'y', ' ', 'a'], ['t', 'h', 'e', 'r', 'e', '.', 'i', 's'], [⟨['i', 'l', ' ', 'y', ' ', 'a'], ['t', 'h', 'e', 'r', 'e', '.', 'i', 's'], none⟩]⟩, ⟨['6', '5'], ['6', '5'], [⟨['6', '5'], ['6', '5'], none⟩]⟩, ⟨['m', 'i', 'l', 'l', 'i', 'o', 'n', 's'], ['m', 'i', 'l', 'l', 'i', 'o', 'n'], [⟨['m', 'i', 'l', 'l', 'i', 'o', 'n', 's'], ['m', 'i', 'l', 'l', 'i', 'o', 'n'], none⟩]⟩, ⟨['d', '\'', 'a', 'n', 's'], ['o', 'f', '.', 'y', 'e', 'a', 'r', 's'], [⟨['d', '\'', 'a', 'n', 's'], ['o', 'f', '.', 'y', 'e', 'a', 'r', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Les dinosaures sont existé il y a 65 millions d'ans.", .nearlyUngrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avoir"⟩, ⟨3, 1, "participle", some "exister"⟩]
    paperFeatures := [] }

def ex23a : Datum :=
  { id := "sorace2000_ex23a"
    source := ⟨"sorace-2000", "(23a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Buch hat mir gefallen."
    glossedTokens := [("Das", "the"), ("Buch", "book"), ("hat", "has"), ("mir", "to-me"), ("gefallen", "pleased")]
    glossedWords := [⟨['D', 'a', 's'], ['t', 'h', 'e'], [⟨['D', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'u', 'c', 'h'], ['b', 'o', 'o', 'k'], [⟨['B', 'u', 'c', 'h'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['m', 'i', 'r'], ['t', 'o', '-', 'm', 'e'], []⟩, ⟨['g', 'e', 'f', 'a', 'l', 'l', 'e', 'n'], ['p', 'l', 'e', 'a', 's', 'e', 'd'], [⟨['g', 'e', 'f', 'a', 'l', 'l', 'e', 'n'], ['p', 'l', 'e', 'a', 's', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "haben"⟩, ⟨4, 1, "participle", some "gefallen"⟩]
    paperFeatures := [] }

def ex23b : Datum :=
  { id := "sorace2000_ex23b"
    source := ⟨"sorace-2000", "(23b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das hat mir genügt."
    glossedTokens := [("Das", "this"), ("hat", "has"), ("mir", "to-me"), ("genügt", "sufficed")]
    glossedWords := [⟨['D', 'a', 's'], ['t', 'h', 'i', 's'], [⟨['D', 'a', 's'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['m', 'i', 'r'], ['t', 'o', '-', 'm', 'e'], []⟩, ⟨['g', 'e', 'n', 'ü', 'g', 't'], ['s', 'u', 'f', 'f', 'i', 'c', 'e', 'd'], [⟨['g', 'e', 'n', 'ü', 'g', 't'], ['s', 'u', 'f', 'f', 'i', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "haben"⟩, ⟨3, 1, "participle", some "genügen"⟩]
    paperFeatures := [] }

def ex23c : Datum :=
  { id := "sorace2000_ex23c"
    source := ⟨"sorace-2000", "(23c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Buch ist auf dem Boden gelegen."
    glossedTokens := [("Das", "the"), ("Buch", "book"), ("ist", "is"), ("auf", "on"), ("dem", "the"), ("Boden", "floor"), ("gelegen", "lain")]
    glossedWords := [⟨['D', 'a', 's'], ['t', 'h', 'e'], [⟨['D', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'u', 'c', 'h'], ['b', 'o', 'o', 'k'], [⟨['B', 'u', 'c', 'h'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['a', 'u', 'f'], ['o', 'n'], [⟨['a', 'u', 'f'], ['o', 'n'], none⟩]⟩, ⟨['d', 'e', 'm'], ['t', 'h', 'e'], [⟨['d', 'e', 'm'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'o', 'd', 'e', 'n'], ['f', 'l', 'o', 'o', 'r'], [⟨['B', 'o', 'd', 'e', 'n'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩, ⟨['g', 'e', 'l', 'e', 'g', 'e', 'n'], ['l', 'a', 'i', 'n'], [⟨['g', 'e', 'l', 'e', 'g', 'e', 'n'], ['l', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Das Buch hat auf dem Boden gelegen.", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "sein"⟩, ⟨6, 1, "participle", some "liegen"⟩]
    paperFeatures := [] }

def ex23d : Datum :=
  { id := "sorace2000_ex23d"
    source := ⟨"sorace-2000", "(23d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich bin von ihr abgehangen."
    glossedTokens := [("Ich", "I"), ("bin", "am"), ("von", "from"), ("ihr", "her"), ("abgehangen", "depended")]
    glossedWords := [⟨['I', 'c', 'h'], ['I'], [⟨['I', 'c', 'h'], ['I'], none⟩]⟩, ⟨['b', 'i', 'n'], ['a', 'm'], [⟨['b', 'i', 'n'], ['a', 'm'], none⟩]⟩, ⟨['v', 'o', 'n'], ['f', 'r', 'o', 'm'], [⟨['v', 'o', 'n'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['i', 'h', 'r'], ['h', 'e', 'r'], [⟨['i', 'h', 'r'], ['h', 'e', 'r'], none⟩]⟩, ⟨['a', 'b', 'g', 'e', 'h', 'a', 'n', 'g', 'e', 'n'], ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'd'], [⟨['a', 'b', 'g', 'e', 'h', 'a', 'n', 'g', 'e', 'n'], ['d', 'e', 'p', 'e', 'n', 'd', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ich habe von ihr abgehangen.", .acceptable)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "sein"⟩, ⟨4, 1, "participle", some "abhängen"⟩]
    paperFeatures := [] }

def ex24a : Datum :=
  { id := "sorace2000_ex24a"
    source := ⟨"sorace-2000", "(24a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het beeldje heeft op de tafel gestaan."
    glossedTokens := [("Het", "the"), ("beeldje", "picture"), ("heeft", "has"), ("op", "on"), ("de", "the"), ("tafel", "table"), ("gestaan", "stood")]
    glossedWords := [⟨['H', 'e', 't'], ['t', 'h', 'e'], [⟨['H', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'e', 'e', 'l', 'd', 'j', 'e'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], [⟨['b', 'e', 'e', 'l', 'd', 'j', 'e'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'f', 'e', 'l'], ['t', 'a', 'b', 'l', 'e'], [⟨['t', 'a', 'f', 'e', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩]⟩, ⟨['g', 'e', 's', 't', 'a', 'a', 'n'], ['s', 't', 'o', 'o', 'd'], [⟨['g', 'e', 's', 't', 'a', 'a', 'n'], ['s', 't', 'o', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "hebben"⟩, ⟨6, 1, "participle", some "staan"⟩]
    paperFeatures := [] }

def ex24b : Datum :=
  { id := "sorace2000_ex24b"
    source := ⟨"sorace-2000", "(24b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het magische zwaard heeft echt bestaan."
    glossedTokens := [("Het", "the"), ("magische", "magic"), ("zwaard", "sword"), ("heeft", "has"), ("echt", "really"), ("bestaan", "existed")]
    glossedWords := [⟨['H', 'e', 't'], ['t', 'h', 'e'], [⟨['H', 'e', 't'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 's', 'c', 'h', 'e'], ['m', 'a', 'g', 'i', 'c'], [⟨['m', 'a', 'g', 'i', 's', 'c', 'h', 'e'], ['m', 'a', 'g', 'i', 'c'], none⟩]⟩, ⟨['z', 'w', 'a', 'a', 'r', 'd'], ['s', 'w', 'o', 'r', 'd'], [⟨['z', 'w', 'a', 'a', 'r', 'd'], ['s', 'w', 'o', 'r', 'd'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['e', 'c', 'h', 't'], ['r', 'e', 'a', 'l', 'l', 'y'], [⟨['e', 'c', 'h', 't'], ['r', 'e', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['b', 'e', 's', 't', 'a', 'a', 'n'], ['e', 'x', 'i', 's', 't', 'e', 'd'], [⟨['b', 'e', 's', 't', 'a', 'a', 'n'], ['e', 'x', 'i', 's', 't', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "auxiliary", some "hebben"⟩, ⟨5, 1, "participle", some "bestaan"⟩]
    paperFeatures := [] }

def ex24c : Datum :=
  { id := "sorace2000_ex24c"
    source := ⟨"sorace-2000", "(24c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Sofie is een goede docente gebleken."
    glossedTokens := [("Sofie", "Sofie"), ("is", "is"), ("een", "a"), ("goede", "good"), ("docente", "teacher"), ("gebleken", "seemed")]
    glossedWords := [⟨['S', 'o', 'f', 'i', 'e'], ['S', 'o', 'f', 'i', 'e'], [⟨['S', 'o', 'f', 'i', 'e'], ['S', 'o', 'f', 'i', 'e'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['g', 'o', 'e', 'd', 'e'], ['g', 'o', 'o', 'd'], [⟨['g', 'o', 'e', 'd', 'e'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['d', 'o', 'c', 'e', 'n', 't', 'e'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['d', 'o', 'c', 'e', 'n', 't', 'e'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['g', 'e', 'b', 'l', 'e', 'k', 'e', 'n'], ['s', 'e', 'e', 'm', 'e', 'd'], [⟨['g', 'e', 'b', 'l', 'e', 'k', 'e', 'n'], ['s', 'e', 'e', 'm', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "zijn"⟩, ⟨5, 1, "participle", some "blijken"⟩]
    paperFeatures := [] }

def ex25a : Datum :=
  { id := "sorace2000_ex25a"
    source := ⟨"sorace-2000", "(25a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter ist lange Zeit im Ausland gewesen."
    glossedTokens := [("Peter", "Peter"), ("ist", "is"), ("lange", "long"), ("Zeit", "time"), ("im", "in.the"), ("Ausland", "abroad"), ("gewesen", "been")]
    glossedWords := [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['l', 'a', 'n', 'g', 'e'], ['l', 'o', 'n', 'g'], [⟨['l', 'a', 'n', 'g', 'e'], ['l', 'o', 'n', 'g'], none⟩]⟩, ⟨['Z', 'e', 'i', 't'], ['t', 'i', 'm', 'e'], [⟨['Z', 'e', 'i', 't'], ['t', 'i', 'm', 'e'], none⟩]⟩, ⟨['i', 'm'], ['i', 'n', '.', 't', 'h', 'e'], [⟨['i', 'm'], ['i', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['A', 'u', 's', 'l', 'a', 'n', 'd'], ['a', 'b', 'r', 'o', 'a', 'd'], [⟨['A', 'u', 's', 'l', 'a', 'n', 'd'], ['a', 'b', 'r', 'o', 'a', 'd'], none⟩]⟩, ⟨['g', 'e', 'w', 'e', 's', 'e', 'n'], ['b', 'e', 'e', 'n'], [⟨['g', 'e', 'w', 'e', 's', 'e', 'n'], ['b', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "sein"⟩, ⟨6, 1, "participle", some "sein"⟩]
    paperFeatures := [] }

def ex25b : Datum :=
  { id := "sorace2000_ex25b"
    source := ⟨"sorace-2000", "(25b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Anne is deze winter in Australië geweest."
    glossedTokens := [("Anne", "Anne"), ("is", "is"), ("deze", "this"), ("winter", "winter"), ("in", "in"), ("Australië", "Australia"), ("geweest", "been")]
    glossedWords := [⟨['A', 'n', 'n', 'e'], ['A', 'n', 'n', 'e'], [⟨['A', 'n', 'n', 'e'], ['A', 'n', 'n', 'e'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'z', 'e'], ['t', 'h', 'i', 's'], [⟨['d', 'e', 'z', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['w', 'i', 'n', 't', 'e', 'r'], ['w', 'i', 'n', 't', 'e', 'r'], [⟨['w', 'i', 'n', 't', 'e', 'r'], ['w', 'i', 'n', 't', 'e', 'r'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['A', 'u', 's', 't', 'r', 'a', 'l', 'i', 'ë'], ['A', 'u', 's', 't', 'r', 'a', 'l', 'i', 'a'], [⟨['A', 'u', 's', 't', 'r', 'a', 'l', 'i', 'ë'], ['A', 'u', 's', 't', 'r', 'a', 'l', 'i', 'a'], none⟩]⟩, ⟨['g', 'e', 'w', 'e', 'e', 's', 't'], ['b', 'e', 'e', 'n'], [⟨['g', 'e', 'w', 'e', 'e', 's', 't'], ['b', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "zijn"⟩, ⟨6, 1, "participle", some "zijn"⟩]
    paperFeatures := [] }

def ex33a : Datum :=
  { id := "sorace2000_ex33a"
    source := ⟨"sorace-2000", "(33a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "I colleghi hanno chiacchierato tutto il pomeriggio."
    glossedTokens := [("I", "the"), ("colleghi", "colleagues"), ("hanno", "have"), ("chiacchierato", "chatted"), ("tutto", "whole"), ("il", "the"), ("pomeriggio", "afternoon")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'o', 'l', 'l', 'e', 'g', 'h', 'i'], ['c', 'o', 'l', 'l', 'e', 'a', 'g', 'u', 'e', 's'], [⟨['c', 'o', 'l', 'l', 'e', 'g', 'h', 'i'], ['c', 'o', 'l', 'l', 'e', 'a', 'g', 'u', 'e', 's'], none⟩]⟩, ⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['c', 'h', 'i', 'a', 'c', 'c', 'h', 'i', 'e', 'r', 'a', 't', 'o'], ['c', 'h', 'a', 't', 't', 'e', 'd'], [⟨['c', 'h', 'i', 'a', 'c', 'c', 'h', 'i', 'e', 'r', 'a', 't', 'o'], ['c', 'h', 'a', 't', 't', 'e', 'd'], none⟩]⟩, ⟨['t', 'u', 't', 't', 'o'], ['w', 'h', 'o', 'l', 'e'], [⟨['t', 'u', 't', 't', 'o'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'o', 'm', 'e', 'r', 'i', 'g', 'g', 'i', 'o'], ['a', 'f', 't', 'e', 'r', 'n', 'o', 'o', 'n'], [⟨['p', 'o', 'm', 'e', 'r', 'i', 'g', 'g', 'i', 'o'], ['a', 'f', 't', 'e', 'r', 'n', 'o', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "chiacchierare"⟩]
    paperFeatures := [] }

def ex33b : Datum :=
  { id := "sorace2000_ex33b"
    source := ⟨"sorace-2000", "(33b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les policiers ont travaillé toute la nuit."
    glossedTokens := [("Les", "the"), ("policiers", "policemen"), ("ont", "have"), ("travaillé", "worked"), ("toute", "whole"), ("la", "the"), ("nuit", "night")]
    glossedWords := [⟨['L', 'e', 's'], ['t', 'h', 'e'], [⟨['L', 'e', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'o', 'l', 'i', 'c', 'i', 'e', 'r', 's'], ['p', 'o', 'l', 'i', 'c', 'e', 'm', 'e', 'n'], [⟨['p', 'o', 'l', 'i', 'c', 'i', 'e', 'r', 's'], ['p', 'o', 'l', 'i', 'c', 'e', 'm', 'e', 'n'], none⟩]⟩, ⟨['o', 'n', 't'], ['h', 'a', 'v', 'e'], [⟨['o', 'n', 't'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['t', 'r', 'a', 'v', 'a', 'i', 'l', 'l', 'é'], ['w', 'o', 'r', 'k', 'e', 'd'], [⟨['t', 'r', 'a', 'v', 'a', 'i', 'l', 'l', 'é'], ['w', 'o', 'r', 'k', 'e', 'd'], none⟩]⟩, ⟨['t', 'o', 'u', 't', 'e'], ['w', 'h', 'o', 'l', 'e'], [⟨['t', 'o', 'u', 't', 'e'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['n', 'u', 'i', 't'], ['n', 'i', 'g', 'h', 't'], [⟨['n', 'u', 'i', 't'], ['n', 'i', 'g', 'h', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avoir"⟩, ⟨3, 1, "participle", some "travailler"⟩]
    paperFeatures := [] }

def ex33c : Datum :=
  { id := "sorace2000_ex33c"
    source := ⟨"sorace-2000", "(33c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De trompettist heeft met bolle wangen geblazen."
    glossedTokens := [("De", "the"), ("trompettist", "trumpeter"), ("heeft", "has"), ("met", "with"), ("bolle", "puffed-out"), ("wangen", "cheeks"), ("geblazen", "blown")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'r', 'o', 'm', 'p', 'e', 't', 't', 'i', 's', 't'], ['t', 'r', 'u', 'm', 'p', 'e', 't', 'e', 'r'], [⟨['t', 'r', 'o', 'm', 'p', 'e', 't', 't', 'i', 's', 't'], ['t', 'r', 'u', 'm', 'p', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['m', 'e', 't'], ['w', 'i', 't', 'h'], [⟨['m', 'e', 't'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['b', 'o', 'l', 'l', 'e'], ['p', 'u', 'f', 'f', 'e', 'd', '-', 'o', 'u', 't'], []⟩, ⟨['w', 'a', 'n', 'g', 'e', 'n'], ['c', 'h', 'e', 'e', 'k', 's'], [⟨['w', 'a', 'n', 'g', 'e', 'n'], ['c', 'h', 'e', 'e', 'k', 's'], none⟩]⟩, ⟨['g', 'e', 'b', 'l', 'a', 'z', 'e', 'n'], ['b', 'l', 'o', 'w', 'n'], [⟨['g', 'e', 'b', 'l', 'a', 'z', 'e', 'n'], ['b', 'l', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "hebben"⟩, ⟨6, 1, "participle", some "blazen"⟩]
    paperFeatures := [] }

def ex33d : Datum :=
  { id := "sorace2000_ex33d"
    source := ⟨"sorace-2000", "(33d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kurt hat den ganzen Sonntag gearbeitet."
    glossedTokens := [("Kurt", "Kurt"), ("hat", "has"), ("den", "the"), ("ganzen", "whole"), ("Sonntag", "Sunday"), ("gearbeitet", "worked")]
    glossedWords := [⟨['K', 'u', 'r', 't'], ['K', 'u', 'r', 't'], [⟨['K', 'u', 'r', 't'], ['K', 'u', 'r', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], [⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['S', 'o', 'n', 'n', 't', 'a', 'g'], ['S', 'u', 'n', 'd', 'a', 'y'], [⟨['S', 'o', 'n', 'n', 't', 'a', 'g'], ['S', 'u', 'n', 'd', 'a', 'y'], none⟩]⟩, ⟨['g', 'e', 'a', 'r', 'b', 'e', 'i', 't', 'e', 't'], ['w', 'o', 'r', 'k', 'e', 'd'], [⟨['g', 'e', 'a', 'r', 'b', 'e', 'i', 't', 'e', 't'], ['w', 'o', 'r', 'k', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "haben"⟩, ⟨5, 1, "participle", some "arbeiten"⟩]
    paperFeatures := [] }

def ex34 : Datum :=
  { id := "sorace2000_ex34"
    source := ⟨"sorace-2000", "(34)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il cibo inviato dall'ONU ha funzionato solo come palliativo."
    glossedTokens := [("Il", "the"), ("cibo", "food"), ("inviato", "sent"), ("dall'ONU", "by.the.UN"), ("ha", "has"), ("funzionato", "functioned"), ("solo", "only"), ("come", "as"), ("palliativo", "palliative")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'i', 'b', 'o'], ['f', 'o', 'o', 'd'], [⟨['c', 'i', 'b', 'o'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['i', 'n', 'v', 'i', 'a', 't', 'o'], ['s', 'e', 'n', 't'], [⟨['i', 'n', 'v', 'i', 'a', 't', 'o'], ['s', 'e', 'n', 't'], none⟩]⟩, ⟨['d', 'a', 'l', 'l', '\'', 'O', 'N', 'U'], ['b', 'y', '.', 't', 'h', 'e', '.', 'U', 'N'], [⟨['d', 'a', 'l', 'l', '\'', 'O', 'N', 'U'], ['b', 'y', '.', 't', 'h', 'e', '.', 'U', 'N'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['f', 'u', 'n', 'z', 'i', 'o', 'n', 'a', 't', 'o'], ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n', 'e', 'd'], [⟨['f', 'u', 'n', 'z', 'i', 'o', 'n', 'a', 't', 'o'], ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n', 'e', 'd'], none⟩]⟩, ⟨['s', 'o', 'l', 'o'], ['o', 'n', 'l', 'y'], [⟨['s', 'o', 'l', 'o'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['c', 'o', 'm', 'e'], ['a', 's'], [⟨['c', 'o', 'm', 'e'], ['a', 's'], none⟩]⟩, ⟨['p', 'a', 'l', 'l', 'i', 'a', 't', 'i', 'v', 'o'], ['p', 'a', 'l', 'l', 'i', 'a', 't', 'i', 'v', 'e'], [⟨['p', 'a', 'l', 'l', 'i', 'a', 't', 'i', 'v', 'o'], ['p', 'a', 'l', 'l', 'i', 'a', 't', 'i', 'v', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il cibo inviato dall'ONU è funzionato solo come palliativo.", .marginal)]
    readings := []
    spans := [⟨4, 1, "auxiliary", some "avere"⟩, ⟨5, 1, "participle", some "funzionare"⟩]
    paperFeatures := [("subject", "nonagentive")] }

def ex35 : Datum :=
  { id := "sorace2000_ex35"
    source := ⟨"sorace-2000", "(35)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "I poliziotti hanno lavorato fino all'alba."
    glossedTokens := [("I", "the"), ("poliziotti", "policemen"), ("hanno", "have"), ("lavorato", "worked"), ("fino", "until"), ("all'alba", "the.dawn")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'o', 'l', 'i', 'z', 'i', 'o', 't', 't', 'i'], ['p', 'o', 'l', 'i', 'c', 'e', 'm', 'e', 'n'], [⟨['p', 'o', 'l', 'i', 'z', 'i', 'o', 't', 't', 'i'], ['p', 'o', 'l', 'i', 'c', 'e', 'm', 'e', 'n'], none⟩]⟩, ⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['l', 'a', 'v', 'o', 'r', 'a', 't', 'o'], ['w', 'o', 'r', 'k', 'e', 'd'], [⟨['l', 'a', 'v', 'o', 'r', 'a', 't', 'o'], ['w', 'o', 'r', 'k', 'e', 'd'], none⟩]⟩, ⟨['f', 'i', 'n', 'o'], ['u', 'n', 't', 'i', 'l'], [⟨['f', 'i', 'n', 'o'], ['u', 'n', 't', 'i', 'l'], none⟩]⟩, ⟨['a', 'l', 'l', '\'', 'a', 'l', 'b', 'a'], ['t', 'h', 'e', '.', 'd', 'a', 'w', 'n'], [⟨['a', 'l', 'l', '\'', 'a', 'l', 'b', 'a'], ['t', 'h', 'e', '.', 'd', 'a', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "lavorare"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex36a : Datum :=
  { id := "sorace2000_ex36a"
    source := ⟨"sorace-2000", "(36a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Maria ha ceduto alle tue insistenze"
    glossedTokens := [("Maria", "Maria"), ("ha", "has"), ("ceduto", "yielded"), ("alle", "to"), ("tue", "your"), ("insistenze", "pressure")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['c', 'e', 'd', 'u', 't', 'o'], ['y', 'i', 'e', 'l', 'd', 'e', 'd'], [⟨['c', 'e', 'd', 'u', 't', 'o'], ['y', 'i', 'e', 'l', 'd', 'e', 'd'], none⟩]⟩, ⟨['a', 'l', 'l', 'e'], ['t', 'o'], [⟨['a', 'l', 'l', 'e'], ['t', 'o'], none⟩]⟩, ⟨['t', 'u', 'e'], ['y', 'o', 'u', 'r'], [⟨['t', 'u', 'e'], ['y', 'o', 'u', 'r'], none⟩]⟩, ⟨['i', 'n', 's', 'i', 's', 't', 'e', 'n', 'z', 'e'], ['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], [⟨['i', 'n', 's', 'i', 's', 't', 'e', 'n', 'z', 'e'], ['p', 'r', 'e', 's', 's', 'u', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Maria è ceduta alle tue insistenze", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "cedere"⟩]
    paperFeatures := [] }

def ex36b : Datum :=
  { id := "sorace2000_ex36b"
    source := ⟨"sorace-2000", "(36b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il pavimento ha ceduto all'improvviso"
    glossedTokens := [("Il", "the"), ("pavimento", "floor"), ("ha", "has"), ("ceduto", "yielded"), ("all'improvviso", "suddenly")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'a', 'v', 'i', 'm', 'e', 'n', 't', 'o'], ['f', 'l', 'o', 'o', 'r'], [⟨['p', 'a', 'v', 'i', 'm', 'e', 'n', 't', 'o'], ['f', 'l', 'o', 'o', 'r'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['c', 'e', 'd', 'u', 't', 'o'], ['y', 'i', 'e', 'l', 'd', 'e', 'd'], [⟨['c', 'e', 'd', 'u', 't', 'o'], ['y', 'i', 'e', 'l', 'd', 'e', 'd'], none⟩]⟩, ⟨['a', 'l', 'l', '\'', 'i', 'm', 'p', 'r', 'o', 'v', 'v', 'i', 's', 'o'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], [⟨['a', 'l', 'l', '\'', 'i', 'm', 'p', 'r', 'o', 'v', 'v', 'i', 's', 'o'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il pavimento è ceduto all'improvviso", .marginal)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "cedere"⟩]
    paperFeatures := [("subject", "nonagentive")] }

def ex37a : Datum :=
  { id := "sorace2000_ex37a"
    source := ⟨"sorace-2000", "(37a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gli atleti svedesi hanno corso alle Olimpiadi"
    glossedTokens := [("Gli", "the"), ("atleti", "athletes"), ("svedesi", "swedish"), ("hanno", "have"), ("corso", "run"), ("alle", "at.the"), ("Olimpiadi", "Olympics")]
    glossedWords := [⟨['G', 'l', 'i'], ['t', 'h', 'e'], [⟨['G', 'l', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 't', 'l', 'e', 't', 'i'], ['a', 't', 'h', 'l', 'e', 't', 'e', 's'], [⟨['a', 't', 'l', 'e', 't', 'i'], ['a', 't', 'h', 'l', 'e', 't', 'e', 's'], none⟩]⟩, ⟨['s', 'v', 'e', 'd', 'e', 's', 'i'], ['s', 'w', 'e', 'd', 'i', 's', 'h'], [⟨['s', 'v', 'e', 'd', 'e', 's', 'i'], ['s', 'w', 'e', 'd', 'i', 's', 'h'], none⟩]⟩, ⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['c', 'o', 'r', 's', 'o'], ['r', 'u', 'n'], [⟨['c', 'o', 'r', 's', 'o'], ['r', 'u', 'n'], none⟩]⟩, ⟨['a', 'l', 'l', 'e'], ['a', 't', '.', 't', 'h', 'e'], [⟨['a', 'l', 'l', 'e'], ['a', 't', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['O', 'l', 'i', 'm', 'p', 'i', 'a', 'd', 'i'], ['O', 'l', 'y', 'm', 'p', 'i', 'c', 's'], [⟨['O', 'l', 'i', 'm', 'p', 'i', 'a', 'd', 'i'], ['O', 'l', 'y', 'm', 'p', 'i', 'c', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Gli atleti svedesi sono corsi alle Olimpiadi", .marginal)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "avere"⟩, ⟨4, 1, "participle", some "correre"⟩]
    paperFeatures := [] }

def ex37b : Datum :=
  { id := "sorace2000_ex37b"
    source := ⟨"sorace-2000", "(37b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De zwerver heeft overal gelopen"
    glossedTokens := [("De", "the"), ("zwerver", "vagabond"), ("heeft", "has"), ("overal", "overall"), ("gelopen", "run")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['z', 'w', 'e', 'r', 'v', 'e', 'r'], ['v', 'a', 'g', 'a', 'b', 'o', 'n', 'd'], [⟨['z', 'w', 'e', 'r', 'v', 'e', 'r'], ['v', 'a', 'g', 'a', 'b', 'o', 'n', 'd'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['o', 'v', 'e', 'r', 'a', 'l'], ['o', 'v', 'e', 'r', 'a', 'l', 'l'], [⟨['o', 'v', 'e', 'r', 'a', 'l'], ['o', 'v', 'e', 'r', 'a', 'l', 'l'], none⟩]⟩, ⟨['g', 'e', 'l', 'o', 'p', 'e', 'n'], ['r', 'u', 'n'], [⟨['g', 'e', 'l', 'o', 'p', 'e', 'n'], ['r', 'u', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("De zwerver is overal gelopen", .marginal)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "hebben"⟩, ⟨4, 1, "participle", some "lopen"⟩]
    paperFeatures := [] }

def ex37c : Datum :=
  { id := "sorace2000_ex37c"
    source := ⟨"sorace-2000", "(37c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie a nagé tout l'après-midi"
    glossedTokens := [("Marie", "Marie"), ("a", "has"), ("nagé", "swum"), ("tout", "all"), ("l'après-midi", "the.afternoon")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['a'], ['h', 'a', 's'], [⟨['a'], ['h', 'a', 's'], none⟩]⟩, ⟨['n', 'a', 'g', 'é'], ['s', 'w', 'u', 'm'], [⟨['n', 'a', 'g', 'é'], ['s', 'w', 'u', 'm'], none⟩]⟩, ⟨['t', 'o', 'u', 't'], ['a', 'l', 'l'], [⟨['t', 'o', 'u', 't'], ['a', 'l', 'l'], none⟩]⟩, ⟨['l', '\'', 'a', 'p', 'r', 'è', 's', '-', 'm', 'i', 'd', 'i'], ['t', 'h', 'e', '.', 'a', 'f', 't', 'e', 'r', 'n', 'o', 'o', 'n'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Marie est nagée tout l'après-midi", .marginal)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avoir"⟩, ⟨2, 1, "participle", some "nager"⟩]
    paperFeatures := [] }

def ex38_rennen : Datum :=
  { id := "sorace2000_ex38_rennen"
    source := ⟨"sorace-2000", "(38)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Uschi ist den ganzen Tag gerannt"
    glossedTokens := [("Uschi", "Uschi"), ("ist", "is"), ("den", "the"), ("ganzen", "whole"), ("Tag", "day"), ("gerannt", "run")]
    glossedWords := [⟨['U', 's', 'c', 'h', 'i'], ['U', 's', 'c', 'h', 'i'], [⟨['U', 's', 'c', 'h', 'i'], ['U', 's', 'c', 'h', 'i'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], [⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['T', 'a', 'g'], ['d', 'a', 'y'], [⟨['T', 'a', 'g'], ['d', 'a', 'y'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'n', 'n', 't'], ['r', 'u', 'n'], [⟨['g', 'e', 'r', 'a', 'n', 'n', 't'], ['r', 'u', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Uschi hat den ganzen Tag gerannt", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "sein"⟩, ⟨5, 1, "participle", some "rennen"⟩]
    paperFeatures := [] }

def ex38_laufen : Datum :=
  { id := "sorace2000_ex38_laufen"
    source := ⟨"sorace-2000", "(38)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Uschi ist den ganzen Tag gelaufen"
    glossedTokens := [("Uschi", "Uschi"), ("ist", "is"), ("den", "the"), ("ganzen", "whole"), ("Tag", "day"), ("gelaufen", "walked")]
    glossedWords := [⟨['U', 's', 'c', 'h', 'i'], ['U', 's', 'c', 'h', 'i'], [⟨['U', 's', 'c', 'h', 'i'], ['U', 's', 'c', 'h', 'i'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], [⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['T', 'a', 'g'], ['d', 'a', 'y'], [⟨['T', 'a', 'g'], ['d', 'a', 'y'], none⟩]⟩, ⟨['g', 'e', 'l', 'a', 'u', 'f', 'e', 'n'], ['w', 'a', 'l', 'k', 'e', 'd'], [⟨['g', 'e', 'l', 'a', 'u', 'f', 'e', 'n'], ['w', 'a', 'l', 'k', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Uschi hat den ganzen Tag gelaufen", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "sein"⟩, ⟨5, 1, "participle", some "laufen"⟩]
    paperFeatures := [] }

def ex38_schwimmen : Datum :=
  { id := "sorace2000_ex38_schwimmen"
    source := ⟨"sorace-2000", "(38)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Uschi ist den ganzen Tag geschwommen"
    glossedTokens := [("Uschi", "Uschi"), ("ist", "is"), ("den", "the"), ("ganzen", "whole"), ("Tag", "day"), ("geschwommen", "swum")]
    glossedWords := [⟨['U', 's', 'c', 'h', 'i'], ['U', 's', 'c', 'h', 'i'], [⟨['U', 's', 'c', 'h', 'i'], ['U', 's', 'c', 'h', 'i'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], [⟨['g', 'a', 'n', 'z', 'e', 'n'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['T', 'a', 'g'], ['d', 'a', 'y'], [⟨['T', 'a', 'g'], ['d', 'a', 'y'], none⟩]⟩, ⟨['g', 'e', 's', 'c', 'h', 'w', 'o', 'm', 'm', 'e', 'n'], ['s', 'w', 'u', 'm'], [⟨['g', 'e', 's', 'c', 'h', 'w', 'o', 'm', 'm', 'e', 'n'], ['s', 'w', 'u', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Uschi hat den ganzen Tag geschwommen", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "sein"⟩, ⟨5, 1, "participle", some "schwimmen"⟩]
    paperFeatures := [] }

def ex39a : Datum :=
  { id := "sorace2000_ex39a"
    source := ⟨"sorace-2000", "(39a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De bal heeft gerold"
    glossedTokens := [("De", "the"), ("bal", "ball"), ("heeft", "has"), ("gerold", "rolled")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'l'], ['b', 'a', 'l', 'l'], [⟨['b', 'a', 'l'], ['b', 'a', 'l', 'l'], none⟩]⟩, ⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], [⟨['h', 'e', 'e', 'f', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['g', 'e', 'r', 'o', 'l', 'd'], ['r', 'o', 'l', 'l', 'e', 'd'], [⟨['g', 'e', 'r', 'o', 'l', 'd'], ['r', 'o', 'l', 'l', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("De bal is gerold", .ungrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "hebben"⟩, ⟨3, 1, "participle", some "rollen"⟩]
    paperFeatures := [] }

def ex39b : Datum :=
  { id := "sorace2000_ex39b"
    source := ⟨"sorace-2000", "(39b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De bal is naar beneden gerold"
    glossedTokens := [("De", "the"), ("bal", "ball"), ("is", "is"), ("naar", "to"), ("beneden", "down"), ("gerold", "rolled")]
    glossedWords := [⟨['D', 'e'], ['t', 'h', 'e'], [⟨['D', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'l'], ['b', 'a', 'l', 'l'], [⟨['b', 'a', 'l'], ['b', 'a', 'l', 'l'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['n', 'a', 'a', 'r'], ['t', 'o'], [⟨['n', 'a', 'a', 'r'], ['t', 'o'], none⟩]⟩, ⟨['b', 'e', 'n', 'e', 'd', 'e', 'n'], ['d', 'o', 'w', 'n'], [⟨['b', 'e', 'n', 'e', 'd', 'e', 'n'], ['d', 'o', 'w', 'n'], none⟩]⟩, ⟨['g', 'e', 'r', 'o', 'l', 'd'], ['r', 'o', 'l', 'l', 'e', 'd'], [⟨['g', 'e', 'r', 'o', 'l', 'd'], ['r', 'o', 'l', 'l', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("De bal heeft naar beneden gerold", .ungrammatical)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "zijn"⟩, ⟨5, 1, "participle", some "rollen"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex40a : Datum :=
  { id := "sorace2000_ex40a"
    source := ⟨"sorace-2000", "(40a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans und Rita haben im Saal getanzt"
    glossedTokens := [("Hans", "Hans"), ("und", "and"), ("Rita", "Rita"), ("haben", "have"), ("im", "in.the"), ("Saal", "hall"), ("getanzt", "danced")]
    glossedWords := [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['u', 'n', 'd'], ['a', 'n', 'd'], [⟨['u', 'n', 'd'], ['a', 'n', 'd'], none⟩]⟩, ⟨['R', 'i', 't', 'a'], ['R', 'i', 't', 'a'], [⟨['R', 'i', 't', 'a'], ['R', 'i', 't', 'a'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['i', 'm'], ['i', 'n', '.', 't', 'h', 'e'], [⟨['i', 'm'], ['i', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['S', 'a', 'a', 'l'], ['h', 'a', 'l', 'l'], [⟨['S', 'a', 'a', 'l'], ['h', 'a', 'l', 'l'], none⟩]⟩, ⟨['g', 'e', 't', 'a', 'n', 'z', 't'], ['d', 'a', 'n', 'c', 'e', 'd'], [⟨['g', 'e', 't', 'a', 'n', 'z', 't'], ['d', 'a', 'n', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Hans und Rita sind im Saal getanzt", .ungrammatical)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "haben"⟩, ⟨6, 1, "participle", some "tanzen"⟩]
    paperFeatures := [] }

def ex40b : Datum :=
  { id := "sorace2000_ex40b"
    source := ⟨"sorace-2000", "(40b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans und Rita sind in den Saal getanzt"
    glossedTokens := [("Hans", "Hans"), ("und", "and"), ("Rita", "Rita"), ("sind", "are"), ("in", "into"), ("den", "the"), ("Saal", "hall"), ("getanzt", "danced")]
    glossedWords := [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['u', 'n', 'd'], ['a', 'n', 'd'], [⟨['u', 'n', 'd'], ['a', 'n', 'd'], none⟩]⟩, ⟨['R', 'i', 't', 'a'], ['R', 'i', 't', 'a'], [⟨['R', 'i', 't', 'a'], ['R', 'i', 't', 'a'], none⟩]⟩, ⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], [⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n', 't', 'o'], [⟨['i', 'n'], ['i', 'n', 't', 'o'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['S', 'a', 'a', 'l'], ['h', 'a', 'l', 'l'], [⟨['S', 'a', 'a', 'l'], ['h', 'a', 'l', 'l'], none⟩]⟩, ⟨['g', 'e', 't', 'a', 'n', 'z', 't'], ['d', 'a', 'n', 'c', 'e', 'd'], [⟨['g', 'e', 't', 'a', 'n', 'z', 't'], ['d', 'a', 'n', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Hans und Rita haben in den Saal getanzt", .ungrammatical)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "sein"⟩, ⟨7, 1, "participle", some "tanzen"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex41a : Datum :=
  { id := "sorace2000_ex41a"
    source := ⟨"sorace-2000", "(41a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Maria ha corso velocemente."
    glossedTokens := [("Maria", "Maria"), ("ha", "has"), ("corso", "run"), ("velocemente", "fast")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['c', 'o', 'r', 's', 'o'], ['r', 'u', 'n'], [⟨['c', 'o', 'r', 's', 'o'], ['r', 'u', 'n'], none⟩]⟩, ⟨['v', 'e', 'l', 'o', 'c', 'e', 'm', 'e', 'n', 't', 'e'], ['f', 'a', 's', 't'], [⟨['v', 'e', 'l', 'o', 'c', 'e', 'm', 'e', 'n', 't', 'e'], ['f', 'a', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Maria è corsa velocemente.", .acceptable)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "correre"⟩]
    paperFeatures := [] }

def ex41b : Datum :=
  { id := "sorace2000_ex41b"
    source := ⟨"sorace-2000", "(41b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Maria è corsa in farmacia"
    glossedTokens := [("Maria", "Maria"), ("è", "is"), ("corsa", "run"), ("in", "to"), ("farmacia", "the.pharmacy")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['c', 'o', 'r', 's', 'a'], ['r', 'u', 'n'], [⟨['c', 'o', 'r', 's', 'a'], ['r', 'u', 'n'], none⟩]⟩, ⟨['i', 'n'], ['t', 'o'], [⟨['i', 'n'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'm', 'a', 'c', 'i', 'a'], ['t', 'h', 'e', '.', 'p', 'h', 'a', 'r', 'm', 'a', 'c', 'y'], [⟨['f', 'a', 'r', 'm', 'a', 'c', 'i', 'a'], ['t', 'h', 'e', '.', 'p', 'h', 'a', 'r', 'm', 'a', 'c', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Maria ha corso in farmacia", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "correre"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex41c : Datum :=
  { id := "sorace2000_ex41c"
    source := ⟨"sorace-2000", "(41c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Paola ha nuotato con perfetto stile"
    glossedTokens := [("Paola", "Paola"), ("ha", "has"), ("nuotato", "swum"), ("con", "with"), ("perfetto", "perfect"), ("stile", "style")]
    glossedWords := [⟨['P', 'a', 'o', 'l', 'a'], ['P', 'a', 'o', 'l', 'a'], [⟨['P', 'a', 'o', 'l', 'a'], ['P', 'a', 'o', 'l', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['n', 'u', 'o', 't', 'a', 't', 'o'], ['s', 'w', 'u', 'm'], [⟨['n', 'u', 'o', 't', 'a', 't', 'o'], ['s', 'w', 'u', 'm'], none⟩]⟩, ⟨['c', 'o', 'n'], ['w', 'i', 't', 'h'], [⟨['c', 'o', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['p', 'e', 'r', 'f', 'e', 't', 't', 'o'], ['p', 'e', 'r', 'f', 'e', 'c', 't'], [⟨['p', 'e', 'r', 'f', 'e', 't', 't', 'o'], ['p', 'e', 'r', 'f', 'e', 'c', 't'], none⟩]⟩, ⟨['s', 't', 'i', 'l', 'e'], ['s', 't', 'y', 'l', 'e'], [⟨['s', 't', 'i', 'l', 'e'], ['s', 't', 'y', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Paola è nuotata con perfetto stile", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "nuotare"⟩]
    paperFeatures := [] }

def ex41d : Datum :=
  { id := "sorace2000_ex41d"
    source := ⟨"sorace-2000", "(41d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Paola ha nuotato a riva"
    glossedTokens := [("Paola", "Paola"), ("ha", "has"), ("nuotato", "swum"), ("a", "to"), ("riva", "the.shore")]
    glossedWords := [⟨['P', 'a', 'o', 'l', 'a'], ['P', 'a', 'o', 'l', 'a'], [⟨['P', 'a', 'o', 'l', 'a'], ['P', 'a', 'o', 'l', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['n', 'u', 'o', 't', 'a', 't', 'o'], ['s', 'w', 'u', 'm'], [⟨['n', 'u', 'o', 't', 'a', 't', 'o'], ['s', 'w', 'u', 'm'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['r', 'i', 'v', 'a'], ['t', 'h', 'e', '.', 's', 'h', 'o', 'r', 'e'], [⟨['r', 'i', 'v', 'a'], ['t', 'h', 'e', '.', 's', 'h', 'o', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Paola è nuotata a riva", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "nuotare"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex42a : Datum :=
  { id := "sorace2000_ex42a"
    source := ⟨"sorace-2000", "(42a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie a couru très vite"
    glossedTokens := [("Marie", "Marie"), ("a", "has"), ("couru", "run"), ("très", "very"), ("vite", "fast")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['a'], ['h', 'a', 's'], [⟨['a'], ['h', 'a', 's'], none⟩]⟩, ⟨['c', 'o', 'u', 'r', 'u'], ['r', 'u', 'n'], [⟨['c', 'o', 'u', 'r', 'u'], ['r', 'u', 'n'], none⟩]⟩, ⟨['t', 'r', 'è', 's'], ['v', 'e', 'r', 'y'], [⟨['t', 'r', 'è', 's'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['v', 'i', 't', 'e'], ['f', 'a', 's', 't'], [⟨['v', 'i', 't', 'e'], ['f', 'a', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Marie est courue très vite", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avoir"⟩, ⟨2, 1, "participle", some "courir"⟩]
    paperFeatures := [] }

def ex42b : Datum :=
  { id := "sorace2000_ex42b"
    source := ⟨"sorace-2000", "(42b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie a couru jusqu'à la maison"
    glossedTokens := [("Marie", "Marie"), ("a", "has"), ("couru", "run"), ("jusqu'à", "as.far.as"), ("la", "the"), ("maison", "house")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['a'], ['h', 'a', 's'], [⟨['a'], ['h', 'a', 's'], none⟩]⟩, ⟨['c', 'o', 'u', 'r', 'u'], ['r', 'u', 'n'], [⟨['c', 'o', 'u', 'r', 'u'], ['r', 'u', 'n'], none⟩]⟩, ⟨['j', 'u', 's', 'q', 'u', '\'', 'à'], ['a', 's', '.', 'f', 'a', 'r', '.', 'a', 's'], [⟨['j', 'u', 's', 'q', 'u', '\'', 'à'], ['a', 's', '.', 'f', 'a', 'r', '.', 'a', 's'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'a', 'i', 's', 'o', 'n'], ['h', 'o', 'u', 's', 'e'], [⟨['m', 'a', 'i', 's', 'o', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Marie est courue jusqu'à la maison", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avoir"⟩, ⟨2, 1, "participle", some "courir"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex43a : Datum :=
  { id := "sorace2000_ex43a"
    source := ⟨"sorace-2000", "(43a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "È corsa voce che Maria si sposa"
    glossedTokens := [("È", "is"), ("corsa", "run"), ("voce", "rumor"), ("che", "that"), ("Maria", "Maria"), ("si", "self"), ("sposa", "marries")]
    glossedWords := [⟨['È'], ['i', 's'], [⟨['È'], ['i', 's'], none⟩]⟩, ⟨['c', 'o', 'r', 's', 'a'], ['r', 'u', 'n'], [⟨['c', 'o', 'r', 's', 'a'], ['r', 'u', 'n'], none⟩]⟩, ⟨['v', 'o', 'c', 'e'], ['r', 'u', 'm', 'o', 'r'], [⟨['v', 'o', 'c', 'e'], ['r', 'u', 'm', 'o', 'r'], none⟩]⟩, ⟨['c', 'h', 'e'], ['t', 'h', 'a', 't'], [⟨['c', 'h', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['s', 'i'], ['s', 'e', 'l', 'f'], [⟨['s', 'i'], ['s', 'e', 'l', 'f'], none⟩]⟩, ⟨['s', 'p', 'o', 's', 'a'], ['m', 'a', 'r', 'r', 'i', 'e', 's'], [⟨['s', 'p', 'o', 's', 'a'], ['m', 'a', 'r', 'r', 'i', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ha corso voce che Maria si sposa", .marginal)]
    readings := []
    spans := [⟨0, 1, "auxiliary", some "essere"⟩, ⟨1, 1, "participle", some "correre"⟩]
    paperFeatures := [("subject", "nonagentive")] }

def ex43b : Datum :=
  { id := "sorace2000_ex43b"
    source := ⟨"sorace-2000", "(43b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "È saltato fuori che i magistrati erano corrotti"
    glossedTokens := [("È", "is"), ("saltato", "jumped"), ("fuori", "out"), ("che", "that"), ("i", "the"), ("magistrati", "magistrates"), ("erano", "were"), ("corrotti", "corrupted")]
    glossedWords := [⟨['È'], ['i', 's'], [⟨['È'], ['i', 's'], none⟩]⟩, ⟨['s', 'a', 'l', 't', 'a', 't', 'o'], ['j', 'u', 'm', 'p', 'e', 'd'], [⟨['s', 'a', 'l', 't', 'a', 't', 'o'], ['j', 'u', 'm', 'p', 'e', 'd'], none⟩]⟩, ⟨['f', 'u', 'o', 'r', 'i'], ['o', 'u', 't'], [⟨['f', 'u', 'o', 'r', 'i'], ['o', 'u', 't'], none⟩]⟩, ⟨['c', 'h', 'e'], ['t', 'h', 'a', 't'], [⟨['c', 'h', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 's', 't', 'r', 'a', 't', 'i'], ['m', 'a', 'g', 'i', 's', 't', 'r', 'a', 't', 'e', 's'], [⟨['m', 'a', 'g', 'i', 's', 't', 'r', 'a', 't', 'i'], ['m', 'a', 'g', 'i', 's', 't', 'r', 'a', 't', 'e', 's'], none⟩]⟩, ⟨['e', 'r', 'a', 'n', 'o'], ['w', 'e', 'r', 'e'], [⟨['e', 'r', 'a', 'n', 'o'], ['w', 'e', 'r', 'e'], none⟩]⟩, ⟨['c', 'o', 'r', 'r', 'o', 't', 't', 'i'], ['c', 'o', 'r', 'r', 'u', 'p', 't', 'e', 'd'], [⟨['c', 'o', 'r', 'r', 'o', 't', 't', 'i'], ['c', 'o', 'r', 'r', 'u', 'p', 't', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ha saltato fuori che i magistrati erano corrotti", .marginal)]
    readings := []
    spans := [⟨0, 1, "auxiliary", some "essere"⟩, ⟨1, 1, "participle", some "saltare"⟩]
    paperFeatures := [("subject", "nonagentive")] }

def ex44a : Datum :=
  { id := "sorace2000_ex44a"
    source := ⟨"sorace-2000", "(44a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il pilota ha atterrato sulla pista di emergenza"
    glossedTokens := [("Il", "the"), ("pilota", "pilot"), ("ha", "has"), ("atterrato", "landed"), ("sulla", "on.the"), ("pista", "runway"), ("di", "of"), ("emergenza", "emergency")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'i', 'l', 'o', 't', 'a'], ['p', 'i', 'l', 'o', 't'], [⟨['p', 'i', 'l', 'o', 't', 'a'], ['p', 'i', 'l', 'o', 't'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['a', 't', 't', 'e', 'r', 'r', 'a', 't', 'o'], ['l', 'a', 'n', 'd', 'e', 'd'], [⟨['a', 't', 't', 'e', 'r', 'r', 'a', 't', 'o'], ['l', 'a', 'n', 'd', 'e', 'd'], none⟩]⟩, ⟨['s', 'u', 'l', 'l', 'a'], ['o', 'n', '.', 't', 'h', 'e'], [⟨['s', 'u', 'l', 'l', 'a'], ['o', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['p', 'i', 's', 't', 'a'], ['r', 'u', 'n', 'w', 'a', 'y'], [⟨['p', 'i', 's', 't', 'a'], ['r', 'u', 'n', 'w', 'a', 'y'], none⟩]⟩, ⟨['d', 'i'], ['o', 'f'], [⟨['d', 'i'], ['o', 'f'], none⟩]⟩, ⟨['e', 'm', 'e', 'r', 'g', 'e', 'n', 'z', 'a'], ['e', 'm', 'e', 'r', 'g', 'e', 'n', 'c', 'y'], [⟨['e', 'm', 'e', 'r', 'g', 'e', 'n', 'z', 'a'], ['e', 'm', 'e', 'r', 'g', 'e', 'n', 'c', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il pilota è atterrato sulla pista di emergenza", .marginal)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "atterrare"⟩]
    paperFeatures := [] }

def ex44b : Datum :=
  { id := "sorace2000_ex44b"
    source := ⟨"sorace-2000", "(44b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'aereo è atterrato sulla pista di emergenza"
    glossedTokens := [("L'aereo", "the.plane"), ("è", "is"), ("atterrato", "landed"), ("sulla", "on.the"), ("pista", "runway"), ("di", "of"), ("emergenza", "emergency")]
    glossedWords := [⟨['L', '\'', 'a', 'e', 'r', 'e', 'o'], ['t', 'h', 'e', '.', 'p', 'l', 'a', 'n', 'e'], [⟨['L', '\'', 'a', 'e', 'r', 'e', 'o'], ['t', 'h', 'e', '.', 'p', 'l', 'a', 'n', 'e'], none⟩]⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['a', 't', 't', 'e', 'r', 'r', 'a', 't', 'o'], ['l', 'a', 'n', 'd', 'e', 'd'], [⟨['a', 't', 't', 'e', 'r', 'r', 'a', 't', 'o'], ['l', 'a', 'n', 'd', 'e', 'd'], none⟩]⟩, ⟨['s', 'u', 'l', 'l', 'a'], ['o', 'n', '.', 't', 'h', 'e'], [⟨['s', 'u', 'l', 'l', 'a'], ['o', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['p', 'i', 's', 't', 'a'], ['r', 'u', 'n', 'w', 'a', 'y'], [⟨['p', 'i', 's', 't', 'a'], ['r', 'u', 'n', 'w', 'a', 'y'], none⟩]⟩, ⟨['d', 'i'], ['o', 'f'], [⟨['d', 'i'], ['o', 'f'], none⟩]⟩, ⟨['e', 'm', 'e', 'r', 'g', 'e', 'n', 'z', 'a'], ['e', 'm', 'e', 'r', 'g', 'e', 'n', 'c', 'y'], [⟨['e', 'm', 'e', 'r', 'g', 'e', 'n', 'z', 'a'], ['e', 'm', 'e', 'r', 'g', 'e', 'n', 'c', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("L'aereo ha atterrato sulla pista di emergenza", .marginal)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "atterrare"⟩]
    paperFeatures := [("subject", "nonagentive")] }

def ex45a : Datum :=
  { id := "sorace2000_ex45a"
    source := ⟨"sorace-2000", "(45a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La fede religiosa ha tentennato anche nei più forti"
    glossedTokens := [("La", "the"), ("fede", "faith"), ("religiosa", "religious"), ("ha", "has"), ("tentennato", "wavered"), ("anche", "even"), ("nei", "in.the"), ("più forti", "strongest")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'e', 'd', 'e'], ['f', 'a', 'i', 't', 'h'], [⟨['f', 'e', 'd', 'e'], ['f', 'a', 'i', 't', 'h'], none⟩]⟩, ⟨['r', 'e', 'l', 'i', 'g', 'i', 'o', 's', 'a'], ['r', 'e', 'l', 'i', 'g', 'i', 'o', 'u', 's'], [⟨['r', 'e', 'l', 'i', 'g', 'i', 'o', 's', 'a'], ['r', 'e', 'l', 'i', 'g', 'i', 'o', 'u', 's'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['t', 'e', 'n', 't', 'e', 'n', 'n', 'a', 't', 'o'], ['w', 'a', 'v', 'e', 'r', 'e', 'd'], [⟨['t', 'e', 'n', 't', 'e', 'n', 'n', 'a', 't', 'o'], ['w', 'a', 'v', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['a', 'n', 'c', 'h', 'e'], ['e', 'v', 'e', 'n'], [⟨['a', 'n', 'c', 'h', 'e'], ['e', 'v', 'e', 'n'], none⟩]⟩, ⟨['n', 'e', 'i'], ['i', 'n', '.', 't', 'h', 'e'], [⟨['n', 'e', 'i'], ['i', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['p', 'i', 'ù', ' ', 'f', 'o', 'r', 't', 'i'], ['s', 't', 'r', 'o', 'n', 'g', 'e', 's', 't'], [⟨['p', 'i', 'ù', ' ', 'f', 'o', 'r', 't', 'i'], ['s', 't', 'r', 'o', 'n', 'g', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La fede religiosa è tentennata anche nei più forti", .questionable)]
    readings := []
    spans := [⟨3, 1, "auxiliary", some "avere"⟩, ⟨4, 1, "participle", some "tentennare"⟩]
    paperFeatures := [] }

def ex45b : Datum :=
  { id := "sorace2000_ex45b"
    source := ⟨"sorace-2000", "(45b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Paolo ha tentennato a lungo prima di decidersi"
    glossedTokens := [("Paolo", "Paolo"), ("ha", "has"), ("tentennato", "wavered"), ("a", "for"), ("lungo", "long"), ("prima", "before"), ("di", "of"), ("decidersi", "decide-self")]
    glossedWords := [⟨['P', 'a', 'o', 'l', 'o'], ['P', 'a', 'o', 'l', 'o'], [⟨['P', 'a', 'o', 'l', 'o'], ['P', 'a', 'o', 'l', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['t', 'e', 'n', 't', 'e', 'n', 'n', 'a', 't', 'o'], ['w', 'a', 'v', 'e', 'r', 'e', 'd'], [⟨['t', 'e', 'n', 't', 'e', 'n', 'n', 'a', 't', 'o'], ['w', 'a', 'v', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['a'], ['f', 'o', 'r'], [⟨['a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['l', 'u', 'n', 'g', 'o'], ['l', 'o', 'n', 'g'], [⟨['l', 'u', 'n', 'g', 'o'], ['l', 'o', 'n', 'g'], none⟩]⟩, ⟨['p', 'r', 'i', 'm', 'a'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['p', 'r', 'i', 'm', 'a'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['d', 'i'], ['o', 'f'], [⟨['d', 'i'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e', 'c', 'i', 'd', 'e', 'r', 's', 'i'], ['d', 'e', 'c', 'i', 'd', 'e', '-', 's', 'e', 'l', 'f'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Paolo è tentennato a lungo prima di decidersi", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "tentennare"⟩]
    paperFeatures := [("subject", "agentive")] }

def ex46a : Datum :=
  { id := "sorace2000_ex46a"
    source := ⟨"sorace-2000", "(46a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mario ha tossito"
    glossedTokens := [("Mario", "Mario"), ("ha", "has"), ("tossito", "coughed")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['t', 'o', 's', 's', 'i', 't', 'o'], ['c', 'o', 'u', 'g', 'h', 'e', 'd'], [⟨['t', 'o', 's', 's', 'i', 't', 'o'], ['c', 'o', 'u', 'g', 'h', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Mario è tossito", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "tossire"⟩]
    paperFeatures := [] }

def ex46b : Datum :=
  { id := "sorace2000_ex46b"
    source := ⟨"sorace-2000", "(46b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mario ha tossito apposta per attirare l'attenzione."
    glossedTokens := [("Mario", "Mario"), ("ha", "has"), ("tossito", "coughed"), ("apposta", "on.purpose"), ("per", "to"), ("attirare", "attract"), ("l'attenzione", "the.attention")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['t', 'o', 's', 's', 'i', 't', 'o'], ['c', 'o', 'u', 'g', 'h', 'e', 'd'], [⟨['t', 'o', 's', 's', 'i', 't', 'o'], ['c', 'o', 'u', 'g', 'h', 'e', 'd'], none⟩]⟩, ⟨['a', 'p', 'p', 'o', 's', 't', 'a'], ['o', 'n', '.', 'p', 'u', 'r', 'p', 'o', 's', 'e'], [⟨['a', 'p', 'p', 'o', 's', 't', 'a'], ['o', 'n', '.', 'p', 'u', 'r', 'p', 'o', 's', 'e'], none⟩]⟩, ⟨['p', 'e', 'r'], ['t', 'o'], [⟨['p', 'e', 'r'], ['t', 'o'], none⟩]⟩, ⟨['a', 't', 't', 'i', 'r', 'a', 'r', 'e'], ['a', 't', 't', 'r', 'a', 'c', 't'], [⟨['a', 't', 't', 'i', 'r', 'a', 'r', 'e'], ['a', 't', 't', 'r', 'a', 'c', 't'], none⟩]⟩, ⟨['l', '\'', 'a', 't', 't', 'e', 'n', 'z', 'i', 'o', 'n', 'e'], ['t', 'h', 'e', '.', 'a', 't', 't', 'e', 'n', 't', 'i', 'o', 'n'], [⟨['l', '\'', 'a', 't', 't', 'e', 'n', 'z', 'i', 'o', 'n', 'e'], ['t', 'h', 'e', '.', 'a', 't', 't', 'e', 'n', 't', 'i', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "tossire"⟩]
    paperFeatures := [("subject", "agentive")] }

def ex47a : Datum :=
  { id := "sorace2000_ex47a"
    source := ⟨"sorace-2000", "(47a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il telefono ha squillato."
    glossedTokens := [("Il", "the"), ("telefono", "telephone"), ("ha", "has"), ("squillato", "rung")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'o'], ['t', 'e', 'l', 'e', 'p', 'h', 'o', 'n', 'e'], [⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'o'], ['t', 'e', 'l', 'e', 'p', 'h', 'o', 'n', 'e'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'q', 'u', 'i', 'l', 'l', 'a', 't', 'o'], ['r', 'u', 'n', 'g'], [⟨['s', 'q', 'u', 'i', 'l', 'l', 'a', 't', 'o'], ['r', 'u', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il telefono è squillato.", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "squillare"⟩]
    paperFeatures := [] }

def ex47b : Datum :=
  { id := "sorace2000_ex47b"
    source := ⟨"sorace-2000", "(47b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'eco ha risuonato nella caverna"
    glossedTokens := [("L'eco", "the.echo"), ("ha", "has"), ("risuonato", "resounded"), ("nella", "in.the"), ("caverna", "cave")]
    glossedWords := [⟨['L', '\'', 'e', 'c', 'o'], ['t', 'h', 'e', '.', 'e', 'c', 'h', 'o'], [⟨['L', '\'', 'e', 'c', 'o'], ['t', 'h', 'e', '.', 'e', 'c', 'h', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['r', 'i', 's', 'u', 'o', 'n', 'a', 't', 'o'], ['r', 'e', 's', 'o', 'u', 'n', 'd', 'e', 'd'], [⟨['r', 'i', 's', 'u', 'o', 'n', 'a', 't', 'o'], ['r', 'e', 's', 'o', 'u', 'n', 'd', 'e', 'd'], none⟩]⟩, ⟨['n', 'e', 'l', 'l', 'a'], ['i', 'n', '.', 't', 'h', 'e'], [⟨['n', 'e', 'l', 'l', 'a'], ['i', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'v', 'e', 'r', 'n', 'a'], ['c', 'a', 'v', 'e'], [⟨['c', 'a', 'v', 'e', 'r', 'n', 'a'], ['c', 'a', 'v', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("L'eco è risuonato nella caverna", .acceptable)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "risuonare"⟩]
    paperFeatures := [] }

def ex47c : Datum :=
  { id := "sorace2000_ex47c"
    source := ⟨"sorace-2000", "(47c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Il tuono ha rimbombato"
    glossedTokens := [("Il", "the"), ("tuono", "thunder"), ("ha", "has"), ("rimbombato", "rumbled")]
    glossedWords := [⟨['I', 'l'], ['t', 'h', 'e'], [⟨['I', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'u', 'o', 'n', 'o'], ['t', 'h', 'u', 'n', 'd', 'e', 'r'], [⟨['t', 'u', 'o', 'n', 'o'], ['t', 'h', 'u', 'n', 'd', 'e', 'r'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['r', 'i', 'm', 'b', 'o', 'm', 'b', 'a', 't', 'o'], ['r', 'u', 'm', 'b', 'l', 'e', 'd'], [⟨['r', 'i', 'm', 'b', 'o', 'm', 'b', 'a', 't', 'o'], ['r', 'u', 'm', 'b', 'l', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Il tuono è rimbombato", .acceptable)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "rimbombare"⟩]
    paperFeatures := [] }

def ex47d : Datum :=
  { id := "sorace2000_ex47d"
    source := ⟨"sorace-2000", "(47d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La campana ha rintoccato"
    glossedTokens := [("La", "the"), ("campana", "bell"), ("ha", "has"), ("rintoccato", "tolled")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'm', 'p', 'a', 'n', 'a'], ['b', 'e', 'l', 'l'], [⟨['c', 'a', 'm', 'p', 'a', 'n', 'a'], ['b', 'e', 'l', 'l'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['r', 'i', 'n', 't', 'o', 'c', 'c', 'a', 't', 'o'], ['t', 'o', 'l', 'l', 'e', 'd'], [⟨['r', 'i', 'n', 't', 'o', 'c', 'c', 'a', 't', 'o'], ['t', 'o', 'l', 'l', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("La campana è rintoccata", .marginal)]
    readings := []
    spans := [⟨2, 1, "auxiliary", some "avere"⟩, ⟨3, 1, "participle", some "rintoccare"⟩]
    paperFeatures := [] }

def ex48_piovere : Datum :=
  { id := "sorace2000_ex48_piovere"
    source := ⟨"sorace-2000", "(48)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ha piovuto tutto il giorno"
    glossedTokens := [("Ieri", "yesterday"), ("ha", "has"), ("piovuto", "rained"), ("tutto", "all"), ("il", "the"), ("giorno", "day")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['p', 'i', 'o', 'v', 'u', 't', 'o'], ['r', 'a', 'i', 'n', 'e', 'd'], [⟨['p', 'i', 'o', 'v', 'u', 't', 'o'], ['r', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩, ⟨['t', 'u', 't', 't', 'o'], ['a', 'l', 'l'], [⟨['t', 'u', 't', 't', 'o'], ['a', 'l', 'l'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'i', 'o', 'r', 'n', 'o'], ['d', 'a', 'y'], [⟨['g', 'i', 'o', 'r', 'n', 'o'], ['d', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ieri è piovuto tutto il giorno", .acceptable)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "piovere"⟩]
    paperFeatures := [] }

def ex48_nevicare : Datum :=
  { id := "sorace2000_ex48_nevicare"
    source := ⟨"sorace-2000", "(48)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ha nevicato tutto il giorno"
    glossedTokens := [("Ieri", "yesterday"), ("ha", "has"), ("nevicato", "snowed"), ("tutto", "all"), ("il", "the"), ("giorno", "day")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['n', 'e', 'v', 'i', 'c', 'a', 't', 'o'], ['s', 'n', 'o', 'w', 'e', 'd'], [⟨['n', 'e', 'v', 'i', 'c', 'a', 't', 'o'], ['s', 'n', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['t', 'u', 't', 't', 'o'], ['a', 'l', 'l'], [⟨['t', 'u', 't', 't', 'o'], ['a', 'l', 'l'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'i', 'o', 'r', 'n', 'o'], ['d', 'a', 'y'], [⟨['g', 'i', 'o', 'r', 'n', 'o'], ['d', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ieri è nevicato tutto il giorno", .acceptable)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "nevicare"⟩]
    paperFeatures := [] }

def ex48_grandinare : Datum :=
  { id := "sorace2000_ex48_grandinare"
    source := ⟨"sorace-2000", "(48)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri ha grandinato tutto il giorno"
    glossedTokens := [("Ieri", "yesterday"), ("ha", "has"), ("grandinato", "hailed"), ("tutto", "all"), ("il", "the"), ("giorno", "day")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['g', 'r', 'a', 'n', 'd', 'i', 'n', 'a', 't', 'o'], ['h', 'a', 'i', 'l', 'e', 'd'], [⟨['g', 'r', 'a', 'n', 'd', 'i', 'n', 'a', 't', 'o'], ['h', 'a', 'i', 'l', 'e', 'd'], none⟩]⟩, ⟨['t', 'u', 't', 't', 'o'], ['a', 'l', 'l'], [⟨['t', 'u', 't', 't', 'o'], ['a', 'l', 'l'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'i', 'o', 'r', 'n', 'o'], ['d', 'a', 'y'], [⟨['g', 'i', 'o', 'r', 'n', 'o'], ['d', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ieri è grandinato tutto il giorno", .acceptable)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "grandinare"⟩]
    paperFeatures := [] }

def ex49 : Datum :=
  { id := "sorace2000_ex49"
    source := ⟨"sorace-2000", "(49)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi è piovuto sulla testa"
    glossedTokens := [("Mi", "to-me"), ("è", "is"), ("piovuto", "rained"), ("sulla", "on.the"), ("testa", "head")]
    glossedWords := [⟨['M', 'i'], ['t', 'o', '-', 'm', 'e'], []⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['p', 'i', 'o', 'v', 'u', 't', 'o'], ['r', 'a', 'i', 'n', 'e', 'd'], [⟨['p', 'i', 'o', 'v', 'u', 't', 'o'], ['r', 'a', 'i', 'n', 'e', 'd'], none⟩]⟩, ⟨['s', 'u', 'l', 'l', 'a'], ['o', 'n', '.', 't', 'h', 'e'], [⟨['s', 'u', 'l', 'l', 'a'], ['o', 'n', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 's', 't', 'a'], ['h', 'e', 'a', 'd'], [⟨['t', 'e', 's', 't', 'a'], ['h', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Mi ha piovuto sulla testa", .ungrammatical)]
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "piovere"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex50a : Datum :=
  { id := "sorace2000_ex50a"
    source := ⟨"sorace-2000", "(50a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ha tuonato molto durante il temporale"
    glossedTokens := [("Ha", "has.3SG"), ("tuonato", "thundered"), ("molto", "a.lot"), ("durante", "during"), ("il", "the"), ("temporale", "storm")]
    glossedWords := [⟨['H', 'a'], ['h', 'a', 's', '.', '3', 'S', 'G'], [⟨['H', 'a'], ['h', 'a', 's', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'u', 'o', 'n', 'a', 't', 'o'], ['t', 'h', 'u', 'n', 'd', 'e', 'r', 'e', 'd'], [⟨['t', 'u', 'o', 'n', 'a', 't', 'o'], ['t', 'h', 'u', 'n', 'd', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['m', 'o', 'l', 't', 'o'], ['a', '.', 'l', 'o', 't'], [⟨['m', 'o', 'l', 't', 'o'], ['a', '.', 'l', 'o', 't'], none⟩]⟩, ⟨['d', 'u', 'r', 'a', 'n', 't', 'e'], ['d', 'u', 'r', 'i', 'n', 'g'], [⟨['d', 'u', 'r', 'a', 'n', 't', 'e'], ['d', 'u', 'r', 'i', 'n', 'g'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 'm', 'p', 'o', 'r', 'a', 'l', 'e'], ['s', 't', 'o', 'r', 'm'], [⟨['t', 'e', 'm', 'p', 'o', 'r', 'a', 'l', 'e'], ['s', 't', 'o', 'r', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("È tuonato molto durante il temporale", .marginal)]
    readings := []
    spans := [⟨0, 1, "auxiliary", some "avere"⟩, ⟨1, 1, "participle", some "tuonare"⟩]
    paperFeatures := [] }

def ex50b : Datum :=
  { id := "sorace2000_ex50b"
    source := ⟨"sorace-2000", "(50b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ha lampeggiato all'improvviso"
    glossedTokens := [("Ha", "has.3SG"), ("lampeggiato", "flashed.lightning"), ("all'improvviso", "suddenly")]
    glossedWords := [⟨['H', 'a'], ['h', 'a', 's', '.', '3', 'S', 'G'], [⟨['H', 'a'], ['h', 'a', 's', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'a', 'm', 'p', 'e', 'g', 'g', 'i', 'a', 't', 'o'], ['f', 'l', 'a', 's', 'h', 'e', 'd', '.', 'l', 'i', 'g', 'h', 't', 'n', 'i', 'n', 'g'], [⟨['l', 'a', 'm', 'p', 'e', 'g', 'g', 'i', 'a', 't', 'o'], ['f', 'l', 'a', 's', 'h', 'e', 'd', '.', 'l', 'i', 'g', 'h', 't', 'n', 'i', 'n', 'g'], none⟩]⟩, ⟨['a', 'l', 'l', '\'', 'i', 'm', 'p', 'r', 'o', 'v', 'v', 'i', 's', 'o'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], [⟨['a', 'l', 'l', '\'', 'i', 'm', 'p', 'r', 'o', 'v', 'v', 'i', 's', 'o'], ['s', 'u', 'd', 'd', 'e', 'n', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("È lampeggiato all'improvviso", .marginal)]
    readings := []
    spans := [⟨0, 1, "auxiliary", some "avere"⟩, ⟨1, 1, "participle", some "lampeggiare"⟩]
    paperFeatures := [] }

def ex51_tuonare : Datum :=
  { id := "sorace2000_ex51_tuonare"
    source := ⟨"sorace-2000", "(51)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ci è tuonato sopra"
    glossedTokens := [("Ci", "to-us"), ("è", "is"), ("tuonato", "thundered"), ("sopra", "over")]
    glossedWords := [⟨['C', 'i'], ['t', 'o', '-', 'u', 's'], []⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['t', 'u', 'o', 'n', 'a', 't', 'o'], ['t', 'h', 'u', 'n', 'd', 'e', 'r', 'e', 'd'], [⟨['t', 'u', 'o', 'n', 'a', 't', 'o'], ['t', 'h', 'u', 'n', 'd', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['s', 'o', 'p', 'r', 'a'], ['o', 'v', 'e', 'r'], [⟨['s', 'o', 'p', 'r', 'a'], ['o', 'v', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "tuonare"⟩]
    paperFeatures := [("predicate", "telicized")] }

def ex51_lampeggiare : Datum :=
  { id := "sorace2000_ex51_lampeggiare"
    source := ⟨"sorace-2000", "(51)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ci è lampeggiato sopra"
    glossedTokens := [("Ci", "to-us"), ("è", "is"), ("lampeggiato", "flashed.lightning"), ("sopra", "over")]
    glossedWords := [⟨['C', 'i'], ['t', 'o', '-', 'u', 's'], []⟩, ⟨['è'], ['i', 's'], [⟨['è'], ['i', 's'], none⟩]⟩, ⟨['l', 'a', 'm', 'p', 'e', 'g', 'g', 'i', 'a', 't', 'o'], ['f', 'l', 'a', 's', 'h', 'e', 'd', '.', 'l', 'i', 'g', 'h', 't', 'n', 'i', 'n', 'g'], [⟨['l', 'a', 'm', 'p', 'e', 'g', 'g', 'i', 'a', 't', 'o'], ['f', 'l', 'a', 's', 'h', 'e', 'd', '.', 'l', 'i', 'g', 'h', 't', 'n', 'i', 'n', 'g'], none⟩]⟩, ⟨['s', 'o', 'p', 'r', 'a'], ['o', 'v', 'e', 'r'], [⟨['s', 'o', 'p', 'r', 'a'], ['o', 'v', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "lampeggiare"⟩]
    paperFeatures := [("predicate", "telicized")] }

def all : List Datum := [ex1a, ex1b, ex1c, ex1d, ex4, ex5a, ex5b, ex30a, ex7a, ex7b, ex8a, ex9a, ex9b, ex9c, ex10a, ex10b, ex11, ex12, ex13, ex14a, ex14c, ex15a, ex15b, ex15c, ex16, ex17a, ex17b, ex18a, ex18b, ex19a, ex19b, ex19c, ex20a, ex20b, ex20c, ex21a, ex21b, ex21c, ex22, ex23a, ex23b, ex23c, ex23d, ex24a, ex24b, ex24c, ex25a, ex25b, ex33a, ex33b, ex33c, ex33d, ex34, ex35, ex36a, ex36b, ex37a, ex37b, ex37c, ex38_rennen, ex38_laufen, ex38_schwimmen, ex39a, ex39b, ex40a, ex40b, ex41a, ex41b, ex41c, ex41d, ex42a, ex42b, ex43a, ex43b, ex44a, ex44b, ex45a, ex45b, ex46a, ex46b, ex47a, ex47b, ex47c, ex47d, ex48_piovere, ex48_nevicare, ex48_grandinare, ex49, ex50a, ex50b, ex51_tuonare, ex51_lampeggiare]

/-- A phrase that changes the telicity of the predicate, where the paper points to one. -/
inductive PredicateShift where
  /-- telicized: a directional or bounding phrase makes the predicate telic -/
  | telicized
  /-- detelicized: a durative adverbial makes the predicate atelic -/
  | detelicized
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `predicate`. -/
def predicate (e : Datum) : Option PredicateShift :=
  e.parse? "predicate" [("telicized", .telicized), ("detelicized", .detelicized)]

/-- The agentivity of the subject, where the paper points to it as departing from the default of the verb's type. -/
inductive SubjectShift where
  /-- agentive: the subject acts on purpose -/
  | agentive
  /-- nonagentive: the subject is inanimate, sentential or not in control -/
  | nonagentive
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option SubjectShift :=
  e.parse? "subject" [("agentive", .agentive), ("nonagentive", .nonagentive)]

/-- The words a row marks. -/
inductive SpanLabel where
  /-- auxiliary: the auxiliary of the perfect -/
  | auxiliary
  /-- participle: the past participle of the verb under test -/
  | participle
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("auxiliary", .auxiliary), ("participle", .participle)]

/-- The auxiliaries and the verbs of the rows. -/
inductive Lexeme where
  /-- essere: *essere* 'be', the Italian auxiliary of the perfect with *be* -/
  | essere
  /-- venire: *venire* 'come' -/
  | venire
  /-- être: *être* 'be', the French auxiliary of the perfect with *be* -/
  | etre
  /-- arriver: *arriver* 'arrive' -/
  | arriver
  /-- zijn: *zijn* 'be' -/
  | zijn
  /-- komen: *komen* 'arrive' -/
  | komen
  /-- sein: *sein* 'be' -/
  | sein
  /-- ankommen: *ankommen* 'arrive' -/
  | ankommen
  /-- arrivare: *arrivare* 'arrive' -/
  | arrivare
  /-- cadere: *cadere* 'fall' -/
  | cadere
  /-- avere: *avere* 'have', the Italian auxiliary of the perfect with *have* -/
  | avere
  /-- salire: *salire* 'rise' -/
  | salire
  /-- marcire: *marcire* 'rot' -/
  | marcire
  /-- fiorire: *fiorire* 'blossom' -/
  | fiorire
  /-- naître: *naître* 'be born' -/
  | naitre
  /-- sterven: *sterven* 'die' -/
  | sterven
  /-- gebären: *gebären* 'give birth', whose participle *geboren* is 'born' -/
  | gebaren
  /-- groeien: *groeien* 'grow' -/
  | groeien
  /-- steigen: *steigen* 'rise' -/
  | steigen
  /-- stijgen: *stijgen* 'rise' -/
  | stijgen
  /-- devenir: *devenir* 'become' -/
  | devenir
  /-- avoir: *avoir* 'have', the French auxiliary of the perfect with *have* -/
  | avoir
  /-- rougir: *rougir* 'blush' -/
  | rougir
  /-- paraître: *paraître* 'appear' -/
  | paraitre
  /-- échapper: *échapper* 'escape' -/
  | echapper
  /-- rimanere: *rimanere* 'remain' -/
  | rimanere
  /-- durare: *durare* 'last' -/
  | durare
  /-- survivre: *survivre* 'survive' -/
  | survivre
  /-- haben: *haben* 'have', the German auxiliary of the perfect with *have* -/
  | haben
  /-- halten: *halten* 'last' -/
  | halten
  /-- verweilen: *verweilen* 'stay' -/
  | verweilen
  /-- overblijven: *overblijven* 'remain' -/
  | overblijven
  /-- hebben: *hebben* 'have', the Dutch auxiliary of the perfect with *have* -/
  | hebben
  /-- duren: *duren* 'last' -/
  | duren
  /-- rester: *rester* 'remain' -/
  | rester
  /-- blijven: *blijven* 'remain' -/
  | blijven
  /-- bleiben: *bleiben* 'remain' -/
  | bleiben
  /-- esistere: *esistere* 'exist' -/
  | esistere
  /-- bastare: *bastare* 'suffice' -/
  | bastare
  /-- sembrare: *sembrare* 'seem' -/
  | sembrare
  /-- appartenere: *appartenere* 'belong' -/
  | appartenere
  /-- scarseggiare: *scarseggiare* 'run short' -/
  | scarseggiare
  /-- exister: *exister* 'exist' -/
  | exister
  /-- gefallen: *gefallen* 'please' -/
  | gefallen
  /-- genügen: *genügen* 'suffice' -/
  | genugen
  /-- liegen: *liegen* 'lie' -/
  | liegen
  /-- abhängen: *abhängen* 'depend' -/
  | abhangen
  /-- staan: *staan* 'stand' -/
  | staan
  /-- bestaan: *bestaan* 'exist' -/
  | bestaan
  /-- blijken: *blijken* 'seem' -/
  | blijken
  /-- chiacchierare: *chiacchierare* 'chat' -/
  | chiacchierare
  /-- travailler: *travailler* 'work' -/
  | travailler
  /-- blazen: *blazen* 'blow' -/
  | blazen
  /-- arbeiten: *arbeiten* 'work' -/
  | arbeiten
  /-- funzionare: *funzionare* 'function' -/
  | funzionare
  /-- lavorare: *lavorare* 'work' -/
  | lavorare
  /-- cedere: *cedere* 'yield' -/
  | cedere
  /-- correre: *correre* 'run' -/
  | correre
  /-- lopen: *lopen* 'run' -/
  | lopen
  /-- nager: *nager* 'swim' -/
  | nager
  /-- rennen: *rennen* 'run' -/
  | rennen
  /-- laufen: *laufen* 'walk' -/
  | laufen
  /-- schwimmen: *schwimmen* 'swim' -/
  | schwimmen
  /-- rollen: *rollen* 'roll' -/
  | rollen
  /-- tanzen: *tanzen* 'dance' -/
  | tanzen
  /-- nuotare: *nuotare* 'swim' -/
  | nuotare
  /-- courir: *courir* 'run' -/
  | courir
  /-- saltare: *saltare* 'jump' -/
  | saltare
  /-- atterrare: *atterrare* 'land' -/
  | atterrare
  /-- tentennare: *tentennare* 'waver' -/
  | tentennare
  /-- tossire: *tossire* 'cough' -/
  | tossire
  /-- squillare: *squillare* 'ring' -/
  | squillare
  /-- risuonare: *risuonare* 'resound' -/
  | risuonare
  /-- rimbombare: *rimbombare* 'rumble' -/
  | rimbombare
  /-- rintoccare: *rintoccare* 'toll' -/
  | rintoccare
  /-- piovere: *piovere* 'rain' -/
  | piovere
  /-- nevicare: *nevicare* 'snow' -/
  | nevicare
  /-- grandinare: *grandinare* 'hail' -/
  | grandinare
  /-- tuonare: *tuonare* 'thunder' -/
  | tuonare
  /-- lampeggiare: *lampeggiare* 'flash with lightning' -/
  | lampeggiare
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("essere", .essere), ("venire", .venire), ("être", .etre), ("arriver", .arriver), ("zijn", .zijn), ("komen", .komen), ("sein", .sein), ("ankommen", .ankommen), ("arrivare", .arrivare), ("cadere", .cadere), ("avere", .avere), ("salire", .salire), ("marcire", .marcire), ("fiorire", .fiorire), ("naître", .naitre), ("sterven", .sterven), ("gebären", .gebaren), ("groeien", .groeien), ("steigen", .steigen), ("stijgen", .stijgen), ("devenir", .devenir), ("avoir", .avoir), ("rougir", .rougir), ("paraître", .paraitre), ("échapper", .echapper), ("rimanere", .rimanere), ("durare", .durare), ("survivre", .survivre), ("haben", .haben), ("halten", .halten), ("verweilen", .verweilen), ("overblijven", .overblijven), ("hebben", .hebben), ("duren", .duren), ("rester", .rester), ("blijven", .blijven), ("bleiben", .bleiben), ("esistere", .esistere), ("bastare", .bastare), ("sembrare", .sembrare), ("appartenere", .appartenere), ("scarseggiare", .scarseggiare), ("exister", .exister), ("gefallen", .gefallen), ("genügen", .genugen), ("liegen", .liegen), ("abhängen", .abhangen), ("staan", .staan), ("bestaan", .bestaan), ("blijken", .blijken), ("chiacchierare", .chiacchierare), ("travailler", .travailler), ("blazen", .blazen), ("arbeiten", .arbeiten), ("funzionare", .funzionare), ("lavorare", .lavorare), ("cedere", .cedere), ("correre", .correre), ("lopen", .lopen), ("nager", .nager), ("rennen", .rennen), ("laufen", .laufen), ("schwimmen", .schwimmen), ("rollen", .rollen), ("tanzen", .tanzen), ("nuotare", .nuotare), ("courir", .courir), ("saltare", .saltare), ("atterrare", .atterrare), ("tentennare", .tentennare), ("tossire", .tossire), ("squillare", .squillare), ("risuonare", .risuonare), ("rimbombare", .rimbombare), ("rintoccare", .rintoccare), ("piovere", .piovere), ("nevicare", .nevicare), ("grandinare", .grandinare), ("tuonare", .tuonare), ("lampeggiare", .lampeggiare)])

/-- The examples of the paper. -/
inductive Example where
  | ex1a
  | ex1b
  | ex1c
  | ex1d
  | ex4
  | ex5a
  | ex5b
  | ex30a
  | ex7a
  | ex7b
  | ex8a
  | ex9a
  | ex9b
  | ex9c
  | ex10a
  | ex10b
  | ex11
  | ex12
  | ex13
  | ex14a
  | ex14c
  | ex15a
  | ex15b
  | ex15c
  | ex16
  | ex17a
  | ex17b
  | ex18a
  | ex18b
  | ex19a
  | ex19b
  | ex19c
  | ex20a
  | ex20b
  | ex20c
  | ex21a
  | ex21b
  | ex21c
  | ex22
  | ex23a
  | ex23b
  | ex23c
  | ex23d
  | ex24a
  | ex24b
  | ex24c
  | ex25a
  | ex25b
  | ex33a
  | ex33b
  | ex33c
  | ex33d
  | ex34
  | ex35
  | ex36a
  | ex36b
  | ex37a
  | ex37b
  | ex37c
  | ex38_rennen
  | ex38_laufen
  | ex38_schwimmen
  | ex39a
  | ex39b
  | ex40a
  | ex40b
  | ex41a
  | ex41b
  | ex41c
  | ex41d
  | ex42a
  | ex42b
  | ex43a
  | ex43b
  | ex44a
  | ex44b
  | ex45a
  | ex45b
  | ex46a
  | ex46b
  | ex47a
  | ex47b
  | ex47c
  | ex47d
  | ex48_piovere
  | ex48_nevicare
  | ex48_grandinare
  | ex49
  | ex50a
  | ex50b
  | ex51_tuonare
  | ex51_lampeggiare
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex1a, .ex1b, .ex1c, .ex1d, .ex4, .ex5a, .ex5b, .ex30a, .ex7a, .ex7b, .ex8a, .ex9a, .ex9b,
    .ex9c, .ex10a, .ex10b, .ex11, .ex12, .ex13, .ex14a, .ex14c, .ex15a, .ex15b, .ex15c, .ex16,
    .ex17a, .ex17b, .ex18a, .ex18b, .ex19a, .ex19b, .ex19c, .ex20a, .ex20b, .ex20c, .ex21a,
    .ex21b, .ex21c, .ex22, .ex23a, .ex23b, .ex23c, .ex23d, .ex24a, .ex24b, .ex24c, .ex25a, .ex25b,
    .ex33a, .ex33b, .ex33c, .ex33d, .ex34, .ex35, .ex36a, .ex36b, .ex37a, .ex37b, .ex37c,
    .ex38_rennen, .ex38_laufen, .ex38_schwimmen, .ex39a, .ex39b, .ex40a, .ex40b, .ex41a, .ex41b,
    .ex41c, .ex41d, .ex42a, .ex42b, .ex43a, .ex43b, .ex44a, .ex44b, .ex45a, .ex45b, .ex46a,
    .ex46b, .ex47a, .ex47b, .ex47c, .ex47d, .ex48_piovere, .ex48_nevicare, .ex48_grandinare,
    .ex49, .ex50a, .ex50b, .ex51_tuonare, .ex51_lampeggiare]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex1a => _root_.Sorace2000.Examples.ex1a
  | .ex1b => _root_.Sorace2000.Examples.ex1b
  | .ex1c => _root_.Sorace2000.Examples.ex1c
  | .ex1d => _root_.Sorace2000.Examples.ex1d
  | .ex4 => _root_.Sorace2000.Examples.ex4
  | .ex5a => _root_.Sorace2000.Examples.ex5a
  | .ex5b => _root_.Sorace2000.Examples.ex5b
  | .ex30a => _root_.Sorace2000.Examples.ex30a
  | .ex7a => _root_.Sorace2000.Examples.ex7a
  | .ex7b => _root_.Sorace2000.Examples.ex7b
  | .ex8a => _root_.Sorace2000.Examples.ex8a
  | .ex9a => _root_.Sorace2000.Examples.ex9a
  | .ex9b => _root_.Sorace2000.Examples.ex9b
  | .ex9c => _root_.Sorace2000.Examples.ex9c
  | .ex10a => _root_.Sorace2000.Examples.ex10a
  | .ex10b => _root_.Sorace2000.Examples.ex10b
  | .ex11 => _root_.Sorace2000.Examples.ex11
  | .ex12 => _root_.Sorace2000.Examples.ex12
  | .ex13 => _root_.Sorace2000.Examples.ex13
  | .ex14a => _root_.Sorace2000.Examples.ex14a
  | .ex14c => _root_.Sorace2000.Examples.ex14c
  | .ex15a => _root_.Sorace2000.Examples.ex15a
  | .ex15b => _root_.Sorace2000.Examples.ex15b
  | .ex15c => _root_.Sorace2000.Examples.ex15c
  | .ex16 => _root_.Sorace2000.Examples.ex16
  | .ex17a => _root_.Sorace2000.Examples.ex17a
  | .ex17b => _root_.Sorace2000.Examples.ex17b
  | .ex18a => _root_.Sorace2000.Examples.ex18a
  | .ex18b => _root_.Sorace2000.Examples.ex18b
  | .ex19a => _root_.Sorace2000.Examples.ex19a
  | .ex19b => _root_.Sorace2000.Examples.ex19b
  | .ex19c => _root_.Sorace2000.Examples.ex19c
  | .ex20a => _root_.Sorace2000.Examples.ex20a
  | .ex20b => _root_.Sorace2000.Examples.ex20b
  | .ex20c => _root_.Sorace2000.Examples.ex20c
  | .ex21a => _root_.Sorace2000.Examples.ex21a
  | .ex21b => _root_.Sorace2000.Examples.ex21b
  | .ex21c => _root_.Sorace2000.Examples.ex21c
  | .ex22 => _root_.Sorace2000.Examples.ex22
  | .ex23a => _root_.Sorace2000.Examples.ex23a
  | .ex23b => _root_.Sorace2000.Examples.ex23b
  | .ex23c => _root_.Sorace2000.Examples.ex23c
  | .ex23d => _root_.Sorace2000.Examples.ex23d
  | .ex24a => _root_.Sorace2000.Examples.ex24a
  | .ex24b => _root_.Sorace2000.Examples.ex24b
  | .ex24c => _root_.Sorace2000.Examples.ex24c
  | .ex25a => _root_.Sorace2000.Examples.ex25a
  | .ex25b => _root_.Sorace2000.Examples.ex25b
  | .ex33a => _root_.Sorace2000.Examples.ex33a
  | .ex33b => _root_.Sorace2000.Examples.ex33b
  | .ex33c => _root_.Sorace2000.Examples.ex33c
  | .ex33d => _root_.Sorace2000.Examples.ex33d
  | .ex34 => _root_.Sorace2000.Examples.ex34
  | .ex35 => _root_.Sorace2000.Examples.ex35
  | .ex36a => _root_.Sorace2000.Examples.ex36a
  | .ex36b => _root_.Sorace2000.Examples.ex36b
  | .ex37a => _root_.Sorace2000.Examples.ex37a
  | .ex37b => _root_.Sorace2000.Examples.ex37b
  | .ex37c => _root_.Sorace2000.Examples.ex37c
  | .ex38_rennen => _root_.Sorace2000.Examples.ex38_rennen
  | .ex38_laufen => _root_.Sorace2000.Examples.ex38_laufen
  | .ex38_schwimmen => _root_.Sorace2000.Examples.ex38_schwimmen
  | .ex39a => _root_.Sorace2000.Examples.ex39a
  | .ex39b => _root_.Sorace2000.Examples.ex39b
  | .ex40a => _root_.Sorace2000.Examples.ex40a
  | .ex40b => _root_.Sorace2000.Examples.ex40b
  | .ex41a => _root_.Sorace2000.Examples.ex41a
  | .ex41b => _root_.Sorace2000.Examples.ex41b
  | .ex41c => _root_.Sorace2000.Examples.ex41c
  | .ex41d => _root_.Sorace2000.Examples.ex41d
  | .ex42a => _root_.Sorace2000.Examples.ex42a
  | .ex42b => _root_.Sorace2000.Examples.ex42b
  | .ex43a => _root_.Sorace2000.Examples.ex43a
  | .ex43b => _root_.Sorace2000.Examples.ex43b
  | .ex44a => _root_.Sorace2000.Examples.ex44a
  | .ex44b => _root_.Sorace2000.Examples.ex44b
  | .ex45a => _root_.Sorace2000.Examples.ex45a
  | .ex45b => _root_.Sorace2000.Examples.ex45b
  | .ex46a => _root_.Sorace2000.Examples.ex46a
  | .ex46b => _root_.Sorace2000.Examples.ex46b
  | .ex47a => _root_.Sorace2000.Examples.ex47a
  | .ex47b => _root_.Sorace2000.Examples.ex47b
  | .ex47c => _root_.Sorace2000.Examples.ex47c
  | .ex47d => _root_.Sorace2000.Examples.ex47d
  | .ex48_piovere => _root_.Sorace2000.Examples.ex48_piovere
  | .ex48_nevicare => _root_.Sorace2000.Examples.ex48_nevicare
  | .ex48_grandinare => _root_.Sorace2000.Examples.ex48_grandinare
  | .ex49 => _root_.Sorace2000.Examples.ex49
  | .ex50a => _root_.Sorace2000.Examples.ex50a
  | .ex50b => _root_.Sorace2000.Examples.ex50b
  | .ex51_tuonare => _root_.Sorace2000.Examples.ex51_tuonare
  | .ex51_lampeggiare => _root_.Sorace2000.Examples.ex51_lampeggiare

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Sorace2000.Examples.all := rfl

/-- The value the example records under `predicate`. -/
def Example.predicate : Example → Option PredicateShift
  | .ex1a => none
  | .ex1b => none
  | .ex1c => none
  | .ex1d => none
  | .ex4 => some .detelicized
  | .ex5a => none
  | .ex5b => none
  | .ex30a => none
  | .ex7a => none
  | .ex7b => none
  | .ex8a => none
  | .ex9a => none
  | .ex9b => none
  | .ex9c => none
  | .ex10a => none
  | .ex10b => none
  | .ex11 => some .detelicized
  | .ex12 => none
  | .ex13 => none
  | .ex14a => none
  | .ex14c => none
  | .ex15a => none
  | .ex15b => none
  | .ex15c => none
  | .ex16 => none
  | .ex17a => none
  | .ex17b => none
  | .ex18a => none
  | .ex18b => none
  | .ex19a => none
  | .ex19b => none
  | .ex19c => none
  | .ex20a => none
  | .ex20b => none
  | .ex20c => none
  | .ex21a => none
  | .ex21b => none
  | .ex21c => none
  | .ex22 => none
  | .ex23a => none
  | .ex23b => none
  | .ex23c => none
  | .ex23d => none
  | .ex24a => none
  | .ex24b => none
  | .ex24c => none
  | .ex25a => none
  | .ex25b => none
  | .ex33a => none
  | .ex33b => none
  | .ex33c => none
  | .ex33d => none
  | .ex34 => none
  | .ex35 => some .telicized
  | .ex36a => none
  | .ex36b => none
  | .ex37a => none
  | .ex37b => none
  | .ex37c => none
  | .ex38_rennen => none
  | .ex38_laufen => none
  | .ex38_schwimmen => none
  | .ex39a => none
  | .ex39b => some .telicized
  | .ex40a => none
  | .ex40b => some .telicized
  | .ex41a => none
  | .ex41b => some .telicized
  | .ex41c => none
  | .ex41d => some .telicized
  | .ex42a => none
  | .ex42b => some .telicized
  | .ex43a => none
  | .ex43b => none
  | .ex44a => none
  | .ex44b => none
  | .ex45a => none
  | .ex45b => none
  | .ex46a => none
  | .ex46b => none
  | .ex47a => none
  | .ex47b => none
  | .ex47c => none
  | .ex47d => none
  | .ex48_piovere => none
  | .ex48_nevicare => none
  | .ex48_grandinare => none
  | .ex49 => some .telicized
  | .ex50a => none
  | .ex50b => none
  | .ex51_tuonare => some .telicized
  | .ex51_lampeggiare => some .telicized

theorem Example.predicate_datum :
    ∀ x : Example, _root_.Sorace2000.Examples.predicate x.datum = x.predicate := by
  decide +kernel

/-- The value the example records under `subject`. -/
def Example.subject : Example → Option SubjectShift
  | .ex1a => none
  | .ex1b => none
  | .ex1c => none
  | .ex1d => none
  | .ex4 => none
  | .ex5a => some .agentive
  | .ex5b => none
  | .ex30a => none
  | .ex7a => none
  | .ex7b => none
  | .ex8a => none
  | .ex9a => none
  | .ex9b => none
  | .ex9c => none
  | .ex10a => none
  | .ex10b => none
  | .ex11 => none
  | .ex12 => none
  | .ex13 => none
  | .ex14a => none
  | .ex14c => none
  | .ex15a => none
  | .ex15b => none
  | .ex15c => some .agentive
  | .ex16 => none
  | .ex17a => none
  | .ex17b => none
  | .ex18a => none
  | .ex18b => none
  | .ex19a => none
  | .ex19b => none
  | .ex19c => none
  | .ex20a => none
  | .ex20b => none
  | .ex20c => none
  | .ex21a => none
  | .ex21b => none
  | .ex21c => none
  | .ex22 => none
  | .ex23a => none
  | .ex23b => none
  | .ex23c => none
  | .ex23d => none
  | .ex24a => none
  | .ex24b => none
  | .ex24c => none
  | .ex25a => none
  | .ex25b => none
  | .ex33a => none
  | .ex33b => none
  | .ex33c => none
  | .ex33d => none
  | .ex34 => some .nonagentive
  | .ex35 => none
  | .ex36a => none
  | .ex36b => some .nonagentive
  | .ex37a => none
  | .ex37b => none
  | .ex37c => none
  | .ex38_rennen => none
  | .ex38_laufen => none
  | .ex38_schwimmen => none
  | .ex39a => none
  | .ex39b => none
  | .ex40a => none
  | .ex40b => none
  | .ex41a => none
  | .ex41b => none
  | .ex41c => none
  | .ex41d => none
  | .ex42a => none
  | .ex42b => none
  | .ex43a => some .nonagentive
  | .ex43b => some .nonagentive
  | .ex44a => none
  | .ex44b => some .nonagentive
  | .ex45a => none
  | .ex45b => some .agentive
  | .ex46a => none
  | .ex46b => some .agentive
  | .ex47a => none
  | .ex47b => none
  | .ex47c => none
  | .ex47d => none
  | .ex48_piovere => none
  | .ex48_nevicare => none
  | .ex48_grandinare => none
  | .ex49 => none
  | .ex50a => none
  | .ex50b => none
  | .ex51_tuonare => none
  | .ex51_lampeggiare => none

theorem Example.subject_datum :
    ∀ x : Example, _root_.Sorace2000.Examples.subject x.datum = x.subject := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex1a => [(.auxiliary, .essere), (.participle, .venire)]
  | .ex1b => [(.auxiliary, .etre), (.participle, .arriver)]
  | .ex1c => [(.auxiliary, .zijn), (.participle, .komen)]
  | .ex1d => [(.auxiliary, .sein), (.participle, .ankommen)]
  | .ex4 => [(.auxiliary, .essere), (.participle, .arrivare)]
  | .ex5a => [(.auxiliary, .essere), (.participle, .cadere)]
  | .ex5b => [(.auxiliary, .essere), (.participle, .cadere)]
  | .ex30a => [(.auxiliary, .avere), (.participle, .arrivare)]
  | .ex7a => [(.auxiliary, .essere), (.participle, .salire)]
  | .ex7b => [(.auxiliary, .essere), (.participle, .marcire)]
  | .ex8a => [(.auxiliary, .essere), (.participle, .fiorire)]
  | .ex9a => [(.auxiliary, .etre), (.participle, .naitre)]
  | .ex9b => [(.auxiliary, .zijn), (.participle, .sterven)]
  | .ex9c => [(.auxiliary, .sein), (.participle, .gebaren)]
  | .ex10a => [(.auxiliary, .zijn), (.participle, .groeien)]
  | .ex10b => [(.auxiliary, .sein), (.participle, .steigen)]
  | .ex11 => [(.auxiliary, .zijn), (.participle, .stijgen)]
  | .ex12 => [(.auxiliary, .etre), (.participle, .devenir)]
  | .ex13 => [(.auxiliary, .avoir), (.participle, .rougir)]
  | .ex14a => [(.auxiliary, .etre), (.participle, .paraitre)]
  | .ex14c => [(.auxiliary, .etre), (.participle, .echapper)]
  | .ex15a => [(.auxiliary, .essere), (.participle, .rimanere)]
  | .ex15b => [(.auxiliary, .essere), (.participle, .durare)]
  | .ex15c => [(.auxiliary, .essere), (.participle, .durare)]
  | .ex16 => [(.auxiliary, .avoir), (.participle, .survivre)]
  | .ex17a => [(.auxiliary, .haben), (.participle, .halten)]
  | .ex17b => [(.auxiliary, .haben), (.participle, .verweilen)]
  | .ex18a => [(.auxiliary, .zijn), (.participle, .overblijven)]
  | .ex18b => [(.auxiliary, .hebben), (.participle, .duren)]
  | .ex19a => [(.auxiliary, .etre), (.participle, .rester)]
  | .ex19b => [(.auxiliary, .zijn), (.participle, .blijven)]
  | .ex19c => [(.auxiliary, .sein), (.participle, .bleiben)]
  | .ex20a => [(.auxiliary, .essere), (.participle, .esistere)]
  | .ex20b => [(.auxiliary, .essere), (.participle, .bastare)]
  | .ex20c => [(.auxiliary, .essere), (.participle, .sembrare)]
  | .ex21a => [(.auxiliary, .avere), (.participle, .bastare)]
  | .ex21b => [(.auxiliary, .avere), (.participle, .appartenere)]
  | .ex21c => [(.auxiliary, .essere), (.participle, .scarseggiare)]
  | .ex22 => [(.auxiliary, .avoir), (.participle, .exister)]
  | .ex23a => [(.auxiliary, .haben), (.participle, .gefallen)]
  | .ex23b => [(.auxiliary, .haben), (.participle, .genugen)]
  | .ex23c => [(.auxiliary, .sein), (.participle, .liegen)]
  | .ex23d => [(.auxiliary, .sein), (.participle, .abhangen)]
  | .ex24a => [(.auxiliary, .hebben), (.participle, .staan)]
  | .ex24b => [(.auxiliary, .hebben), (.participle, .bestaan)]
  | .ex24c => [(.auxiliary, .zijn), (.participle, .blijken)]
  | .ex25a => [(.auxiliary, .sein), (.participle, .sein)]
  | .ex25b => [(.auxiliary, .zijn), (.participle, .zijn)]
  | .ex33a => [(.auxiliary, .avere), (.participle, .chiacchierare)]
  | .ex33b => [(.auxiliary, .avoir), (.participle, .travailler)]
  | .ex33c => [(.auxiliary, .hebben), (.participle, .blazen)]
  | .ex33d => [(.auxiliary, .haben), (.participle, .arbeiten)]
  | .ex34 => [(.auxiliary, .avere), (.participle, .funzionare)]
  | .ex35 => [(.auxiliary, .avere), (.participle, .lavorare)]
  | .ex36a => [(.auxiliary, .avere), (.participle, .cedere)]
  | .ex36b => [(.auxiliary, .avere), (.participle, .cedere)]
  | .ex37a => [(.auxiliary, .avere), (.participle, .correre)]
  | .ex37b => [(.auxiliary, .hebben), (.participle, .lopen)]
  | .ex37c => [(.auxiliary, .avoir), (.participle, .nager)]
  | .ex38_rennen => [(.auxiliary, .sein), (.participle, .rennen)]
  | .ex38_laufen => [(.auxiliary, .sein), (.participle, .laufen)]
  | .ex38_schwimmen => [(.auxiliary, .sein), (.participle, .schwimmen)]
  | .ex39a => [(.auxiliary, .hebben), (.participle, .rollen)]
  | .ex39b => [(.auxiliary, .zijn), (.participle, .rollen)]
  | .ex40a => [(.auxiliary, .haben), (.participle, .tanzen)]
  | .ex40b => [(.auxiliary, .sein), (.participle, .tanzen)]
  | .ex41a => [(.auxiliary, .avere), (.participle, .correre)]
  | .ex41b => [(.auxiliary, .essere), (.participle, .correre)]
  | .ex41c => [(.auxiliary, .avere), (.participle, .nuotare)]
  | .ex41d => [(.auxiliary, .avere), (.participle, .nuotare)]
  | .ex42a => [(.auxiliary, .avoir), (.participle, .courir)]
  | .ex42b => [(.auxiliary, .avoir), (.participle, .courir)]
  | .ex43a => [(.auxiliary, .essere), (.participle, .correre)]
  | .ex43b => [(.auxiliary, .essere), (.participle, .saltare)]
  | .ex44a => [(.auxiliary, .avere), (.participle, .atterrare)]
  | .ex44b => [(.auxiliary, .essere), (.participle, .atterrare)]
  | .ex45a => [(.auxiliary, .avere), (.participle, .tentennare)]
  | .ex45b => [(.auxiliary, .avere), (.participle, .tentennare)]
  | .ex46a => [(.auxiliary, .avere), (.participle, .tossire)]
  | .ex46b => [(.auxiliary, .avere), (.participle, .tossire)]
  | .ex47a => [(.auxiliary, .avere), (.participle, .squillare)]
  | .ex47b => [(.auxiliary, .avere), (.participle, .risuonare)]
  | .ex47c => [(.auxiliary, .avere), (.participle, .rimbombare)]
  | .ex47d => [(.auxiliary, .avere), (.participle, .rintoccare)]
  | .ex48_piovere => [(.auxiliary, .avere), (.participle, .piovere)]
  | .ex48_nevicare => [(.auxiliary, .avere), (.participle, .nevicare)]
  | .ex48_grandinare => [(.auxiliary, .avere), (.participle, .grandinare)]
  | .ex49 => [(.auxiliary, .essere), (.participle, .piovere)]
  | .ex50a => [(.auxiliary, .avere), (.participle, .tuonare)]
  | .ex50b => [(.auxiliary, .avere), (.participle, .lampeggiare)]
  | .ex51_tuonare => [(.auxiliary, .essere), (.participle, .tuonare)]
  | .ex51_lampeggiare => [(.auxiliary, .essere), (.participle, .lampeggiare)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.Sorace2000.Examples.label? · = some l)).filterMap _root_.Sorace2000.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end Sorace2000.Examples
