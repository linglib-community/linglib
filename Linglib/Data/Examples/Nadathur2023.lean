module

public import Linglib.Data.Examples.Schema

/-!
# `Nadathur2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Nadathur2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Nadathur2023.Examples`.
-/

@[expose] public section

namespace Nadathur2023.Examples

def ex_2a : Datum :=
  { id := "nadathur2023_2a"
    source := ⟨"nadathur-2023-implicatives", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman onnistu-i kuitenkin pakenema-an."
    glossedTokens := [("Eman", "Eman"), ("onnistu-i", "succeed-PST.3SG"), ("kuitenkin", "however"), ("pakenema-an", "flee-INF.ILL")]
    glossedWords := [⟨['E', 'm', 'a', 'n'], ['E', 'm', 'a', 'n'], [⟨['E', 'm', 'a', 'n'], ['E', 'm', 'a', 'n'], none⟩]⟩, ⟨['o', 'n', 'n', 'i', 's', 't', 'u', '-', 'i'], ['s', 'u', 'c', 'c', 'e', 'e', 'd', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['o', 'n', 'n', 'i', 's', 't', 'u'], ['s', 'u', 'c', 'c', 'e', 'e', 'd'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'u', 'i', 't', 'e', 'n', 'k', 'i', 'n'], ['h', 'o', 'w', 'e', 'v', 'e', 'r'], [⟨['k', 'u', 'i', 't', 'e', 'n', 'k', 'i', 'n'], ['h', 'o', 'w', 'e', 'v', 'e', 'r'], none⟩]⟩, ⟨['p', 'a', 'k', 'e', 'n', 'e', 'm', 'a', '-', 'a', 'n'], ['f', 'l', 'e', 'e', '-', 'I', 'N', 'F', '.', 'I', 'L', 'L'], [⟨['p', 'a', 'k', 'e', 'n', 'e', 'm', 'a'], ['f', 'l', 'e', 'e'], none⟩, ⟨['a', 'n'], ['I', 'N', 'F', '.', 'I', 'L', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "positive"), ("entails", "complement")] }

def ex_2b : Datum :=
  { id := "nadathur2023_2b"
    source := ⟨"nadathur-2023-implicatives", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman e-i onnistu-nut kuitenkaan pakenema-an."
    glossedTokens := [("Eman", "Eman"), ("e-i", "NEG-3SG"), ("onnistu-nut", "succeed-SG.PP"), ("kuitenkaan", "however"), ("pakenema-an", "flee-INF.ILL")]
    glossedWords := [⟨['E', 'm', 'a', 'n'], ['E', 'm', 'a', 'n'], [⟨['E', 'm', 'a', 'n'], ['E', 'm', 'a', 'n'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 'n', 'n', 'i', 's', 't', 'u', '-', 'n', 'u', 't'], ['s', 'u', 'c', 'c', 'e', 'e', 'd', '-', 'S', 'G', '.', 'P', 'P'], [⟨['o', 'n', 'n', 'i', 's', 't', 'u'], ['s', 'u', 'c', 'c', 'e', 'e', 'd'], none⟩, ⟨['n', 'u', 't'], ['S', 'G', '.', 'P', 'P'], some '-'⟩]⟩, ⟨['k', 'u', 'i', 't', 'e', 'n', 'k', 'a', 'a', 'n'], ['h', 'o', 'w', 'e', 'v', 'e', 'r'], [⟨['k', 'u', 'i', 't', 'e', 'n', 'k', 'a', 'a', 'n'], ['h', 'o', 'w', 'e', 'v', 'e', 'r'], none⟩]⟩, ⟨['p', 'a', 'k', 'e', 'n', 'e', 'm', 'a', '-', 'a', 'n'], ['f', 'l', 'e', 'e', '-', 'I', 'N', 'F', '.', 'I', 'L', 'L'], [⟨['p', 'a', 'k', 'e', 'n', 'e', 'm', 'a'], ['f', 'l', 'e', 'e'], none⟩, ⟨['a', 'n'], ['I', 'N', 'F', '.', 'I', 'L', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "negated"), ("entails", "negation")] }

def ex_4a : Datum :=
  { id := "nadathur2023_4a"
    source := ⟨"nadathur-2023-implicatives", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno uskals-i avat-a ove-n."
    glossedTokens := [("Juno", "Juno"), ("uskals-i", "dare-PST.3SG"), ("avat-a", "open-INF"), ("ove-n", "door-GEN/ACC")]
    glossedWords := [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], none⟩]⟩, ⟨['u', 's', 'k', 'a', 'l', 's', '-', 'i'], ['d', 'a', 'r', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['u', 's', 'k', 'a', 'l', 's'], ['d', 'a', 'r', 'e'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['a', 'v', 'a', 't', '-', 'a'], ['o', 'p', 'e', 'n', '-', 'I', 'N', 'F'], [⟨['a', 'v', 'a', 't'], ['o', 'p', 'e', 'n'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['o', 'v', 'e', '-', 'n'], ['d', 'o', 'o', 'r', '-', 'G', 'E', 'N', '/', 'A', 'C', 'C'], [⟨['o', 'v', 'e'], ['d', 'o', 'o', 'r'], none⟩, ⟨['n'], ['G', 'E', 'N', '/', 'A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_4b : Datum :=
  { id := "nadathur2023_4b"
    source := ⟨"nadathur-2023-implicatives", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i uskalta-nut avat-a ove-a."
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("uskalta-nut", "dare-SG.PP"), ("avat-a", "open-INF"), ("ove-a", "door-PART")]
    glossedWords := [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['u', 's', 'k', 'a', 'l', 't', 'a', '-', 'n', 'u', 't'], ['d', 'a', 'r', 'e', '-', 'S', 'G', '.', 'P', 'P'], [⟨['u', 's', 'k', 'a', 'l', 't', 'a'], ['d', 'a', 'r', 'e'], none⟩, ⟨['n', 'u', 't'], ['S', 'G', '.', 'P', 'P'], some '-'⟩]⟩, ⟨['a', 'v', 'a', 't', '-', 'a'], ['o', 'p', 'e', 'n', '-', 'I', 'N', 'F'], [⟨['a', 'v', 'a', 't'], ['o', 'p', 'e', 'n'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['o', 'v', 'e', '-', 'a'], ['d', 'o', 'o', 'r', '-', 'P', 'A', 'R', 'T'], [⟨['o', 'v', 'e'], ['d', 'o', 'o', 'r'], none⟩, ⟨['a'], ['P', 'A', 'R', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_5a : Datum :=
  { id := "nadathur2023_5a"
    source := ⟨"nadathur-2023-implicatives", "(5a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo jakso-i noust-a."
    glossedTokens := [("Sampo", "Sampo"), ("jakso-i", "have.strength-PST.3SG"), ("noust-a", "rise-INF")]
    glossedWords := [⟨['S', 'a', 'm', 'p', 'o'], ['S', 'a', 'm', 'p', 'o'], [⟨['S', 'a', 'm', 'p', 'o'], ['S', 'a', 'm', 'p', 'o'], none⟩]⟩, ⟨['j', 'a', 'k', 's', 'o', '-', 'i'], ['h', 'a', 'v', 'e', '.', 's', 't', 'r', 'e', 'n', 'g', 't', 'h', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['j', 'a', 'k', 's', 'o'], ['h', 'a', 'v', 'e', '.', 's', 't', 'r', 'e', 'n', 'g', 't', 'h'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['n', 'o', 'u', 's', 't', '-', 'a'], ['r', 'i', 's', 'e', '-', 'I', 'N', 'F'], [⟨['n', 'o', 'u', 's', 't'], ['r', 'i', 's', 'e'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_5b : Datum :=
  { id := "nadathur2023_5b"
    source := ⟨"nadathur-2023-implicatives", "(5b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo e-i jaksa-nut noust-a."
    glossedTokens := [("Sampo", "Sampo"), ("e-i", "NEG-3SG"), ("jaksa-nut", "have.strength-PP.SG"), ("noust-a", "rise-INF")]
    glossedWords := [⟨['S', 'a', 'm', 'p', 'o'], ['S', 'a', 'm', 'p', 'o'], [⟨['S', 'a', 'm', 'p', 'o'], ['S', 'a', 'm', 'p', 'o'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['j', 'a', 'k', 's', 'a', '-', 'n', 'u', 't'], ['h', 'a', 'v', 'e', '.', 's', 't', 'r', 'e', 'n', 'g', 't', 'h', '-', 'P', 'P', '.', 'S', 'G'], [⟨['j', 'a', 'k', 's', 'a'], ['h', 'a', 'v', 'e', '.', 's', 't', 'r', 'e', 'n', 'g', 't', 'h'], none⟩, ⟨['n', 'u', 't'], ['P', 'P', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['n', 'o', 'u', 's', 't', '-', 'a'], ['r', 'i', 's', 'e', '-', 'I', 'N', 'F'], [⟨['n', 'o', 'u', 's', 't'], ['r', 'i', 's', 'e'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_10a : Datum :=
  { id := "nadathur2023_10a"
    source := ⟨"nadathur-2023-implicatives", "(10a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän viits-i vastat-a."
    glossedTokens := [("Hän", "he.NOM"), ("viits-i", "bother-PST.3SG"), ("vastat-a", "answer-INF")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['v', 'i', 'i', 't', 's', '-', 'i'], ['b', 'o', 't', 'h', 'e', 'r', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['v', 'i', 'i', 't', 's'], ['b', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['v', 'a', 's', 't', 'a', 't', '-', 'a'], ['a', 'n', 's', 'w', 'e', 'r', '-', 'I', 'N', 'F'], [⟨['v', 'a', 's', 't', 'a', 't'], ['a', 'n', 's', 'w', 'e', 'r'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "positive"), ("entails", "complement")] }

def ex_10b : Datum :=
  { id := "nadathur2023_10b"
    source := ⟨"nadathur-2023-implicatives", "(10b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i viitsi-nyt vastat-a."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("viitsi-nyt", "bother-PP.SG"), ("vastat-a", "answer-INF")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['v', 'i', 'i', 't', 's', 'i', '-', 'n', 'y', 't'], ['b', 'o', 't', 'h', 'e', 'r', '-', 'P', 'P', '.', 'S', 'G'], [⟨['v', 'i', 'i', 't', 's', 'i'], ['b', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'y', 't'], ['P', 'P', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['v', 'a', 's', 't', 'a', 't', '-', 'a'], ['a', 'n', 's', 'w', 'e', 'r', '-', 'I', 'N', 'F'], [⟨['v', 'a', 's', 't', 'a', 't'], ['a', 'n', 's', 'w', 'e', 'r'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "negated"), ("entails", "negation")] }

def ex_11a : Datum :=
  { id := "nadathur2023_11a"
    source := ⟨"nadathur-2023-implicatives", "(11a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja maltto-i odotta-a."
    glossedTokens := [("Marja", "Marja"), ("maltto-i", "have.patience-PST.3SG"), ("odotta-a", "wait-INF")]
    glossedWords := [⟨['M', 'a', 'r', 'j', 'a'], ['M', 'a', 'r', 'j', 'a'], [⟨['M', 'a', 'r', 'j', 'a'], ['M', 'a', 'r', 'j', 'a'], none⟩]⟩, ⟨['m', 'a', 'l', 't', 't', 'o', '-', 'i'], ['h', 'a', 'v', 'e', '.', 'p', 'a', 't', 'i', 'e', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['m', 'a', 'l', 't', 't', 'o'], ['h', 'a', 'v', 'e', '.', 'p', 'a', 't', 'i', 'e', 'n', 'c', 'e'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 'd', 'o', 't', 't', 'a', '-', 'a'], ['w', 'a', 'i', 't', '-', 'I', 'N', 'F'], [⟨['o', 'd', 'o', 't', 't', 'a'], ['w', 'a', 'i', 't'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_11b : Datum :=
  { id := "nadathur2023_11b"
    source := ⟨"nadathur-2023-implicatives", "(11b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja e-i maltta-nut odotta-a."
    glossedTokens := [("Marja", "Marja"), ("e-i", "NEG-3SG"), ("maltta-nut", "have.patience-SG.PP"), ("odotta-a", "wait-INF")]
    glossedWords := [⟨['M', 'a', 'r', 'j', 'a'], ['M', 'a', 'r', 'j', 'a'], [⟨['M', 'a', 'r', 'j', 'a'], ['M', 'a', 'r', 'j', 'a'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'l', 't', 't', 'a', '-', 'n', 'u', 't'], ['h', 'a', 'v', 'e', '.', 'p', 'a', 't', 'i', 'e', 'n', 'c', 'e', '-', 'S', 'G', '.', 'P', 'P'], [⟨['m', 'a', 'l', 't', 't', 'a'], ['h', 'a', 'v', 'e', '.', 'p', 'a', 't', 'i', 'e', 'n', 'c', 'e'], none⟩, ⟨['n', 'u', 't'], ['S', 'G', '.', 'P', 'P'], some '-'⟩]⟩, ⟨['o', 'd', 'o', 't', 't', 'a', '-', 'a'], ['w', 'a', 'i', 't', '-', 'I', 'N', 'F'], [⟨['o', 'd', 'o', 't', 't', 'a'], ['w', 'a', 'i', 't'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_27a : Datum :=
  { id := "nadathur2023_27a"
    source := ⟨"nadathur-2023-implicatives", "(27a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän henno-i tappa-a kissa-n."
    glossedTokens := [("Hän", "he.NOM"), ("henno-i", "have.heart-PST.3SG"), ("tappa-a", "kill-INF"), ("kissa-n", "cat-GEN/ACC")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'e', 'n', 'n', 'o', '-', 'i'], ['h', 'a', 'v', 'e', '.', 'h', 'e', 'a', 'r', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['h', 'e', 'n', 'n', 'o'], ['h', 'a', 'v', 'e', '.', 'h', 'e', 'a', 'r', 't'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'a', 'p', 'p', 'a', '-', 'a'], ['k', 'i', 'l', 'l', '-', 'I', 'N', 'F'], [⟨['t', 'a', 'p', 'p', 'a'], ['k', 'i', 'l', 'l'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['k', 'i', 's', 's', 'a', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N', '/', 'A', 'C', 'C'], [⟨['k', 'i', 's', 's', 'a'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N', '/', 'A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_27b : Datum :=
  { id := "nadathur2023_27b"
    source := ⟨"nadathur-2023-implicatives", "(27b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i henno-nut tappa-a kissa-a."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("henno-nut", "have.heart-SG.PP"), ("tappa-a", "kill-INF"), ("kissa-a", "cat-PART")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['h', 'e', 'n', 'n', 'o', '-', 'n', 'u', 't'], ['h', 'a', 'v', 'e', '.', 'h', 'e', 'a', 'r', 't', '-', 'S', 'G', '.', 'P', 'P'], [⟨['h', 'e', 'n', 'n', 'o'], ['h', 'a', 'v', 'e', '.', 'h', 'e', 'a', 'r', 't'], none⟩, ⟨['n', 'u', 't'], ['S', 'G', '.', 'P', 'P'], some '-'⟩]⟩, ⟨['t', 'a', 'p', 'p', 'a', '-', 'a'], ['k', 'i', 'l', 'l', '-', 'I', 'N', 'F'], [⟨['t', 'a', 'p', 'p', 'a'], ['k', 'i', 'l', 'l'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['k', 'i', 's', 's', 'a', '-', 'a'], ['c', 'a', 't', '-', 'P', 'A', 'R', 'T'], [⟨['k', 'i', 's', 's', 'a'], ['c', 'a', 't'], none⟩, ⟨['a'], ['P', 'A', 'R', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_29a : Datum :=
  { id := "nadathur2023_29a"
    source := ⟨"nadathur-2023-implicatives", "(29a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit pysty-i tappelema-an."
    glossedTokens := [("Maarit", "Maarit"), ("pysty-i", "able-PST.3SG"), ("tappelema-an", "fight-INF")]
    glossedWords := [⟨['M', 'a', 'a', 'r', 'i', 't'], ['M', 'a', 'a', 'r', 'i', 't'], [⟨['M', 'a', 'a', 'r', 'i', 't'], ['M', 'a', 'a', 'r', 'i', 't'], none⟩]⟩, ⟨['p', 'y', 's', 't', 'y', '-', 'i'], ['a', 'b', 'l', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['p', 'y', 's', 't', 'y'], ['a', 'b', 'l', 'e'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['t', 'a', 'p', 'p', 'e', 'l', 'e', 'm', 'a', '-', 'a', 'n'], ['f', 'i', 'g', 'h', 't', '-', 'I', 'N', 'F'], [⟨['t', 'a', 'p', 'p', 'e', 'l', 'e', 'm', 'a'], ['f', 'i', 'g', 'h', 't'], none⟩, ⟨['a', 'n'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_29b : Datum :=
  { id := "nadathur2023_29b"
    source := ⟨"nadathur-2023-implicatives", "(29b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit e-i pysty-nyt tappelema-an."
    glossedTokens := [("Maarit", "Maarit"), ("e-i", "NEG-3SG"), ("pysty-nyt", "able-SG.PP"), ("tappelema-an", "fight-INF")]
    glossedWords := [⟨['M', 'a', 'a', 'r', 'i', 't'], ['M', 'a', 'a', 'r', 'i', 't'], [⟨['M', 'a', 'a', 'r', 'i', 't'], ['M', 'a', 'a', 'r', 'i', 't'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['p', 'y', 's', 't', 'y', '-', 'n', 'y', 't'], ['a', 'b', 'l', 'e', '-', 'S', 'G', '.', 'P', 'P'], [⟨['p', 'y', 's', 't', 'y'], ['a', 'b', 'l', 'e'], none⟩, ⟨['n', 'y', 't'], ['S', 'G', '.', 'P', 'P'], some '-'⟩]⟩, ⟨['t', 'a', 'p', 'p', 'e', 'l', 'e', 'm', 'a', '-', 'a', 'n'], ['f', 'i', 'g', 'h', 't', '-', 'I', 'N', 'F'], [⟨['t', 'a', 'p', 'p', 'e', 'l', 'e', 'm', 'a'], ['f', 'i', 'g', 'h', 't'], none⟩, ⟨['a', 'n'], ['I', 'N', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "negated"), ("entails", "negation")] }

def ex_30a : Datum :=
  { id := "nadathur2023_30a"
    source := ⟨"nadathur-2023-implicatives", "(30a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija mahtu-i kulke-ma-an ove-sta."
    glossedTokens := [("Freija", "Freija"), ("mahtu-i", "fit-PST.3SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    glossedWords := [⟨['F', 'r', 'e', 'i', 'j', 'a'], ['F', 'r', 'e', 'i', 'j', 'a'], [⟨['F', 'r', 'e', 'i', 'j', 'a'], ['F', 'r', 'e', 'i', 'j', 'a'], none⟩]⟩, ⟨['m', 'a', 'h', 't', 'u', '-', 'i'], ['f', 'i', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['m', 'a', 'h', 't', 'u'], ['f', 'i', 't'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'u', 'l', 'k', 'e', '-', 'm', 'a', '-', 'a', 'n'], ['g', 'o', '-', 'I', 'N', 'F', '-', 'I', 'L', 'L'], [⟨['k', 'u', 'l', 'k', 'e'], ['g', 'o'], none⟩, ⟨['m', 'a'], ['I', 'N', 'F'], some '-'⟩, ⟨['a', 'n'], ['I', 'L', 'L'], some '-'⟩]⟩, ⟨['o', 'v', 'e', '-', 's', 't', 'a'], ['d', 'o', 'o', 'r', '-', 'E', 'L', 'A'], [⟨['o', 'v', 'e'], ['d', 'o', 'o', 'r'], none⟩, ⟨['s', 't', 'a'], ['E', 'L', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_30b : Datum :=
  { id := "nadathur2023_30b"
    source := ⟨"nadathur-2023-implicatives", "(30b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija e-i mahtu-nut kulke-ma-an ove-sta."
    glossedTokens := [("Freija", "Freija"), ("e-i", "NEG-3SG"), ("mahtu-nut", "fit-PP.SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    glossedWords := [⟨['F', 'r', 'e', 'i', 'j', 'a'], ['F', 'r', 'e', 'i', 'j', 'a'], [⟨['F', 'r', 'e', 'i', 'j', 'a'], ['F', 'r', 'e', 'i', 'j', 'a'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['m', 'a', 'h', 't', 'u', '-', 'n', 'u', 't'], ['f', 'i', 't', '-', 'P', 'P', '.', 'S', 'G'], [⟨['m', 'a', 'h', 't', 'u'], ['f', 'i', 't'], none⟩, ⟨['n', 'u', 't'], ['P', 'P', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'u', 'l', 'k', 'e', '-', 'm', 'a', '-', 'a', 'n'], ['g', 'o', '-', 'I', 'N', 'F', '-', 'I', 'L', 'L'], [⟨['k', 'u', 'l', 'k', 'e'], ['g', 'o'], none⟩, ⟨['m', 'a'], ['I', 'N', 'F'], some '-'⟩, ⟨['a', 'n'], ['I', 'L', 'L'], some '-'⟩]⟩, ⟨['o', 'v', 'e', '-', 's', 't', 'a'], ['d', 'o', 'o', 'r', '-', 'E', 'L', 'A'], [⟨['o', 'v', 'e'], ['d', 'o', 'o', 'r'], none⟩, ⟨['s', 't', 'a'], ['E', 'L', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "negated"), ("entails", "negation")] }

def ex_44a : Datum :=
  { id := "nadathur2023_44a"
    source := ⟨"nadathur-2023-implicatives", "(44a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän laiminlö-i korjat-a virhee-n."
    glossedTokens := [("Hän", "he.NOM"), ("laiminlö-i", "neglect-PST.3SG"), ("korjat-a", "repair-INF"), ("virhee-n", "error-GEN/ACC")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['l', 'a', 'i', 'm', 'i', 'n', 'l', 'ö', '-', 'i'], ['n', 'e', 'g', 'l', 'e', 'c', 't', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['l', 'a', 'i', 'm', 'i', 'n', 'l', 'ö'], ['n', 'e', 'g', 'l', 'e', 'c', 't'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'o', 'r', 'j', 'a', 't', '-', 'a'], ['r', 'e', 'p', 'a', 'i', 'r', '-', 'I', 'N', 'F'], [⟨['k', 'o', 'r', 'j', 'a', 't'], ['r', 'e', 'p', 'a', 'i', 'r'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['v', 'i', 'r', 'h', 'e', 'e', '-', 'n'], ['e', 'r', 'r', 'o', 'r', '-', 'G', 'E', 'N', '/', 'A', 'C', 'C'], [⟨['v', 'i', 'r', 'h', 'e', 'e'], ['e', 'r', 'r', 'o', 'r'], none⟩, ⟨['n'], ['G', 'E', 'N', '/', 'A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "positive"), ("entails", "negation")] }

def ex_44b : Datum :=
  { id := "nadathur2023_44b"
    source := ⟨"nadathur-2023-implicatives", "(44b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i laiminlyö-nyt korjat-a virhe-ttä."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("laiminlyö-nyt", "neglect-PP.SG"), ("korjat-a", "repair-INF"), ("virhe-ttä", "error-PART")]
    glossedWords := [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], [⟨['H', 'ä', 'n'], ['h', 'e', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['l', 'a', 'i', 'm', 'i', 'n', 'l', 'y', 'ö', '-', 'n', 'y', 't'], ['n', 'e', 'g', 'l', 'e', 'c', 't', '-', 'P', 'P', '.', 'S', 'G'], [⟨['l', 'a', 'i', 'm', 'i', 'n', 'l', 'y', 'ö'], ['n', 'e', 'g', 'l', 'e', 'c', 't'], none⟩, ⟨['n', 'y', 't'], ['P', 'P', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['k', 'o', 'r', 'j', 'a', 't', '-', 'a'], ['r', 'e', 'p', 'a', 'i', 'r', '-', 'I', 'N', 'F'], [⟨['k', 'o', 'r', 'j', 'a', 't'], ['r', 'e', 'p', 'a', 'i', 'r'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['v', 'i', 'r', 'h', 'e', '-', 't', 't', 'ä'], ['e', 'r', 'r', 'o', 'r', '-', 'P', 'A', 'R', 'T'], [⟨['v', 'i', 'r', 'h', 'e'], ['e', 'r', 'r', 'o', 'r'], none⟩, ⟨['t', 't', 'ä'], ['P', 'A', 'R', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "negated"), ("entails", "complement")] }

def ex_46a : Datum :=
  { id := "nadathur2023_46a"
    source := ⟨"nadathur-2023-implicatives", "(46a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno epärö-i otta-a osa-a kilpailu-un."
    glossedTokens := [("Juno", "Juno"), ("epärö-i", "hesitate-PST.3SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    glossedWords := [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], none⟩]⟩, ⟨['e', 'p', 'ä', 'r', 'ö', '-', 'i'], ['h', 'e', 's', 'i', 't', 'a', 't', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['e', 'p', 'ä', 'r', 'ö'], ['h', 'e', 's', 'i', 't', 'a', 't', 'e'], none⟩, ⟨['i'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 't', 't', 'a', '-', 'a'], ['t', 'a', 'k', 'e', '-', 'I', 'N', 'F'], [⟨['o', 't', 't', 'a'], ['t', 'a', 'k', 'e'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['o', 's', 'a', '-', 'a'], ['p', 'a', 'r', 't', '-', 'P', 'A', 'R', 'T'], [⟨['o', 's', 'a'], ['p', 'a', 'r', 't'], none⟩, ⟨['a'], ['P', 'A', 'R', 'T'], some '-'⟩]⟩, ⟨['k', 'i', 'l', 'p', 'a', 'i', 'l', 'u', '-', 'u', 'n'], ['r', 'a', 'c', 'e', '-', 'I', 'L', 'L'], [⟨['k', 'i', 'l', 'p', 'a', 'i', 'l', 'u'], ['r', 'a', 'c', 'e'], none⟩, ⟨['u', 'n'], ['I', 'L', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_46b : Datum :=
  { id := "nadathur2023_46b"
    source := ⟨"nadathur-2023-implicatives", "(46b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i epäröi-nyt otta-a osa-a kilpailu-un."
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("epäröi-nyt", "hesitate-PP.SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    glossedWords := [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], [⟨['J', 'u', 'n', 'o'], ['J', 'u', 'n', 'o'], none⟩]⟩, ⟨['e', '-', 'i'], ['N', 'E', 'G', '-', '3', 'S', 'G'], [⟨['e'], ['N', 'E', 'G'], none⟩, ⟨['i'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['e', 'p', 'ä', 'r', 'ö', 'i', '-', 'n', 'y', 't'], ['h', 'e', 's', 'i', 't', 'a', 't', 'e', '-', 'P', 'P', '.', 'S', 'G'], [⟨['e', 'p', 'ä', 'r', 'ö', 'i'], ['h', 'e', 's', 'i', 't', 'a', 't', 'e'], none⟩, ⟨['n', 'y', 't'], ['P', 'P', '.', 'S', 'G'], some '-'⟩]⟩, ⟨['o', 't', 't', 'a', '-', 'a'], ['t', 'a', 'k', 'e', '-', 'I', 'N', 'F'], [⟨['o', 't', 't', 'a'], ['t', 'a', 'k', 'e'], none⟩, ⟨['a'], ['I', 'N', 'F'], some '-'⟩]⟩, ⟨['o', 's', 'a', '-', 'a'], ['p', 'a', 'r', 't', '-', 'P', 'A', 'R', 'T'], [⟨['o', 's', 'a'], ['p', 'a', 'r', 't'], none⟩, ⟨['a'], ['P', 'A', 'R', 'T'], some '-'⟩]⟩, ⟨['k', 'i', 'l', 'p', 'a', 'i', 'l', 'u', '-', 'u', 'n'], ['r', 'a', 'c', 'e', '-', 'I', 'L', 'L'], [⟨['k', 'i', 'l', 'p', 'a', 'i', 'l', 'u'], ['r', 'a', 'c', 'e'], none⟩, ⟨['u', 'n'], ['I', 'L', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "negated"), ("entails", "complement")] }

def all : List Datum := [ex_2a, ex_2b, ex_4a, ex_4b, ex_5a, ex_5b, ex_10a, ex_10b, ex_11a, ex_11b, ex_27a, ex_27b, ex_29a, ex_29b, ex_30a, ex_30b, ex_44a, ex_44b, ex_46a, ex_46b]

end Nadathur2023.Examples
