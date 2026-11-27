module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `BaleKhanjian2014` — typed example data

Auto-generated from `Linglib/Data/Examples/BaleKhanjian2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BaleKhanjian2014.Examples`.
-/

@[expose] public section

namespace BaleKhanjian2014.Examples

def ex_3 : Datum :=
  { id := "balekhanjian2014_3"
    source := ⟨"bale-khanjian-2014", "(3)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəgha vazets."
    glossedTokens := [("Dəgha", "boy(SG)"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's'], ['r', 'u', 'n', '-', 'P', 'S', 'T'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "SG"), ("definite", "no"), ("reading", "general")] }

def ex_4a : Datum :=
  { id := "balekhanjian2014_4a"
    source := ⟨"bale-khanjian-2014", "(4a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə dəgha e."
    glossedTokens := [("John-ə", "John-DEF"), ("dəgha", "boy(SG)"), ("e", "is")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['e'], ['i', 's'], [⟨['e'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "atom"), ("number", "SG")] }

def ex_4b : Datum :=
  { id := "balekhanjian2014_4b"
    source := ⟨"bale-khanjian-2014", "(4b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə dəgha en."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("dəgha", "boy(SG)"), ("en", "are")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['y', 'e', 'v'], ['a', 'n', 'd'], [⟨['y', 'e', 'v'], ['a', 'n', 'd'], none⟩]⟩, ⟨['B', 'r', 'a', 'd', '-', 'ə'], ['B', 'r', 'a', 'd', '-', 'D', 'E', 'F'], [⟨['B', 'r', 'a', 'd'], ['B', 'r', 'a', 'd'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['e', 'n'], ['a', 'r', 'e'], [⟨['e', 'n'], ['a', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "SG")] }

def ex_5a : Datum :=
  { id := "balekhanjian2014_5a"
    source := ⟨"bale-khanjian-2014", "(5a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə yergu dəghaner en."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("yergu", "two"), ("dəgha-ner", "boy-PL"), ("en", "are")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['y', 'e', 'v'], ['a', 'n', 'd'], [⟨['y', 'e', 'v'], ['a', 'n', 'd'], none⟩]⟩, ⟨['B', 'r', 'a', 'd', '-', 'ə'], ['B', 'r', 'a', 'd', '-', 'D', 'E', 'F'], [⟨['B', 'r', 'a', 'd'], ['B', 'r', 'a', 'd'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['e', 'n'], ['a', 'r', 'e'], [⟨['e', 'n'], ['a', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "PL"), ("numeral", "two")] }

def ex_5b : Datum :=
  { id := "balekhanjian2014_5b"
    source := ⟨"bale-khanjian-2014", "(5b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə meg dəgha en/e."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("meg", "one"), ("dəgha", "boy"), ("en/e", "are/is")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['y', 'e', 'v'], ['a', 'n', 'd'], [⟨['y', 'e', 'v'], ['a', 'n', 'd'], none⟩]⟩, ⟨['B', 'r', 'a', 'd', '-', 'ə'], ['B', 'r', 'a', 'd', '-', 'D', 'E', 'F'], [⟨['B', 'r', 'a', 'd'], ['B', 'r', 'a', 'd'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['m', 'e', 'g'], ['o', 'n', 'e'], [⟨['m', 'e', 'g'], ['o', 'n', 'e'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩]⟩, ⟨['e', 'n', '/', 'e'], ['a', 'r', 'e', '/', 'i', 's'], [⟨['e', 'n', '/', 'e'], ['a', 'r', 'e', '/', 'i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "SG"), ("numeral", "one")] }

def ex_5c : Datum :=
  { id := "balekhanjian2014_5c"
    source := ⟨"bale-khanjian-2014", "(5c)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə dəgha mən e."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("dəgha", "boy"), ("mən", "INDEF(SG)"), ("e", "is")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['y', 'e', 'v'], ['a', 'n', 'd'], [⟨['y', 'e', 'v'], ['a', 'n', 'd'], none⟩]⟩, ⟨['B', 'r', 'a', 'd', '-', 'ə'], ['B', 'r', 'a', 'd', '-', 'D', 'E', 'F'], [⟨['B', 'r', 'a', 'd'], ['B', 'r', 'a', 'd'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩]⟩, ⟨['m', 'ə', 'n'], ['I', 'N', 'D', 'E', 'F', '(', 'S', 'G', ')'], [⟨['m', 'ə', 'n'], ['I', 'N', 'D', 'E', 'F', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['e'], ['i', 's'], [⟨['e'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicativeIndefinite"), ("subject", "group"), ("number", "SG")] }

def ex_6a : Datum :=
  { id := "balekhanjian2014_6a"
    source := ⟨"bale-khanjian-2014", "(6a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə yev Bradə dəghaner en."
    glossedTokens := [("John-ə", "John-DEF"), ("yev", "and"), ("Brad-ə", "Brad-DEF"), ("dəgha-ner", "boy-PL"), ("en", "are")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['y', 'e', 'v'], ['a', 'n', 'd'], [⟨['y', 'e', 'v'], ['a', 'n', 'd'], none⟩]⟩, ⟨['B', 'r', 'a', 'd', '-', 'ə'], ['B', 'r', 'a', 'd', '-', 'D', 'E', 'F'], [⟨['B', 'r', 'a', 'd'], ['B', 'r', 'a', 'd'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['e', 'n'], ['a', 'r', 'e'], [⟨['e', 'n'], ['a', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "group"), ("number", "PL")] }

def ex_6b : Datum :=
  { id := "balekhanjian2014_6b"
    source := ⟨"bale-khanjian-2014", "(6b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Johnə dəghaner e."
    glossedTokens := [("John-ə", "John-DEF"), ("dəgha-ner", "boy-PL"), ("e", "is")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'ə'], ['J', 'o', 'h', 'n', '-', 'D', 'E', 'F'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['e'], ['i', 's'], [⟨['e'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "predicative"), ("subject", "atom"), ("number", "PL")] }

def ex_7 : Datum :=
  { id := "balekhanjian2014_7"
    source := ⟨"bale-khanjian-2014", "(7)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəghaner vazetsin."
    glossedTokens := [("Dəgha-ner", "boy-PL"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨['D', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's', '-', 'i', 'n'], ['r', 'u', 'n', '-', 'P', 'S', 'T', '-', '3', 'P', 'L'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "PL"), ("definite", "no"), ("reading", "strictPlural")] }

def ex_8a : Datum :=
  { id := "balekhanjian2014_8a"
    source := ⟨"bale-khanjian-2014", "(8a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen mart vor bəzdigner uner vodki gajnetsav."
    glossedTokens := [("Amen", "all"), ("mart", "person"), ("vor", "that"), ("bəzdig-ner", "child-PL"), ("uner", "had"), ("vodk-i", "foot-DAT"), ("gajne-tsav", "stand.up-PST")]
    glossedWords := [⟨['A', 'm', 'e', 'n'], ['a', 'l', 'l'], [⟨['A', 'm', 'e', 'n'], ['a', 'l', 'l'], none⟩]⟩, ⟨['m', 'a', 'r', 't'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['m', 'a', 'r', 't'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['v', 'o', 'r'], ['t', 'h', 'a', 't'], [⟨['v', 'o', 'r'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['b', 'ə', 'z', 'd', 'i', 'g', '-', 'n', 'e', 'r'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['b', 'ə', 'z', 'd', 'i', 'g'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['u', 'n', 'e', 'r'], ['h', 'a', 'd'], [⟨['u', 'n', 'e', 'r'], ['h', 'a', 'd'], none⟩]⟩, ⟨['v', 'o', 'd', 'k', '-', 'i'], ['f', 'o', 'o', 't', '-', 'D', 'A', 'T'], [⟨['v', 'o', 'd', 'k'], ['f', 'o', 'o', 't'], none⟩, ⟨['i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['g', 'a', 'j', 'n', 'e', '-', 't', 's', 'a', 'v'], ['s', 't', 'a', 'n', 'd', '.', 'u', 'p', '-', 'P', 'S', 'T'], [⟨['g', 'a', 'j', 'n', 'e'], ['s', 't', 'a', 'n', 'd', '.', 'u', 'p'], none⟩, ⟨['t', 's', 'a', 'v'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("construction", "restrictor"), ("number", "PL"), ("reading", "strictPlural")] }

def ex_8b : Datum :=
  { id := "balekhanjian2014_8b"
    source := ⟨"bale-khanjian-2014", "(8b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen mart vor bəzdig uner vodki gajnetsav."
    glossedTokens := [("Amen", "all"), ("mart", "person"), ("vor", "that"), ("bəzdig", "child(SG)"), ("uner", "had"), ("vodk-i", "foot-DAT"), ("gajne-tsav", "stand.up-PST")]
    glossedWords := [⟨['A', 'm', 'e', 'n'], ['a', 'l', 'l'], [⟨['A', 'm', 'e', 'n'], ['a', 'l', 'l'], none⟩]⟩, ⟨['m', 'a', 'r', 't'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['m', 'a', 'r', 't'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['v', 'o', 'r'], ['t', 'h', 'a', 't'], [⟨['v', 'o', 'r'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['b', 'ə', 'z', 'd', 'i', 'g'], ['c', 'h', 'i', 'l', 'd', '(', 'S', 'G', ')'], [⟨['b', 'ə', 'z', 'd', 'i', 'g'], ['c', 'h', 'i', 'l', 'd', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['u', 'n', 'e', 'r'], ['h', 'a', 'd'], [⟨['u', 'n', 'e', 'r'], ['h', 'a', 'd'], none⟩]⟩, ⟨['v', 'o', 'd', 'k', '-', 'i'], ['f', 'o', 'o', 't', '-', 'D', 'A', 'T'], [⟨['v', 'o', 'd', 'k'], ['f', 'o', 'o', 't'], none⟩, ⟨['i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['g', 'a', 'j', 'n', 'e', '-', 't', 's', 'a', 'v'], ['s', 't', 'a', 'n', 'd', '.', 'u', 'p', '-', 'P', 'S', 'T'], [⟨['g', 'a', 'j', 'n', 'e'], ['s', 't', 'a', 'n', 'd', '.', 'u', 'p'], none⟩, ⟨['t', 's', 'a', 'v'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "restrictor"), ("number", "SG"), ("reading", "general")] }

def ex_10a : Datum :=
  { id := "balekhanjian2014_10a"
    source := ⟨"bale-khanjian-2014", "(10a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəgha vazets."
    glossedTokens := [("Yergu", "two"), ("dəgha", "boy(SG)"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's'], ['r', 'u', 'n', '-', 'P', 'S', 'T'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "SG"), ("numeral", "two"), ("definite", "no")] }

def ex_10b : Datum :=
  { id := "balekhanjian2014_10b"
    source := ⟨"bale-khanjian-2014", "(10b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghaner vazetsin."
    glossedTokens := [("Yergu", "two"), ("dəgha-ner", "boy-PL"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's', '-', 'i', 'n'], ['r', 'u', 'n', '-', 'P', 'S', 'T', '-', '3', 'P', 'L'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "existential"), ("number", "PL"), ("numeral", "two"), ("definite", "no")] }

def ex_11b : Datum :=
  { id := "balekhanjian2014_11b"
    source := ⟨"bale-khanjian-2014", "(11b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəghan vazets."
    glossedTokens := [("Dəgha-n", "boy(SG)-DEF"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨['D', 'ə', 'g', 'h', 'a', '-', 'n'], ['b', 'o', 'y', '(', 'S', 'G', ')', '-', 'D', 'E', 'F'], [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩, ⟨['n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's'], ['r', 'u', 'n', '-', 'P', 'S', 'T'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "definite"), ("number", "SG"), ("definite", "yes"), ("reading", "strictSingular")] }

def ex_13a : Datum :=
  { id := "balekhanjian2014_13a"
    source := ⟨"bale-khanjian-2014", "(13a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen dəgha ir kirkerə kənadz e."
    glossedTokens := [("Amen", "every"), ("dəgha", "boy"), ("ir", "3SG.HUMAN.GEN"), ("kirk-er-ə", "book-PL-DEF"), ("kənadz", "buy.PRF"), ("e", "be.3SG")]
    glossedWords := [⟨['A', 'm', 'e', 'n'], ['e', 'v', 'e', 'r', 'y'], [⟨['A', 'm', 'e', 'n'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩]⟩, ⟨['i', 'r'], ['3', 'S', 'G', '.', 'H', 'U', 'M', 'A', 'N', '.', 'G', 'E', 'N'], [⟨['i', 'r'], ['3', 'S', 'G', '.', 'H', 'U', 'M', 'A', 'N', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['k', 'i', 'r', 'k', '-', 'e', 'r', '-', 'ə'], ['b', 'o', 'o', 'k', '-', 'P', 'L', '-', 'D', 'E', 'F'], [⟨['k', 'i', 'r', 'k'], ['b', 'o', 'o', 'k'], none⟩, ⟨['e', 'r'], ['P', 'L'], some '-'⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['k', 'ə', 'n', 'a', 'd', 'z'], ['b', 'u', 'y', '.', 'P', 'R', 'F'], [⟨['k', 'ə', 'n', 'a', 'd', 'z'], ['b', 'u', 'y', '.', 'P', 'R', 'F'], none⟩]⟩, ⟨['e'], ['b', 'e', '.', '3', 'S', 'G'], [⟨['e'], ['b', 'e', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "boundPossessive"), ("number", "PL"), ("definite", "yes"), ("reading", "strictPlural")] }

def ex_13b : Datum :=
  { id := "balekhanjian2014_13b"
    source := ⟨"bale-khanjian-2014", "(13b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Amen dəgha ir kirkə kənadz e."
    glossedTokens := [("Amen", "every"), ("dəgha", "boy"), ("ir", "3SG.HUMAN.GEN"), ("kirk-ə", "book-DEF"), ("kənadz", "buy.PRF"), ("e", "be.3SG")]
    glossedWords := [⟨['A', 'm', 'e', 'n'], ['e', 'v', 'e', 'r', 'y'], [⟨['A', 'm', 'e', 'n'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩]⟩, ⟨['i', 'r'], ['3', 'S', 'G', '.', 'H', 'U', 'M', 'A', 'N', '.', 'G', 'E', 'N'], [⟨['i', 'r'], ['3', 'S', 'G', '.', 'H', 'U', 'M', 'A', 'N', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['k', 'i', 'r', 'k', '-', 'ə'], ['b', 'o', 'o', 'k', '-', 'D', 'E', 'F'], [⟨['k', 'i', 'r', 'k'], ['b', 'o', 'o', 'k'], none⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['k', 'ə', 'n', 'a', 'd', 'z'], ['b', 'u', 'y', '.', 'P', 'R', 'F'], [⟨['k', 'ə', 'n', 'a', 'd', 'z'], ['b', 'u', 'y', '.', 'P', 'R', 'F'], none⟩]⟩, ⟨['e'], ['b', 'e', '.', '3', 'S', 'G'], [⟨['e'], ['b', 'e', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "boundPossessive"), ("number", "SG"), ("definite", "yes"), ("reading", "strictSingular")] }

def ex_14a : Datum :=
  { id := "balekhanjian2014_14a"
    source := ⟨"bale-khanjian-2014", "(14a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghan vazets."
    glossedTokens := [("Yergu", "two"), ("dəgha-n", "boy(SG)-DEF"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n'], ['b', 'o', 'y', '(', 'S', 'G', ')', '-', 'D', 'E', 'F'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩, ⟨['n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's'], ['r', 'u', 'n', '-', 'P', 'S', 'T'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "definite"), ("number", "SG"), ("numeral", "two"), ("definite", "yes")] }

def ex_14b : Datum :=
  { id := "balekhanjian2014_14b"
    source := ⟨"bale-khanjian-2014", "(14b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghanerə vazetsin."
    glossedTokens := [("Yergu", "two"), ("dəgha-ner-ə", "boy-PL-DEF"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r', '-', 'ə'], ['b', 'o', 'y', '-', 'P', 'L', '-', 'D', 'E', 'F'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩, ⟨['ə'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's', '-', 'i', 'n'], ['r', 'u', 'n', '-', 'P', 'S', 'T', '-', '3', 'P', 'L'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "definite"), ("number", "PL"), ("numeral", "two"), ("definite", "yes")] }

def ex_24a : Datum :=
  { id := "balekhanjian2014_24a"
    source := ⟨"bale-khanjian-2014", "(24a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəgha chi vazets."
    glossedTokens := [("Dəgha", "boy(SG)"), ("chi", "not"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['c', 'h', 'i'], ['n', 'o', 't'], [⟨['c', 'h', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's'], ['r', 'u', 'n', '-', 'P', 'S', 'T'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "SG"), ("definite", "no"), ("scopeAmbiguous", "no")] }

def ex_25a : Datum :=
  { id := "balekhanjian2014_25a"
    source := ⟨"bale-khanjian-2014", "(25a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Dəghaner chi vazetsin."
    glossedTokens := [("Dəgha-ner", "boy-PL"), ("chi", "not"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨['D', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['D', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['c', 'h', 'i'], ['n', 'o', 't'], [⟨['c', 'h', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's', '-', 'i', 'n'], ['r', 'u', 'n', '-', 'P', 'S', 'T', '-', '3', 'P', 'L'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "PL"), ("definite", "no"), ("scopeAmbiguous", "yes")] }

def ex_26a : Datum :=
  { id := "balekhanjian2014_26a"
    source := ⟨"bale-khanjian-2014", "(26a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəgha chi vazets."
    glossedTokens := [("Yergu", "two"), ("dəgha", "boy(SG)"), ("chi", "not"), ("vaze-ts", "run-PST")]
    glossedWords := [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y', '(', 'S', 'G', ')'], none⟩]⟩, ⟨['c', 'h', 'i'], ['n', 'o', 't'], [⟨['c', 'h', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's'], ['r', 'u', 'n', '-', 'P', 'S', 'T'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "SG"), ("numeral", "two"), ("definite", "no"), ("scopeAmbiguous", "yes")] }

def ex_27a : Datum :=
  { id := "balekhanjian2014_27a"
    source := ⟨"bale-khanjian-2014", "(27a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "Yergu dəghaner chi vazetsin."
    glossedTokens := [("Yergu", "two"), ("dəgha-ner", "boy-PL"), ("chi", "not"), ("vaze-ts-in", "run-PST-3PL")]
    glossedWords := [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], [⟨['Y', 'e', 'r', 'g', 'u'], ['t', 'w', 'o'], none⟩]⟩, ⟨['d', 'ə', 'g', 'h', 'a', '-', 'n', 'e', 'r'], ['b', 'o', 'y', '-', 'P', 'L'], [⟨['d', 'ə', 'g', 'h', 'a'], ['b', 'o', 'y'], none⟩, ⟨['n', 'e', 'r'], ['P', 'L'], some '-'⟩]⟩, ⟨['c', 'h', 'i'], ['n', 'o', 't'], [⟨['c', 'h', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['v', 'a', 'z', 'e', '-', 't', 's', '-', 'i', 'n'], ['r', 'u', 'n', '-', 'P', 'S', 'T', '-', '3', 'P', 'L'], [⟨['v', 'a', 'z', 'e'], ['r', 'u', 'n'], none⟩, ⟨['t', 's'], ['P', 'S', 'T'], some '-'⟩, ⟨['i', 'n'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "negated"), ("number", "PL"), ("numeral", "two"), ("definite", "no"), ("scopeAmbiguous", "yes")] }

def all : List Datum := [ex_3, ex_4a, ex_4b, ex_5a, ex_5b, ex_5c, ex_6a, ex_6b, ex_7, ex_8a, ex_8b, ex_10a, ex_10b, ex_11b, ex_13a, ex_13b, ex_14a, ex_14b, ex_24a, ex_25a, ex_26a, ex_27a]

/-- The head of the number phrase: the null singular *-∅* or the plural *-ner*. -/
inductive NumberHead where
  /-- SG: SG -/
  | sg
  /-- PL: PL -/
  | pl
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `number`. -/
def number (e : Datum) : Option NumberHead :=
  e.parse? "number" [("SG", .sg), ("PL", .pl)]

/-- Whether the subject denotes one individual or several. -/
inductive Subject where
  /-- atom: a single individual -/
  | atom
  /-- group: a conjunction of two individuals -/
  | group
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option Subject :=
  e.parse? "subject" [("atom", .atom), ("group", .group)]

end BaleKhanjian2014.Examples
