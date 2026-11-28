module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Chierchia1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Chierchia1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chierchia1998.Examples`.
-/

@[expose] public section

namespace Chierchia1998.Examples

def ex21a : Datum :=
  { id := "chierchia1998_ex21a"
    source := ⟨"chierchia-1998", "(21a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yí lì mǐ"
    glossedTokens := [("yí", "one"), ("lì", "CL"), ("mǐ", "rice")]
    glossedWords := [⟨['y', 'í'], ['o', 'n', 'e'], [⟨['y', 'í'], ['o', 'n', 'e'], none⟩]⟩, ⟨['l', 'ì'], ['C', 'L'], [⟨['l', 'ì'], ['C', 'L'], none⟩]⟩, ⟨['m', 'ǐ'], ['r', 'i', 'c', 'e'], [⟨['m', 'ǐ'], ['r', 'i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex21b : Datum :=
  { id := "chierchia1998_ex21b"
    source := ⟨"chierchia-1998", "(21b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "liǎng lì mǐ"
    glossedTokens := [("liǎng", "two"), ("lì", "CL"), ("mǐ", "rice")]
    glossedWords := [⟨['l', 'i', 'ǎ', 'n', 'g'], ['t', 'w', 'o'], [⟨['l', 'i', 'ǎ', 'n', 'g'], ['t', 'w', 'o'], none⟩]⟩, ⟨['l', 'ì'], ['C', 'L'], [⟨['l', 'ì'], ['C', 'L'], none⟩]⟩, ⟨['m', 'ǐ'], ['r', 'i', 'c', 'e'], [⟨['m', 'ǐ'], ['r', 'i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex21c : Datum :=
  { id := "chierchia1998_ex21c"
    source := ⟨"chierchia-1998", "(21c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yí zhāng zhuōzi"
    glossedTokens := [("yí", "one"), ("zhāng", "CL"), ("zhuōzi", "table")]
    glossedWords := [⟨['y', 'í'], ['o', 'n', 'e'], [⟨['y', 'í'], ['o', 'n', 'e'], none⟩]⟩, ⟨['z', 'h', 'ā', 'n', 'g'], ['C', 'L'], [⟨['z', 'h', 'ā', 'n', 'g'], ['C', 'L'], none⟩]⟩, ⟨['z', 'h', 'u', 'ō', 'z', 'i'], ['t', 'a', 'b', 'l', 'e'], [⟨['z', 'h', 'u', 'ō', 'z', 'i'], ['t', 'a', 'b', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex21d : Datum :=
  { id := "chierchia1998_ex21d"
    source := ⟨"chierchia-1998", "(21d)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "liǎng zhāng zhuōzi"
    glossedTokens := [("liǎng", "two"), ("zhāng", "CL"), ("zhuōzi", "table")]
    glossedWords := [⟨['l', 'i', 'ǎ', 'n', 'g'], ['t', 'w', 'o'], [⟨['l', 'i', 'ǎ', 'n', 'g'], ['t', 'w', 'o'], none⟩]⟩, ⟨['z', 'h', 'ā', 'n', 'g'], ['C', 'L'], [⟨['z', 'h', 'ā', 'n', 'g'], ['C', 'L'], none⟩]⟩, ⟨['z', 'h', 'u', 'ō', 'z', 'i'], ['t', 'a', 'b', 'l', 'e'], [⟨['z', 'h', 'u', 'ō', 'z', 'i'], ['t', 'a', 'b', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex21e : Datum :=
  { id := "chierchia1998_ex21e"
    source := ⟨"chierchia-1998", "(21e)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "wò kànjiàn xióng le"
    glossedTokens := [("wò", "I"), ("kànjiàn", "see"), ("xióng", "bear"), ("le", "ASP")]
    glossedWords := [⟨['w', 'ò'], ['I'], [⟨['w', 'ò'], ['I'], none⟩]⟩, ⟨['k', 'à', 'n', 'j', 'i', 'à', 'n'], ['s', 'e', 'e'], [⟨['k', 'à', 'n', 'j', 'i', 'à', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['x', 'i', 'ó', 'n', 'g'], ['b', 'e', 'a', 'r'], [⟨['x', 'i', 'ó', 'n', 'g'], ['b', 'e', 'a', 'r'], none⟩]⟩, ⟨['l', 'e'], ['A', 'S', 'P'], [⟨['l', 'e'], ['A', 'S', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "mass"), ("position", "governed"), ("predicate", "object")] }

def ex22a : Datum :=
  { id := "chierchia1998_ex22a"
    source := ⟨"chierchia-1998", "(22a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Enfants sont venus chez nous."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "object")] }

def ex22b : Datum :=
  { id := "chierchia1998_ex22b"
    source := ⟨"chierchia-1998", "(22b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai mangé biscuits dans mon lait."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "governed"), ("predicate", "object")] }

def ex23a : Datum :=
  { id := "chierchia1998_ex23a"
    source := ⟨"chierchia-1998", "(23a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Bambini sono venuti da noi."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "object")] }

def ex23b : Datum :=
  { id := "chierchia1998_ex23b"
    source := ⟨"chierchia-1998", "(23b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ho preso biscotti con il mio latte."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "governed"), ("predicate", "object")] }

def ex27a : Datum :=
  { id := "chierchia1998_ex27a"
    source := ⟨"chierchia-1998", "(27a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ja kupil khleb"
    glossedTokens := [("Ja", "I"), ("kupil", "bought"), ("khleb", "bread")]
    glossedWords := [⟨['J', 'a'], ['I'], [⟨['J', 'a'], ['I'], none⟩]⟩, ⟨['k', 'u', 'p', 'i', 'l'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'u', 'p', 'i', 'l'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['k', 'h', 'l', 'e', 'b'], ['b', 'r', 'e', 'a', 'd'], [⟨['k', 'h', 'l', 'e', 'b'], ['b', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ja kupil khliby", .ungrammatical)]
    readings := []
    paperFeatures := [("bare", "mass"), ("position", "governed"), ("predicate", "object")] }

def ex27b : Datum :=
  { id := "chierchia1998_ex27b"
    source := ⟨"chierchia-1998", "(27b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ja kupil 3 batona khleba"
    glossedTokens := [("Ja", "I"), ("kupil", "bought"), ("3", "3"), ("batona", "loafs"), ("khleba", "of_bread")]
    glossedWords := [⟨['J', 'a'], ['I'], [⟨['J', 'a'], ['I'], none⟩]⟩, ⟨['k', 'u', 'p', 'i', 'l'], ['b', 'o', 'u', 'g', 'h', 't'], [⟨['k', 'u', 'p', 'i', 'l'], ['b', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['3'], ['3'], [⟨['3'], ['3'], none⟩]⟩, ⟨['b', 'a', 't', 'o', 'n', 'a'], ['l', 'o', 'a', 'f', 's'], [⟨['b', 'a', 't', 'o', 'n', 'a'], ['l', 'o', 'a', 'f', 's'], none⟩]⟩, ⟨['k', 'h', 'l', 'e', 'b', 'a'], ['o', 'f', '_', 'b', 'r', 'e', 'a', 'd'], [⟨['k', 'h', 'l', 'e', 'b', 'a'], ['o', 'f', '_', 'b', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ja kupil 3 khleba", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex27c : Datum :=
  { id := "chierchia1998_ex27c"
    source := ⟨"chierchia-1998", "(27c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Na stole bylo neskolko sortov syra"
    glossedTokens := [("Na", "on"), ("stole", "the_table"), ("bylo", "were"), ("neskolko", "several"), ("sortov", "types_of"), ("syra", "cheese")]
    glossedWords := [⟨['N', 'a'], ['o', 'n'], [⟨['N', 'a'], ['o', 'n'], none⟩]⟩, ⟨['s', 't', 'o', 'l', 'e'], ['t', 'h', 'e', '_', 't', 'a', 'b', 'l', 'e'], [⟨['s', 't', 'o', 'l', 'e'], ['t', 'h', 'e', '_', 't', 'a', 'b', 'l', 'e'], none⟩]⟩, ⟨['b', 'y', 'l', 'o'], ['w', 'e', 'r', 'e'], [⟨['b', 'y', 'l', 'o'], ['w', 'e', 'r', 'e'], none⟩]⟩, ⟨['n', 'e', 's', 'k', 'o', 'l', 'k', 'o'], ['s', 'e', 'v', 'e', 'r', 'a', 'l'], [⟨['n', 'e', 's', 'k', 'o', 'l', 'k', 'o'], ['s', 'e', 'v', 'e', 'r', 'a', 'l'], none⟩]⟩, ⟨['s', 'o', 'r', 't', 'o', 'v'], ['t', 'y', 'p', 'e', 's', '_', 'o', 'f'], [⟨['s', 'o', 'r', 't', 'o', 'v'], ['t', 'y', 'p', 'e', 's', '_', 'o', 'f'], none⟩]⟩, ⟨['s', 'y', 'r', 'a'], ['c', 'h', 'e', 'e', 's', 'e'], [⟨['s', 'y', 'r', 'a'], ['c', 'h', 'e', 'e', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Na stole bylo neskolko syra", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex27d : Datum :=
  { id := "chierchia1998_ex27d"
    source := ⟨"chierchia-1998", "(27d)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "V komnate byli malcik i devocka. Ja obratilsja k malciky."
    glossedTokens := [("V", "in"), ("komnate", "(the)_room"), ("byli", "were"), ("malcik", "(a)_boy"), ("i", "and"), ("devocka.", "(a)_girl"), ("Ja", "I"), ("obratilsja", "turned"), ("k", "to"), ("malciky.", "(the)_boy")]
    glossedWords := [⟨['V'], ['i', 'n'], [⟨['V'], ['i', 'n'], none⟩]⟩, ⟨['k', 'o', 'm', 'n', 'a', 't', 'e'], ['(', 't', 'h', 'e', ')', '_', 'r', 'o', 'o', 'm'], [⟨['k', 'o', 'm', 'n', 'a', 't', 'e'], ['(', 't', 'h', 'e', ')', '_', 'r', 'o', 'o', 'm'], none⟩]⟩, ⟨['b', 'y', 'l', 'i'], ['w', 'e', 'r', 'e'], [⟨['b', 'y', 'l', 'i'], ['w', 'e', 'r', 'e'], none⟩]⟩, ⟨['m', 'a', 'l', 'c', 'i', 'k'], ['(', 'a', ')', '_', 'b', 'o', 'y'], [⟨['m', 'a', 'l', 'c', 'i', 'k'], ['(', 'a', ')', '_', 'b', 'o', 'y'], none⟩]⟩, ⟨['i'], ['a', 'n', 'd'], [⟨['i'], ['a', 'n', 'd'], none⟩]⟩, ⟨['d', 'e', 'v', 'o', 'c', 'k', 'a', '.'], ['(', 'a', ')', '_', 'g', 'i', 'r', 'l'], [⟨['d', 'e', 'v', 'o', 'c', 'k', 'a'], ['(', 'a', ')', '_', 'g', 'i', 'r', 'l'], none⟩]⟩, ⟨['J', 'a'], ['I'], [⟨['J', 'a'], ['I'], none⟩]⟩, ⟨['o', 'b', 'r', 'a', 't', 'i', 'l', 's', 'j', 'a'], ['t', 'u', 'r', 'n', 'e', 'd'], [⟨['o', 'b', 'r', 'a', 't', 'i', 'l', 's', 'j', 'a'], ['t', 'u', 'r', 'n', 'e', 'd'], none⟩]⟩, ⟨['k'], ['t', 'o'], [⟨['k'], ['t', 'o'], none⟩]⟩, ⟨['m', 'a', 'l', 'c', 'i', 'k', 'y', '.'], ['(', 't', 'h', 'e', ')', '_', 'b', 'o', 'y'], [⟨['m', 'a', 'l', 'c', 'i', 'k', 'y'], ['(', 't', 'h', 'e', ')', '_', 'b', 'o', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "singular"), ("position", "governed"), ("predicate", "object")] }

def ex27e : Datum :=
  { id := "chierchia1998_ex27e"
    source := ⟨"chierchia-1998", "(27e)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Dinosavry vymerli"
    glossedTokens := [("Dinosavry", "dinosaurs"), ("vymerli", "(are)_extinct")]
    glossedWords := [⟨['D', 'i', 'n', 'o', 's', 'a', 'v', 'r', 'y'], ['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 's'], [⟨['D', 'i', 'n', 'o', 's', 'a', 'v', 'r', 'y'], ['d', 'i', 'n', 'o', 's', 'a', 'u', 'r', 's'], none⟩]⟩, ⟨['v', 'y', 'm', 'e', 'r', 'l', 'i'], ['(', 'a', 'r', 'e', ')', '_', 'e', 'x', 't', 'i', 'n', 'c', 't'], [⟨['v', 'y', 'm', 'e', 'r', 'l', 'i'], ['(', 'a', 'r', 'e', ')', '_', 'e', 'x', 't', 'i', 'n', 'c', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "kind")] }

def ex27e_sg : Datum :=
  { id := "chierchia1998_ex27e_sg"
    source := ⟨"chierchia-1998", "(27e)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Dynosavr vymerli"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "singular"), ("position", "subject"), ("predicate", "kind")] }

def ex27f : Datum :=
  { id := "chierchia1998_ex27f"
    source := ⟨"chierchia-1998", "(27f)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "sobaka obycnoe zyvotnoe"
    glossedTokens := [("sobaka", "dog"), ("obycnoe", "common"), ("zyvotnoe", "animal")]
    glossedWords := [⟨['s', 'o', 'b', 'a', 'k', 'a'], ['d', 'o', 'g'], [⟨['s', 'o', 'b', 'a', 'k', 'a'], ['d', 'o', 'g'], none⟩]⟩, ⟨['o', 'b', 'y', 'c', 'n', 'o', 'e'], ['c', 'o', 'm', 'm', 'o', 'n'], [⟨['o', 'b', 'y', 'c', 'n', 'o', 'e'], ['c', 'o', 'm', 'm', 'o', 'n'], none⟩]⟩, ⟨['z', 'y', 'v', 'o', 't', 'n', 'o', 'e'], ['a', 'n', 'i', 'm', 'a', 'l'], [⟨['z', 'y', 'v', 'o', 't', 'n', 'o', 'e'], ['a', 'n', 'i', 'm', 'a', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "singular"), ("position", "subject"), ("predicate", "kind")] }

def ex29a : Datum :=
  { id := "chierchia1998_ex29a"
    source := ⟨"chierchia-1998", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gold is rare"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "mass"), ("position", "subject"), ("predicate", "kind")] }

def ex29b : Datum :=
  { id := "chierchia1998_ex29b"
    source := ⟨"chierchia-1998", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs are widespread"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "kind")] }

def ex32a : Datum :=
  { id := "chierchia1998_ex32a"
    source := ⟨"chierchia-1998", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lions are ruining my garden."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "object")] }

def ex38a : Datum :=
  { id := "chierchia1998_ex38a"
    source := ⟨"chierchia-1998", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dogs bark."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "object")] }

def ex72a : Datum :=
  { id := "chierchia1998_ex72a"
    source := ⟨"chierchia-1998", "(72a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Leo ha mangiato patate."
    glossedTokens := [("Leo", "Leo"), ("ha", "PAST"), ("mangiato", "eat"), ("patate", "potatoes")]
    glossedWords := [⟨['L', 'e', 'o'], ['L', 'e', 'o'], [⟨['L', 'e', 'o'], ['L', 'e', 'o'], none⟩]⟩, ⟨['h', 'a'], ['P', 'A', 'S', 'T'], [⟨['h', 'a'], ['P', 'A', 'S', 'T'], none⟩]⟩, ⟨['m', 'a', 'n', 'g', 'i', 'a', 't', 'o'], ['e', 'a', 't'], [⟨['m', 'a', 'n', 'g', 'i', 'a', 't', 'o'], ['e', 'a', 't'], none⟩]⟩, ⟨['p', 'a', 't', 'a', 't', 'e'], ['p', 'o', 't', 'a', 't', 'o', 'e', 's'], [⟨['p', 'a', 't', 'a', 't', 'e'], ['p', 'o', 't', 'a', 't', 'o', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "governed"), ("predicate", "object")] }

def ex72b : Datum :=
  { id := "chierchia1998_ex72b"
    source := ⟨"chierchia-1998", "(72b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Leo stermina ratti."
    glossedTokens := [("Leo", "Leo"), ("stermina", "exterminates"), ("ratti", "rats")]
    glossedWords := [⟨['L', 'e', 'o'], ['L', 'e', 'o'], [⟨['L', 'e', 'o'], ['L', 'e', 'o'], none⟩]⟩, ⟨['s', 't', 'e', 'r', 'm', 'i', 'n', 'a'], ['e', 'x', 't', 'e', 'r', 'm', 'i', 'n', 'a', 't', 'e', 's'], [⟨['s', 't', 'e', 'r', 'm', 'i', 'n', 'a'], ['e', 'x', 't', 'e', 'r', 'm', 'i', 'n', 'a', 't', 'e', 's'], none⟩]⟩, ⟨['r', 'a', 't', 't', 'i'], ['r', 'a', 't', 's'], [⟨['r', 'a', 't', 't', 'i'], ['r', 'a', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "governed"), ("predicate", "kind")] }

def ex72c : Datum :=
  { id := "chierchia1998_ex72c"
    source := ⟨"chierchia-1998", "(72c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Leo è andato da amici."
    glossedTokens := [("Leo", "Leo"), ("è", "PAST"), ("andato", "go"), ("da", "to"), ("amici", "friend")]
    glossedWords := [⟨['L', 'e', 'o'], ['L', 'e', 'o'], [⟨['L', 'e', 'o'], ['L', 'e', 'o'], none⟩]⟩, ⟨['è'], ['P', 'A', 'S', 'T'], [⟨['è'], ['P', 'A', 'S', 'T'], none⟩]⟩, ⟨['a', 'n', 'd', 'a', 't', 'o'], ['g', 'o'], [⟨['a', 'n', 'd', 'a', 't', 'o'], ['g', 'o'], none⟩]⟩, ⟨['d', 'a'], ['t', 'o'], [⟨['d', 'a'], ['t', 'o'], none⟩]⟩, ⟨['a', 'm', 'i', 'c', 'i'], ['f', 'r', 'i', 'e', 'n', 'd'], [⟨['a', 'm', 'i', 'c', 'i'], ['f', 'r', 'i', 'e', 'n', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "governed"), ("predicate", "object")] }

def ex74a : Datum :=
  { id := "chierchia1998_ex74a"
    source := ⟨"chierchia-1998", "(74a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Studenti hanno telefonato."
    glossedTokens := [("Studenti", "students"), ("hanno", "have"), ("telefonato", "phoned")]
    glossedWords := [⟨['S', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['S', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩, ⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'a', 't', 'o'], ['p', 'h', 'o', 'n', 'e', 'd'], [⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'a', 't', 'o'], ['p', 'h', 'o', 'n', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "object")] }

def ex74b : Datum :=
  { id := "chierchia1998_ex74b"
    source := ⟨"chierchia-1998", "(74b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Hanno telefonato studenti."
    glossedTokens := [("Hanno", "have"), ("telefonato", "called"), ("studenti", "students")]
    glossedWords := [⟨['H', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], [⟨['H', 'a', 'n', 'n', 'o'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'a', 't', 'o'], ['c', 'a', 'l', 'l', 'e', 'd'], [⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'a', 't', 'o'], ['c', 'a', 'l', 'l', 'e', 'd'], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['s', 't', 'u', 'd', 'e', 'n', 't', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "plural"), ("position", "subject"), ("predicate", "object")] }

def p356_water : Datum :=
  { id := "chierchia1998_p356_water"
    source := ⟨"chierchia-1998", "p. 356"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "water is dripping on the floor"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("bare", "mass"), ("position", "subject"), ("predicate", "object")] }

def p356_table : Datum :=
  { id := "chierchia1998_p356_table"
    source := ⟨"chierchia-1998", "p. 356"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "table is on the corner"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("bare", "singular"), ("position", "subject"), ("predicate", "object")] }

def all : List Datum := [ex21a, ex21b, ex21c, ex21d, ex21e, ex22a, ex22b, ex23a, ex23b, ex27a, ex27b, ex27c, ex27d, ex27e, ex27e_sg, ex27f, ex29a, ex29b, ex32a, ex38a, ex72a, ex72b, ex72c, ex74a, ex74b, p356_water, p356_table]

/-- The bare nominal argument of the example, by number. -/
inductive Bare where
  /-- singular: a singular count noun -/
  | singular
  /-- plural: a plural count noun -/
  | plural
  /-- mass: a mass noun, or a noun of a language whose nouns have no number -/
  | mass
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `bare`. -/
def bare (e : Datum) : Option Bare :=
  e.parse? "bare" [("singular", .singular), ("plural", .plural), ("mass", .mass)]

/-- Where the bare nominal stands. -/
inductive Position where
  /-- subject: the subject -/
  | subject
  /-- governed: the complement of a verb or a preposition -/
  | governed
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `position`. -/
def position (e : Datum) : Option Position :=
  e.parse? "position" [("subject", .subject), ("governed", .governed)]

/-- What the predicate of the bare nominal applies to. -/
inductive Predicate where
  /-- object: a predicate of objects -/
  | object
  /-- kind: a predicate of kinds, as *rare* or *extinct* -/
  | kind
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `predicate`. -/
def predicate (e : Datum) : Option Predicate :=
  e.parse? "predicate" [("object", .object), ("kind", .kind)]

/-- The examples of the paper. -/
inductive Example where
  | ex21a
  | ex21b
  | ex21c
  | ex21d
  | ex21e
  | ex22a
  | ex22b
  | ex23a
  | ex23b
  | ex27a
  | ex27b
  | ex27c
  | ex27d
  | ex27e
  | ex27e_sg
  | ex27f
  | ex29a
  | ex29b
  | ex32a
  | ex38a
  | ex72a
  | ex72b
  | ex72c
  | ex74a
  | ex74b
  | p356_water
  | p356_table
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex21a, .ex21b, .ex21c, .ex21d, .ex21e, .ex22a, .ex22b, .ex23a, .ex23b, .ex27a, .ex27b,
    .ex27c, .ex27d, .ex27e, .ex27e_sg, .ex27f, .ex29a, .ex29b, .ex32a, .ex38a, .ex72a, .ex72b,
    .ex72c, .ex74a, .ex74b, .p356_water, .p356_table]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex21a => _root_.Chierchia1998.Examples.ex21a
  | .ex21b => _root_.Chierchia1998.Examples.ex21b
  | .ex21c => _root_.Chierchia1998.Examples.ex21c
  | .ex21d => _root_.Chierchia1998.Examples.ex21d
  | .ex21e => _root_.Chierchia1998.Examples.ex21e
  | .ex22a => _root_.Chierchia1998.Examples.ex22a
  | .ex22b => _root_.Chierchia1998.Examples.ex22b
  | .ex23a => _root_.Chierchia1998.Examples.ex23a
  | .ex23b => _root_.Chierchia1998.Examples.ex23b
  | .ex27a => _root_.Chierchia1998.Examples.ex27a
  | .ex27b => _root_.Chierchia1998.Examples.ex27b
  | .ex27c => _root_.Chierchia1998.Examples.ex27c
  | .ex27d => _root_.Chierchia1998.Examples.ex27d
  | .ex27e => _root_.Chierchia1998.Examples.ex27e
  | .ex27e_sg => _root_.Chierchia1998.Examples.ex27e_sg
  | .ex27f => _root_.Chierchia1998.Examples.ex27f
  | .ex29a => _root_.Chierchia1998.Examples.ex29a
  | .ex29b => _root_.Chierchia1998.Examples.ex29b
  | .ex32a => _root_.Chierchia1998.Examples.ex32a
  | .ex38a => _root_.Chierchia1998.Examples.ex38a
  | .ex72a => _root_.Chierchia1998.Examples.ex72a
  | .ex72b => _root_.Chierchia1998.Examples.ex72b
  | .ex72c => _root_.Chierchia1998.Examples.ex72c
  | .ex74a => _root_.Chierchia1998.Examples.ex74a
  | .ex74b => _root_.Chierchia1998.Examples.ex74b
  | .p356_water => _root_.Chierchia1998.Examples.p356_water
  | .p356_table => _root_.Chierchia1998.Examples.p356_table

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Chierchia1998.Examples.all := rfl

/-- The value the example records under `bare`. -/
def Example.bare : Example → Option Bare
  | .ex21a => none
  | .ex21b => none
  | .ex21c => none
  | .ex21d => none
  | .ex21e => some .mass
  | .ex22a => some .plural
  | .ex22b => some .plural
  | .ex23a => some .plural
  | .ex23b => some .plural
  | .ex27a => some .mass
  | .ex27b => none
  | .ex27c => none
  | .ex27d => some .singular
  | .ex27e => some .plural
  | .ex27e_sg => some .singular
  | .ex27f => some .singular
  | .ex29a => some .mass
  | .ex29b => some .plural
  | .ex32a => some .plural
  | .ex38a => some .plural
  | .ex72a => some .plural
  | .ex72b => some .plural
  | .ex72c => some .plural
  | .ex74a => some .plural
  | .ex74b => some .plural
  | .p356_water => some .mass
  | .p356_table => some .singular

theorem Example.bare_datum :
    ∀ x : Example, _root_.Chierchia1998.Examples.bare x.datum = x.bare := by
  decide +kernel

/-- The value the example records under `position`. -/
def Example.position : Example → Option Position
  | .ex21a => none
  | .ex21b => none
  | .ex21c => none
  | .ex21d => none
  | .ex21e => some .governed
  | .ex22a => some .subject
  | .ex22b => some .governed
  | .ex23a => some .subject
  | .ex23b => some .governed
  | .ex27a => some .governed
  | .ex27b => none
  | .ex27c => none
  | .ex27d => some .governed
  | .ex27e => some .subject
  | .ex27e_sg => some .subject
  | .ex27f => some .subject
  | .ex29a => some .subject
  | .ex29b => some .subject
  | .ex32a => some .subject
  | .ex38a => some .subject
  | .ex72a => some .governed
  | .ex72b => some .governed
  | .ex72c => some .governed
  | .ex74a => some .subject
  | .ex74b => some .subject
  | .p356_water => some .subject
  | .p356_table => some .subject

theorem Example.position_datum :
    ∀ x : Example, _root_.Chierchia1998.Examples.position x.datum = x.position := by
  decide +kernel

/-- The value the example records under `predicate`. -/
def Example.predicate : Example → Option Predicate
  | .ex21a => none
  | .ex21b => none
  | .ex21c => none
  | .ex21d => none
  | .ex21e => some .object
  | .ex22a => some .object
  | .ex22b => some .object
  | .ex23a => some .object
  | .ex23b => some .object
  | .ex27a => some .object
  | .ex27b => none
  | .ex27c => none
  | .ex27d => some .object
  | .ex27e => some .kind
  | .ex27e_sg => some .kind
  | .ex27f => some .kind
  | .ex29a => some .kind
  | .ex29b => some .kind
  | .ex32a => some .object
  | .ex38a => some .object
  | .ex72a => some .object
  | .ex72b => some .kind
  | .ex72c => some .object
  | .ex74a => some .object
  | .ex74b => some .object
  | .p356_water => some .object
  | .p356_table => some .object

theorem Example.predicate_datum :
    ∀ x : Example, _root_.Chierchia1998.Examples.predicate x.datum = x.predicate := by
  decide +kernel

end Chierchia1998.Examples
