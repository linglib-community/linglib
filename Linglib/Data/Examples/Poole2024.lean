module

public import Linglib.Data.Examples.Schema

/-!
# `Poole2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Poole2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Poole2024.Examples`.
-/

@[expose] public section

namespace Poole2024.Examples

def ex15 : Datum :=
  { id := "poole2024_ex15"
    source := ⟨"poole-2024", "(15)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kinige-ni Masha-qa bier-di-m."
    glossedTokens := [("Min", "I"), ("kinige-ni", "book-ACC"), ("Masha-qa", "Masha-DAT"), ("bier-di-m", "give-PST-1SG")]
    glossedWords := [⟨['M', 'i', 'n'], ['I'], [⟨['M', 'i', 'n'], ['I'], none⟩]⟩, ⟨['k', 'i', 'n', 'i', 'g', 'e', '-', 'n', 'i'], ['b', 'o', 'o', 'k', '-', 'A', 'C', 'C'], [⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], none⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['M', 'a', 's', 'h', 'a', '-', 'q', 'a'], ['M', 'a', 's', 'h', 'a', '-', 'D', 'A', 'T'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩, ⟨['q', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'i', 'e', 'r', '-', 'd', 'i', '-', 'm'], ['g', 'i', 'v', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['b', 'i', 'e', 'r'], ['g', 'i', 'v', 'e'], none⟩, ⟨['d', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "yes")] }

def ex15_bare : Datum :=
  { id := "poole2024_ex15_bare"
    source := ⟨"poole-2024", "(15)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min kinige Masha-qa bier-di-m."
    glossedTokens := [("Min", "I"), ("kinige", "book"), ("Masha-qa", "Masha-DAT"), ("bier-di-m", "give-PST-1SG")]
    glossedWords := [⟨['M', 'i', 'n'], ['I'], [⟨['M', 'i', 'n'], ['I'], none⟩]⟩, ⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], [⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['M', 'a', 's', 'h', 'a', '-', 'q', 'a'], ['M', 'a', 's', 'h', 'a', '-', 'D', 'A', 'T'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩, ⟨['q', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'i', 'e', 'r', '-', 'd', 'i', '-', 'm'], ['g', 'i', 'v', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['b', 'i', 'e', 'r'], ['g', 'i', 'v', 'e'], none⟩, ⟨['d', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "yes"), ("licensor", "yes")] }

def ex18 : Datum :=
  { id := "poole2024_ex18"
    source := ⟨"poole-2024", "(18)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min Masha-qa kinige bier-di-m."
    glossedTokens := [("Min", "I"), ("Masha-qa", "Masha-DAT"), ("kinige", "book"), ("bier-di-m", "give-PST-1SG")]
    glossedWords := [⟨['M', 'i', 'n'], ['I'], [⟨['M', 'i', 'n'], ['I'], none⟩]⟩, ⟨['M', 'a', 's', 'h', 'a', '-', 'q', 'a'], ['M', 'a', 's', 'h', 'a', '-', 'D', 'A', 'T'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩, ⟨['q', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], [⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['b', 'i', 'e', 'r', '-', 'd', 'i', '-', 'm'], ['g', 'i', 'v', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['b', 'i', 'e', 'r'], ['g', 'i', 'v', 'e'], none⟩, ⟨['d', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "no"), ("licensor", "yes")] }

def ex18_acc : Datum :=
  { id := "poole2024_ex18_acc"
    source := ⟨"poole-2024", "(18)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Min Masha-qa kinige-ni bier-di-m."
    glossedTokens := [("Min", "I"), ("Masha-qa", "Masha-DAT"), ("kinige-ni", "book-ACC"), ("bier-di-m", "give-PST-1SG")]
    glossedWords := [⟨['M', 'i', 'n'], ['I'], [⟨['M', 'i', 'n'], ['I'], none⟩]⟩, ⟨['M', 'a', 's', 'h', 'a', '-', 'q', 'a'], ['M', 'a', 's', 'h', 'a', '-', 'D', 'A', 'T'], [⟨['M', 'a', 's', 'h', 'a'], ['M', 'a', 's', 'h', 'a'], none⟩, ⟨['q', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'i', 'g', 'e', '-', 'n', 'i'], ['b', 'o', 'o', 'k', '-', 'A', 'C', 'C'], [⟨['k', 'i', 'n', 'i', 'g', 'e'], ['b', 'o', 'o', 'k'], none⟩, ⟨['n', 'i'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['b', 'i', 'e', 'r', '-', 'd', 'i', '-', 'm'], ['g', 'i', 'v', 'e', '-', 'P', 'S', 'T', '-', '1', 'S', 'G'], [⟨['b', 'i', 'e', 'r'], ['g', 'i', 'v', 'e'], none⟩, ⟨['d', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['1', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "no"), ("licensor", "yes")] }

def ex20a : Datum :=
  { id := "poole2024_ex20a"
    source := ⟨"vinokurova-2005", "p. 366"⟩
    reportedIn := some ⟨"poole-2024", "(20a)"⟩
    language := "yaku1245"
    primaryText := "Keskil Aisen-y kel-bet dien xomoj-do."
    glossedTokens := [("Keskil", "Keskil"), ("Aisen-y", "Aisen-ACC"), ("kel-bet", "come-NEG.AOR.3SG"), ("dien", "that"), ("xomoj-do", "become.sad-PST.3SG")]
    glossedWords := [⟨['K', 'e', 's', 'k', 'i', 'l'], ['K', 'e', 's', 'k', 'i', 'l'], [⟨['K', 'e', 's', 'k', 'i', 'l'], ['K', 'e', 's', 'k', 'i', 'l'], none⟩]⟩, ⟨['A', 'i', 's', 'e', 'n', '-', 'y'], ['A', 'i', 's', 'e', 'n', '-', 'A', 'C', 'C'], [⟨['A', 'i', 's', 'e', 'n'], ['A', 'i', 's', 'e', 'n'], none⟩, ⟨['y'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'e', 'l', '-', 'b', 'e', 't'], ['c', 'o', 'm', 'e', '-', 'N', 'E', 'G', '.', 'A', 'O', 'R', '.', '3', 'S', 'G'], [⟨['k', 'e', 'l'], ['c', 'o', 'm', 'e'], none⟩, ⟨['b', 'e', 't'], ['N', 'E', 'G', '.', 'A', 'O', 'R', '.', '3', 'S', 'G'], some '-'⟩]⟩, ⟨['d', 'i', 'e', 'n'], ['t', 'h', 'a', 't'], [⟨['d', 'i', 'e', 'n'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['x', 'o', 'm', 'o', 'j', '-', 'd', 'o'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 's', 'a', 'd', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['x', 'o', 'm', 'o', 'j'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 's', 'a', 'd'], none⟩, ⟨['d', 'o'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "yes")] }

def ex20b : Datum :=
  { id := "poole2024_ex20b"
    source := ⟨"poole-2024", "(20b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Aisen-y massyyna atyylah-ar-a naada buol-la."
    glossedTokens := [("Aisen-y", "Aisen-ACC"), ("massyyna", "car"), ("atyylah-ar-a", "buy-AOR-3SG"), ("naada", "need"), ("buol-la", "become-PST.3SG")]
    glossedWords := [⟨['A', 'i', 's', 'e', 'n', '-', 'y'], ['A', 'i', 's', 'e', 'n', '-', 'A', 'C', 'C'], [⟨['A', 'i', 's', 'e', 'n'], ['A', 'i', 's', 'e', 'n'], none⟩, ⟨['y'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'a', 's', 's', 'y', 'y', 'n', 'a'], ['c', 'a', 'r'], [⟨['m', 'a', 's', 's', 'y', 'y', 'n', 'a'], ['c', 'a', 'r'], none⟩]⟩, ⟨['a', 't', 'y', 'y', 'l', 'a', 'h', '-', 'a', 'r', '-', 'a'], ['b', 'u', 'y', '-', 'A', 'O', 'R', '-', '3', 'S', 'G'], [⟨['a', 't', 'y', 'y', 'l', 'a', 'h'], ['b', 'u', 'y'], none⟩, ⟨['a', 'r'], ['A', 'O', 'R'], some '-'⟩, ⟨['a'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['n', 'a', 'a', 'd', 'a'], ['n', 'e', 'e', 'd'], [⟨['n', 'a', 'a', 'd', 'a'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['b', 'u', 'o', 'l', '-', 'l', 'a'], ['b', 'e', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['b', 'u', 'o', 'l'], ['b', 'e', 'c', 'o', 'm', 'e'], none⟩, ⟨['l', 'a'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("acc", "yes"), ("accessible", "yes"), ("licensor", "no")] }

def ex20b_bare : Datum :=
  { id := "poole2024_ex20b_bare"
    source := ⟨"poole-2024", "(20b)"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "Aisen massyyna atyylah-ar-a naada buol-la."
    glossedTokens := [("Aisen", "Aisen"), ("massyyna", "car"), ("atyylah-ar-a", "buy-AOR-3SG"), ("naada", "need"), ("buol-la", "become-PST.3SG")]
    glossedWords := [⟨['A', 'i', 's', 'e', 'n'], ['A', 'i', 's', 'e', 'n'], [⟨['A', 'i', 's', 'e', 'n'], ['A', 'i', 's', 'e', 'n'], none⟩]⟩, ⟨['m', 'a', 's', 's', 'y', 'y', 'n', 'a'], ['c', 'a', 'r'], [⟨['m', 'a', 's', 's', 'y', 'y', 'n', 'a'], ['c', 'a', 'r'], none⟩]⟩, ⟨['a', 't', 'y', 'y', 'l', 'a', 'h', '-', 'a', 'r', '-', 'a'], ['b', 'u', 'y', '-', 'A', 'O', 'R', '-', '3', 'S', 'G'], [⟨['a', 't', 'y', 'y', 'l', 'a', 'h'], ['b', 'u', 'y'], none⟩, ⟨['a', 'r'], ['A', 'O', 'R'], some '-'⟩, ⟨['a'], ['3', 'S', 'G'], some '-'⟩]⟩, ⟨['n', 'a', 'a', 'd', 'a'], ['n', 'e', 'e', 'd'], [⟨['n', 'a', 'a', 'd', 'a'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['b', 'u', 'o', 'l', '-', 'l', 'a'], ['b', 'e', 'c', 'o', 'm', 'e', '-', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['b', 'u', 'o', 'l'], ['b', 'e', 'c', 'o', 'm', 'e'], none⟩, ⟨['l', 'a'], ['P', 'S', 'T', '.', '3', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("acc", "no"), ("accessible", "yes"), ("licensor", "no")] }

def all : List Datum := [ex15, ex15_bare, ex18, ex18_acc, ex20a, ex20b, ex20b_bare]

end Poole2024.Examples
