module

public import Linglib.Data.Examples.Schema

/-!
# `Owusu2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Owusu2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Owusu2022.Examples`.
-/

@[expose] public section

namespace Owusu2022.Examples

def ex_3_21 : Datum :=
  { id := "owusu2022_3_21"
    source := ⟨"owusu-2022", "(21)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Onipa bí a-n-to dwom."
    glossedTokens := [("Onipa", "person"), ("bí", "INDEF"), ("a-n-to", "PERF-NEG-sing"), ("dwom", "song")]
    glossedWords := [⟨['O', 'n', 'i', 'p', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['O', 'n', 'i', 'p', 'a'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩, ⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], [⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩, ⟨['a', '-', 'n', '-', 't', 'o'], ['P', 'E', 'R', 'F', '-', 'N', 'E', 'G', '-', 's', 'i', 'n', 'g'], [⟨['a'], ['P', 'E', 'R', 'F'], none⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩, ⟨['t', 'o'], ['s', 'i', 'n', 'g'], some '-'⟩]⟩, ⟨['d', 'w', 'o', 'm'], ['s', 'o', 'n', 'g'], [⟨['d', 'w', 'o', 'm'], ['s', 'o', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable)]
    paperFeatures := [("operator", "negation"), ("position", "subject")] }

def ex_3_22 : Datum :=
  { id := "owusu2022_3_22"
    source := ⟨"owusu-2022", "(22)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-n-ni fish bí."
    glossedTokens := [("Me-n-ni", "1SG-NEG-eat"), ("fish", "fish"), ("bí", "INDEF")]
    glossedWords := [⟨['M', 'e', '-', 'n', '-', 'n', 'i'], ['1', 'S', 'G', '-', 'N', 'E', 'G', '-', 'e', 'a', 't'], [⟨['M', 'e'], ['1', 'S', 'G'], none⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩, ⟨['n', 'i'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['f', 'i', 's', 'h'], ['f', 'i', 's', 'h'], [⟨['f', 'i', 's', 'h'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], [⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .unacceptable), ("wide", .acceptable)]
    paperFeatures := [("operator", "negation"), ("position", "object")] }

def ex_3_23 : Datum :=
  { id := "owusu2022_3_23"
    source := ⟨"owusu-2022", "(23)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Sojani bí gyina pono biara ano."
    glossedTokens := [("Sojani", "soldier"), ("bí", "INDEF"), ("gyina", "stand"), ("pono", "door"), ("biara", "every"), ("ano", "mouth")]
    glossedWords := [⟨['S', 'o', 'j', 'a', 'n', 'i'], ['s', 'o', 'l', 'd', 'i', 'e', 'r'], [⟨['S', 'o', 'j', 'a', 'n', 'i'], ['s', 'o', 'l', 'd', 'i', 'e', 'r'], none⟩]⟩, ⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], [⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩, ⟨['g', 'y', 'i', 'n', 'a'], ['s', 't', 'a', 'n', 'd'], [⟨['g', 'y', 'i', 'n', 'a'], ['s', 't', 'a', 'n', 'd'], none⟩]⟩, ⟨['p', 'o', 'n', 'o'], ['d', 'o', 'o', 'r'], [⟨['p', 'o', 'n', 'o'], ['d', 'o', 'o', 'r'], none⟩]⟩, ⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], [⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['a', 'n', 'o'], ['m', 'o', 'u', 't', 'h'], [⟨['a', 'n', 'o'], ['m', 'o', 'u', 't', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable), ("narrow", .unacceptable)]
    paperFeatures := [("operator", "every"), ("position", "subject")] }

def ex_3_24 : Datum :=
  { id := "owusu2022_3_24"
    source := ⟨"owusu-2022", "(24)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "ɔbaa biara kane-e nhoma bí."
    glossedTokens := [("ɔbaa", "woman"), ("biara", "every"), ("kane-e", "read-PST"), ("nhoma", "book"), ("bí", "INDEF")]
    glossedWords := [⟨['ɔ', 'b', 'a', 'a'], ['w', 'o', 'm', 'a', 'n'], [⟨['ɔ', 'b', 'a', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], [⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['k', 'a', 'n', 'e', '-', 'e'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T'], [⟨['k', 'a', 'n', 'e'], ['r', 'e', 'a', 'd'], none⟩, ⟨['e'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['n', 'h', 'o', 'm', 'a'], ['b', 'o', 'o', 'k'], [⟨['n', 'h', 'o', 'm', 'a'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], [⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .acceptable)]
    paperFeatures := [("operator", "every"), ("position", "object")] }

def ex_3_29 : Datum :=
  { id := "owusu2022_3_29"
    source := ⟨"owusu-2022", "(29)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Dan n-ni ha."
    glossedTokens := [("Dan", "house"), ("n-ni", "NEG-be.located"), ("ha", "there")]
    glossedWords := [⟨['D', 'a', 'n'], ['h', 'o', 'u', 's', 'e'], [⟨['D', 'a', 'n'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['n', '-', 'n', 'i'], ['N', 'E', 'G', '-', 'b', 'e', '.', 'l', 'o', 'c', 'a', 't', 'e', 'd'], [⟨['n'], ['N', 'E', 'G'], none⟩, ⟨['n', 'i'], ['b', 'e', '.', 'l', 'o', 'c', 'a', 't', 'e', 'd'], some '-'⟩]⟩, ⟨['h', 'a'], ['t', 'h', 'e', 'r', 'e'], [⟨['h', 'a'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable)]
    paperFeatures := [("operator", "negation"), ("position", "subject")] }

def ex_3_30 : Datum :=
  { id := "owusu2022_3_30"
    source := ⟨"owusu-2022", "(30)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-n-ni fish."
    glossedTokens := [("Me-n-ni", "1SG-NEG-eat"), ("fish", "fish")]
    glossedWords := [⟨['M', 'e', '-', 'n', '-', 'n', 'i'], ['1', 'S', 'G', '-', 'N', 'E', 'G', '-', 'e', 'a', 't'], [⟨['M', 'e'], ['1', 'S', 'G'], none⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩, ⟨['n', 'i'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['f', 'i', 's', 'h'], ['f', 'i', 's', 'h'], [⟨['f', 'i', 's', 'h'], ['f', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("operator", "negation"), ("position", "object")] }

def ex_3_31 : Datum :=
  { id := "owusu2022_3_31"
    source := ⟨"owusu-2022", "(31)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "ɔbaa biara kane-e nhoma."
    glossedTokens := [("ɔbaa", "woman"), ("biara", "every"), ("kane-e", "read-PST"), ("nhoma", "book")]
    glossedWords := [⟨['ɔ', 'b', 'a', 'a'], ['w', 'o', 'm', 'a', 'n'], [⟨['ɔ', 'b', 'a', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], [⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['k', 'a', 'n', 'e', '-', 'e'], ['r', 'e', 'a', 'd', '-', 'P', 'S', 'T'], [⟨['k', 'a', 'n', 'e'], ['r', 'e', 'a', 'd'], none⟩, ⟨['e'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['n', 'h', 'o', 'm', 'a'], ['b', 'o', 'o', 'k'], [⟨['n', 'h', 'o', 'm', 'a'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("operator", "every"), ("position", "object")] }

def ex_3_32 : Datum :=
  { id := "owusu2022_3_32"
    source := ⟨"owusu-2022", "(32)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Sojani gyina pono biara ano."
    glossedTokens := [("Sojani", "soldier"), ("gyina", "stand"), ("pono", "door"), ("biara", "every"), ("ano", "mouth")]
    glossedWords := [⟨['S', 'o', 'j', 'a', 'n', 'i'], ['s', 'o', 'l', 'd', 'i', 'e', 'r'], [⟨['S', 'o', 'j', 'a', 'n', 'i'], ['s', 'o', 'l', 'd', 'i', 'e', 'r'], none⟩]⟩, ⟨['g', 'y', 'i', 'n', 'a'], ['s', 't', 'a', 'n', 'd'], [⟨['g', 'y', 'i', 'n', 'a'], ['s', 't', 'a', 'n', 'd'], none⟩]⟩, ⟨['p', 'o', 'n', 'o'], ['d', 'o', 'o', 'r'], [⟨['p', 'o', 'n', 'o'], ['d', 'o', 'o', 'r'], none⟩]⟩, ⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], [⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['a', 'n', 'o'], ['m', 'o', 'u', 't', 'h'], [⟨['a', 'n', 'o'], ['m', 'o', 'u', 't', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .unacceptable), ("narrow", .acceptable)]
    paperFeatures := [("operator", "every"), ("position", "subject")] }

def ex_3_57 : Datum :=
  { id := "owusu2022_3_57"
    source := ⟨"owusu-2022", "(57)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Sukuuni biara a-m-fa krataa bí àa ɔ-kyere-e a-n-kɔ."
    glossedTokens := [("Sukuuni", "student"), ("biara", "every"), ("a-m-fa", "PERF-NEG-take"), ("krataa", "paper"), ("bí", "INDEF"), ("àa", "REL"), ("ɔ-kyere-e", "3SG-write-PST"), ("a-n-kɔ", "PERF-NEG-go")]
    glossedWords := [⟨['S', 'u', 'k', 'u', 'u', 'n', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't'], [⟨['S', 'u', 'k', 'u', 'u', 'n', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], [⟨['b', 'i', 'a', 'r', 'a'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['a', '-', 'm', '-', 'f', 'a'], ['P', 'E', 'R', 'F', '-', 'N', 'E', 'G', '-', 't', 'a', 'k', 'e'], [⟨['a'], ['P', 'E', 'R', 'F'], none⟩, ⟨['m'], ['N', 'E', 'G'], some '-'⟩, ⟨['f', 'a'], ['t', 'a', 'k', 'e'], some '-'⟩]⟩, ⟨['k', 'r', 'a', 't', 'a', 'a'], ['p', 'a', 'p', 'e', 'r'], [⟨['k', 'r', 'a', 't', 'a', 'a'], ['p', 'a', 'p', 'e', 'r'], none⟩]⟩, ⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], [⟨['b', 'í'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩, ⟨['à', 'a'], ['R', 'E', 'L'], [⟨['à', 'a'], ['R', 'E', 'L'], none⟩]⟩, ⟨['ɔ', '-', 'k', 'y', 'e', 'r', 'e', '-', 'e'], ['3', 'S', 'G', '-', 'w', 'r', 'i', 't', 'e', '-', 'P', 'S', 'T'], [⟨['ɔ'], ['3', 'S', 'G'], none⟩, ⟨['k', 'y', 'e', 'r', 'e'], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['e'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['a', '-', 'n', '-', 'k', 'ɔ'], ['P', 'E', 'R', 'F', '-', 'N', 'E', 'G', '-', 'g', 'o'], [⟨['a'], ['P', 'E', 'R', 'F'], none⟩, ⟨['n'], ['N', 'E', 'G'], some '-'⟩, ⟨['k', 'ɔ'], ['g', 'o'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "There are three students, Alan, Bob and Carl. They all have three published papers. For their job application, they all submitted only two of their papers."
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .unacceptable)]
    paperFeatures := [("operator", "negation"), ("position", "object")] }

def all : List Datum := [ex_3_21, ex_3_22, ex_3_23, ex_3_24, ex_3_29, ex_3_30, ex_3_31, ex_3_32, ex_3_57]

end Owusu2022.Examples
