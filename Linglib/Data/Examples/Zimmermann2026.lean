module

public import Linglib.Data.Examples.Schema

/-!
# `Zimmermann2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Zimmermann2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zimmermann2026.Examples`.
-/

@[expose] public section

namespace Zimmermann2026.Examples

def ex_12 : Datum :=
  { id := "zimmermann2026_12"
    source := ⟨"zimmermann-2026", "(12)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "John ya karanta wani littafi, amma ban san ko wanne ba ne."
    glossedTokens := [("John", "John"), ("ya", "3SG.M.PFV"), ("karanta", "read"), ("wani", "INDEF"), ("littafi", "book"), ("amma", "but"), ("ban", "NEG-1SG"), ("san", "know"), ("ko", "Q"), ("wanne", "which"), ("ba", "NEG"), ("ne", "COP")]
    glossedWords := [⟨[['J', 'o', 'h', 'n']], [['J', 'o', 'h', 'n']]⟩, ⟨[['y', 'a']], [['3', 'S', 'G', '.', 'M', '.', 'P', 'F', 'V']]⟩, ⟨[['k', 'a', 'r', 'a', 'n', 't', 'a']], [['r', 'e', 'a', 'd']]⟩, ⟨[['w', 'a', 'n', 'i']], [['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['l', 'i', 't', 't', 'a', 'f', 'i']], [['b', 'o', 'o', 'k']]⟩, ⟨[['a', 'm', 'm', 'a']], [['b', 'u', 't']]⟩, ⟨[['b', 'a', 'n']], [['N', 'E', 'G'], ['1', 'S', 'G']]⟩, ⟨[['s', 'a', 'n']], [['k', 'n', 'o', 'w']]⟩, ⟨[['k', 'o']], [['Q']]⟩, ⟨[['w', 'a', 'n', 'n', 'e']], [['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩, ⟨[['n', 'e']], [['C', 'O', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "sluicing antecedent")] }

def ex_13a : Datum :=
  { id := "zimmermann2026_13a"
    source := ⟨"zimmermann-2014", ""⟩
    reportedIn := some ⟨"zimmermann-2026", "(13a)"⟩
    language := "haus1257"
    primaryText := "Audù bà-i sàyi wani kiifii ba."
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG.M"), ("sàyi", "buy"), ("wani", "INDEF"), ("kiifii", "fish"), ("ba", "NEG")]
    glossedWords := [⟨[['A', 'u', 'd', 'ù']], [['A', 'u', 'd', 'u']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G', '.', 'M']]⟩, ⟨[['s', 'à', 'y', 'i']], [['b', 'u', 'y']]⟩, ⟨[['w', 'a', 'n', 'i']], [['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['k', 'i', 'i', 'f', 'i', 'i']], [['f', 'i', 's', 'h']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "wide"), ("context", "Audu bought a lot of fish, but")] }

def ex_13b : Datum :=
  { id := "zimmermann2026_13b"
    source := ⟨"zimmermann-2014", ""⟩
    reportedIn := some ⟨"zimmermann-2026", "(13b)"⟩
    language := "haus1257"
    primaryText := "Audù bà-i sàyi wani kiifii ba."
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG.M"), ("sàyi", "buy"), ("wani", "INDEF"), ("kiifii", "fish"), ("ba", "NEG")]
    glossedWords := [⟨[['A', 'u', 'd', 'ù']], [['A', 'u', 'd', 'u']]⟩, ⟨[['b', 'à'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G', '.', 'M']]⟩, ⟨[['s', 'à', 'y', 'i']], [['b', 'u', 'y']]⟩, ⟨[['w', 'a', 'n', 'i']], [['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['k', 'i', 'i', 'f', 'i', 'i']], [['f', 'i', 's', 'h']]⟩, ⟨[['b', 'a']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "narrow"), ("context", "the market was closed, so")] }

def ex_14 : Datum :=
  { id := "zimmermann2026_14"
    source := ⟨"zimmermann-2026", "(14)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-re-kɔ-tɔ mpaboa bí."
    glossedTokens := [("Me-re-kɔ-tɔ", "1SG-PROG-go-buy"), ("mpaboa", "shoes"), ("bí", "INDEF")]
    glossedWords := [⟨[['M', 'e'], ['r', 'e'], ['k', 'ɔ'], ['t', 'ɔ']], [['1', 'S', 'G'], ['P', 'R', 'O', 'G'], ['g', 'o'], ['b', 'u', 'y']]⟩, ⟨[['m', 'p', 'a', 'b', 'o', 'a']], [['s', 'h', 'o', 'e', 's']]⟩, ⟨[['b', 'í']], [['I', 'N', 'D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "specificity")] }

def ex_15 : Datum :=
  { id := "zimmermann2026_15"
    source := ⟨"zimmermann-2026", "(15)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-n-ni fish bí."
    glossedTokens := [("Me-n-ni", "1SG-NEG-eat"), ("fish", "fish"), ("bí", "INDEF")]
    glossedWords := [⟨[['M', 'e'], ['n'], ['n', 'i']], [['1', 'S', 'G'], ['N', 'E', 'G'], ['e', 'a', 't']]⟩, ⟨[['f', 'i', 's', 'h']], [['f', 'i', 's', 'h']]⟩, ⟨[['b', 'í']], [['I', 'N', 'D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "wide only")] }

def ex_17 : Datum :=
  { id := "zimmermann2026_17"
    source := ⟨"zimmermann-2026", "(17)"⟩
    reportedIn := none
    language := "gaaa1244"
    primaryText := "Nikasel ko kɛ e-wolo ko ni e-ma lɛ e-ya-aa."
    glossedTokens := [("Nikasel", "student"), ("ko", "INDEF"), ("kɛ", "take"), ("e-wolo", "3SG.POSS-letter"), ("ko", "INDEF"), ("ni", "REL"), ("e-ma", "3SG-write"), ("lɛ", "DEF"), ("e-ya-aa", "3SG-send-NEG")]
    glossedWords := [⟨[['N', 'i', 'k', 'a', 's', 'e', 'l']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩, ⟨[['k', 'o']], [['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['k', 'ɛ']], [['t', 'a', 'k', 'e']]⟩, ⟨[['e'], ['w', 'o', 'l', 'o']], [['3', 'S', 'G', '.', 'P', 'O', 'S', 'S'], ['l', 'e', 't', 't', 'e', 'r']]⟩, ⟨[['k', 'o']], [['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['n', 'i']], [['R', 'E', 'L']]⟩, ⟨[['e'], ['m', 'a']], [['3', 'S', 'G'], ['w', 'r', 'i', 't', 'e']]⟩, ⟨[['l', 'ɛ']], [['D', 'E', 'F']]⟩, ⟨[['e'], ['y', 'a'], ['a', 'a']], [['3', 'S', 'G'], ['s', 'e', 'n', 'd'], ['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "There were three students: Mary, Sue, and Joe. All of them wrote letters, but none of them sent all of them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "ko"), ("reading", "existentially closed choice function")] }

def ex_18 : Datum :=
  { id := "zimmermann2026_18"
    source := ⟨"zimmermann-2026", "(18)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Papa bí nó bisa me me nɔma."
    glossedTokens := [("Papa", "man"), ("bí", "INDEF"), ("nó", "DEF"), ("bisa", "ask-PST"), ("me", "1SG"), ("me", "1SG"), ("nɔma", "number")]
    glossedWords := [⟨[['P', 'a', 'p', 'a']], [['m', 'a', 'n']]⟩, ⟨[['b', 'í']], [['I', 'N', 'D', 'E', 'F']]⟩, ⟨[['n', 'ó']], [['D', 'E', 'F']]⟩, ⟨[['b', 'i', 's', 'a']], [['a', 's', 'k'], ['P', 'S', 'T']]⟩, ⟨[['m', 'e']], [['1', 'S', 'G']]⟩, ⟨[['m', 'e']], [['1', 'S', 'G']]⟩, ⟨[['n', 'ɔ', 'm', 'a']], [['n', 'u', 'm', 'b', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("co-occurrence", "INDEF and DEF")] }

def ex_19 : Datum :=
  { id := "zimmermann2026_19"
    source := ⟨"zimmermann-2026", "(19)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "tùuluu yaa fashèe"
    glossedTokens := [("tùuluu", "pot"), ("yaa", "3SG.PFV"), ("fashèe", "break")]
    glossedWords := [⟨[['t', 'ù', 'u', 'l', 'u', 'u']], [['p', 'o', 't']]⟩, ⟨[['y', 'a', 'a']], [['3', 'S', 'G', '.', 'P', 'F', 'V']]⟩, ⟨[['f', 'a', 's', 'h', 'è', 'e']], [['b', 'r', 'e', 'a', 'k']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("bare NP", "definite or indefinite")] }

def all : List Datum := [ex_12, ex_13a, ex_13b, ex_14, ex_15, ex_17, ex_18, ex_19]

end Zimmermann2026.Examples
