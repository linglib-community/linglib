module

public import Linglib.Data.Examples.Schema

/-!
# `MitrovicSauerland2016` — typed example data

Auto-generated from `Linglib/Data/Examples/MitrovicSauerland2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MitrovicSauerland2016.Examples`.
-/

@[expose] public section

namespace MitrovicSauerland2016.Examples

def ex1c : Datum :=
  { id := "mitrovicsauerland2016_ex1c"
    source := ⟨"mitrovic-sauerland-2016", "(1c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mary-mo John-mo wakaru"
    glossedTokens := [("Mary-mo", "M-μ"), ("John-mo", "J-μ"), ("wakaru", "understand")]
    glossedWords := [⟨['M', 'a', 'r', 'y', '-', 'm', 'o'], ['M', '-', 'μ'], [⟨['M', 'a', 'r', 'y'], ['M'], none⟩, ⟨['m', 'o'], ['μ'], some '-'⟩]⟩, ⟨['J', 'o', 'h', 'n', '-', 'm', 'o'], ['J', '-', 'μ'], [⟨['J', 'o', 'h', 'n'], ['J'], none⟩, ⟨['m', 'o'], ['μ'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'a', 'r', 'u'], ['u', 'n', 'd', 'e', 'r', 's', 't', 'a', 'n', 'd'], [⟨['w', 'a', 'k', 'a', 'r', 'u'], ['u', 'n', 'd', 'e', 'r', 's', 't', 'a', 'n', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "mu-second")] }

def ex1c_omitted : Datum :=
  { id := "mitrovicsauerland2016_ex1c_omitted"
    source := ⟨"mitrovic-sauerland-2016", "(1c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mary John-mo wakaru"
    glossedTokens := [("Mary", "M"), ("John-mo", "J-μ"), ("wakaru", "understand")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M'], [⟨['M', 'a', 'r', 'y'], ['M'], none⟩]⟩, ⟨['J', 'o', 'h', 'n', '-', 'm', 'o'], ['J', '-', 'μ'], [⟨['J', 'o', 'h', 'n'], ['J'], none⟩, ⟨['m', 'o'], ['μ'], some '-'⟩]⟩, ⟨['w', 'a', 'k', 'a', 'r', 'u'], ['u', 'n', 'd', 'e', 'r', 's', 't', 'a', 'n', 'd'], [⟨['w', 'a', 'k', 'a', 'r', 'u'], ['u', 'n', 'd', 'e', 'r', 's', 't', 'a', 'n', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-second")] }

def ex23 : Datum :=
  { id := "mitrovicsauerland2016_ex23"
    source := ⟨"mitrovic-sauerland-2016", "(23)"⟩
    reportedIn := none
    language := "mace1250"
    primaryText := "Roska i Ivan"
    glossedTokens := [("Roska", "R"), ("i", "J⁰"), ("Ivan", "I")]
    glossedWords := [⟨['R', 'o', 's', 'k', 'a'], ['R'], [⟨['R', 'o', 's', 'k', 'a'], ['R'], none⟩]⟩, ⟨['i'], ['J', '⁰'], [⟨['i'], ['J', '⁰'], none⟩]⟩, ⟨['I', 'v', 'a', 'n'], ['I'], [⟨['I', 'v', 'a', 'n'], ['I'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "j")] }

def ex24 : Datum :=
  { id := "mitrovicsauerland2016_ex24"
    source := ⟨"mitrovic-sauerland-2016", "(24)"⟩
    reportedIn := none
    language := "mace1250"
    primaryText := "i Roska i Ivan"
    glossedTokens := [("i", "μ⁰"), ("Roska", "R"), ("i", "μ⁰"), ("Ivan", "I")]
    glossedWords := [⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['R', 'o', 's', 'k', 'a'], ['R'], [⟨['R', 'o', 's', 'k', 'a'], ['R'], none⟩]⟩, ⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['I', 'v', 'a', 'n'], ['I'], [⟨['I', 'v', 'a', 'n'], ['I'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "mu-second")] }

def ex25 : Datum :=
  { id := "mitrovicsauerland2016_ex25"
    source := ⟨"mitrovic-sauerland-2016", "(25)"⟩
    reportedIn := none
    language := "mace1250"
    primaryText := "Roska i i Ivan"
    glossedTokens := [("Roska", "R"), ("i", "J⁰"), ("i", "μ⁰"), ("Ivan", "I")]
    glossedWords := [⟨['R', 'o', 's', 'k', 'a'], ['R'], [⟨['R', 'o', 's', 'k', 'a'], ['R'], none⟩]⟩, ⟨['i'], ['J', '⁰'], [⟨['i'], ['J', '⁰'], none⟩]⟩, ⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['I', 'v', 'a', 'n'], ['I'], [⟨['I', 'v', 'a', 'n'], ['I'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "j"), ("head", "mu-second")] }

def ex26 : Datum :=
  { id := "mitrovicsauerland2016_ex26"
    source := ⟨"mitrovic-sauerland-2016", "(26)"⟩
    reportedIn := none
    language := "mace1250"
    primaryText := "i Roska i i Ivan"
    glossedTokens := [("i", "μ⁰"), ("Roska", "R"), ("i", "J⁰"), ("i", "μ⁰"), ("Ivan", "I")]
    glossedWords := [⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['R', 'o', 's', 'k', 'a'], ['R'], [⟨['R', 'o', 's', 'k', 'a'], ['R'], none⟩]⟩, ⟨['i'], ['J', '⁰'], [⟨['i'], ['J', '⁰'], none⟩]⟩, ⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['I', 'v', 'a', 'n'], ['I'], [⟨['I', 'v', 'a', 'n'], ['I'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "j"), ("head", "mu-second")] }

def ex27 : Datum :=
  { id := "mitrovicsauerland2016_ex27"
    source := ⟨"mitrovic-sauerland-2016", "(27)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "i Mujo a i Haso"
    glossedTokens := [("i", "μ⁰"), ("Mujo", "M"), ("a", "J⁰.but"), ("i", "μ⁰"), ("Haso", "H")]
    glossedWords := [⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['M', 'u', 'j', 'o'], ['M'], [⟨['M', 'u', 'j', 'o'], ['M'], none⟩]⟩, ⟨['a'], ['J', '⁰', '.', 'b', 'u', 't'], [⟨['a'], ['J', '⁰', '.', 'b', 'u', 't'], none⟩]⟩, ⟨['i'], ['μ', '⁰'], [⟨['i'], ['μ', '⁰'], none⟩]⟩, ⟨['H', 'a', 's', 'o'], ['H'], [⟨['H', 'a', 's', 'o'], ['H'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "j"), ("head", "mu-second"), ("junctor", "adversative")] }

def ex28 : Datum :=
  { id := "mitrovicsauerland2016_ex28"
    source := ⟨"mitrovic-sauerland-2016", "(28)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati is és Mari is"
    glossedTokens := [("Kati", "K"), ("is", "μ"), ("és", "J"), ("Mari", "M"), ("is", "μ")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K'], [⟨['K', 'a', 't', 'i'], ['K'], none⟩]⟩, ⟨['i', 's'], ['μ'], [⟨['i', 's'], ['μ'], none⟩]⟩, ⟨['é', 's'], ['J'], [⟨['é', 's'], ['J'], none⟩]⟩, ⟨['M', 'a', 'r', 'i'], ['M'], [⟨['M', 'a', 'r', 'i'], ['M'], none⟩]⟩, ⟨['i', 's'], ['μ'], [⟨['i', 's'], ['μ'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "j"), ("head", "mu-second")] }

def ex28_omitted : Datum :=
  { id := "mitrovicsauerland2016_ex28_omitted"
    source := ⟨"mitrovic-sauerland-2016", "(28)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati is Mari is"
    glossedTokens := [("Kati", "K"), ("is", "μ"), ("Mari", "M"), ("is", "μ")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K'], [⟨['K', 'a', 't', 'i'], ['K'], none⟩]⟩, ⟨['i', 's'], ['μ'], [⟨['i', 's'], ['μ'], none⟩]⟩, ⟨['M', 'a', 'r', 'i'], ['M'], [⟨['M', 'a', 'r', 'i'], ['M'], none⟩]⟩, ⟨['i', 's'], ['μ'], [⟨['i', 's'], ['μ'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "mu-second")] }

def fn9 : Datum :=
  { id := "mitrovicsauerland2016_fn9"
    source := ⟨"mitrovic-sauerland-2016", "fn. 9 (i)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Mari is"
    glossedTokens := [("Kati", "K"), ("és", "J"), ("Mari", "M"), ("is", "μ")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K'], [⟨['K', 'a', 't', 'i'], ['K'], none⟩]⟩, ⟨['é', 's'], ['J'], [⟨['é', 's'], ['J'], none⟩]⟩, ⟨['M', 'a', 'r', 'i'], ['M'], [⟨['M', 'a', 'r', 'i'], ['M'], none⟩]⟩, ⟨['i', 's'], ['μ'], [⟨['i', 's'], ['μ'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "j"), ("head", "mu-second")] }

def ex29 : Datum :=
  { id := "mitrovicsauerland2016_ex29"
    source := ⟨"mitrovic-sauerland-2016", "(29)"⟩
    reportedIn := none
    language := "avar1256"
    primaryText := "keto gi va ħve gi"
    glossedTokens := [("keto", "cat"), ("gi", "μ"), ("va", "J"), ("ħve", "dog"), ("gi", "μ")]
    glossedWords := [⟨['k', 'e', 't', 'o'], ['c', 'a', 't'], [⟨['k', 'e', 't', 'o'], ['c', 'a', 't'], none⟩]⟩, ⟨['g', 'i'], ['μ'], [⟨['g', 'i'], ['μ'], none⟩]⟩, ⟨['v', 'a'], ['J'], [⟨['v', 'a'], ['J'], none⟩]⟩, ⟨['ħ', 'v', 'e'], ['d', 'o', 'g'], [⟨['ħ', 'v', 'e'], ['d', 'o', 'g'], none⟩]⟩, ⟨['g', 'i'], ['μ'], [⟨['g', 'i'], ['μ'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-first"), ("head", "j"), ("head", "mu-second")] }

def ex33a : Datum :=
  { id := "mitrovicsauerland2016_ex33a"
    source := ⟨"mitrovic-sauerland-2016", "(33a)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "ad summam rem pūblicam atque ad omnium nostrum"
    glossedTokens := [("ad", "to"), ("summam", "utmost"), ("rem", "weal"), ("pūblicam", "common"), ("atque", "and"), ("ad", "to"), ("omnium", "all"), ("nostrum", "of.us")]
    glossedWords := [⟨['a', 'd'], ['t', 'o'], [⟨['a', 'd'], ['t', 'o'], none⟩]⟩, ⟨['s', 'u', 'm', 'm', 'a', 'm'], ['u', 't', 'm', 'o', 's', 't'], [⟨['s', 'u', 'm', 'm', 'a', 'm'], ['u', 't', 'm', 'o', 's', 't'], none⟩]⟩, ⟨['r', 'e', 'm'], ['w', 'e', 'a', 'l'], [⟨['r', 'e', 'm'], ['w', 'e', 'a', 'l'], none⟩]⟩, ⟨['p', 'ū', 'b', 'l', 'i', 'c', 'a', 'm'], ['c', 'o', 'm', 'm', 'o', 'n'], [⟨['p', 'ū', 'b', 'l', 'i', 'c', 'a', 'm'], ['c', 'o', 'm', 'm', 'o', 'n'], none⟩]⟩, ⟨['a', 't', 'q', 'u', 'e'], ['a', 'n', 'd'], [⟨['a', 't', 'q', 'u', 'e'], ['a', 'n', 'd'], none⟩]⟩, ⟨['a', 'd'], ['t', 'o'], [⟨['a', 'd'], ['t', 'o'], none⟩]⟩, ⟨['o', 'm', 'n', 'i', 'u', 'm'], ['a', 'l', 'l'], [⟨['o', 'm', 'n', 'i', 'u', 'm'], ['a', 'l', 'l'], none⟩]⟩, ⟨['n', 'o', 's', 't', 'r', 'u', 'm'], ['o', 'f', '.', 'u', 's'], [⟨['n', 'o', 's', 't', 'r', 'u', 'm'], ['o', 'f', '.', 'u', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "j"), ("head", "mu-second")] }

def ex33b : Datum :=
  { id := "mitrovicsauerland2016_ex33b"
    source := ⟨"mitrovic-sauerland-2016", "(33b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "vītam salūtemque"
    glossedTokens := [("vītam", "life"), ("salūtem-que", "safety-and")]
    glossedWords := [⟨['v', 'ī', 't', 'a', 'm'], ['l', 'i', 'f', 'e'], [⟨['v', 'ī', 't', 'a', 'm'], ['l', 'i', 'f', 'e'], none⟩]⟩, ⟨['s', 'a', 'l', 'ū', 't', 'e', 'm', '-', 'q', 'u', 'e'], ['s', 'a', 'f', 'e', 't', 'y', '-', 'a', 'n', 'd'], [⟨['s', 'a', 'l', 'ū', 't', 'e', 'm'], ['s', 'a', 'f', 'e', 't', 'y'], none⟩, ⟨['q', 'u', 'e'], ['a', 'n', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("head", "mu-second")] }

def all : List Datum := [ex1c, ex1c_omitted, ex23, ex24, ex25, ex26, ex27, ex28, ex28_omitted, fn9, ex29, ex33a, ex33b]

end MitrovicSauerland2016.Examples
