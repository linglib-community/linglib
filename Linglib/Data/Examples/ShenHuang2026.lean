module

public import Linglib.Data.Examples.Schema

/-!
# `ShenHuang2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ShenHuang2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ShenHuang2026.Examples`.
-/

@[expose] public section

namespace ShenHuang2026.Examples

def ex3a : Datum :=
  { id := "shenhuang2026_ex3a"
    source := ⟨"shen-huang-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you compose a song about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("object", "indefinite"), ("creation", "yes")] }

def ex3b : Datum :=
  { id := "shenhuang2026_ex3b"
    source := ⟨"shen-huang-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you compose that song about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "fronted"), ("object", "definite"), ("creation", "yes")] }

def ex28_indefinite : Datum :=
  { id := "shenhuang2026_ex28_indefinite"
    source := ⟨"li-1992", "(54)"⟩
    reportedIn := some ⟨"shen-huang-2026", "(28)"⟩
    language := "mand1415"
    primaryText := "Wǒ yǐwéi tā ná-le shénme rén de xiàngpiàn"
    glossedTokens := [("Wǒ", "I"), ("yǐwéi", "mistakenly.believe"), ("tā", "he"), ("ná-le", "take.away-PERF"), ("shénme", "what"), ("rén", "man"), ("de", "DE"), ("xiàngpiàn", "picture")]
    glossedWords := [⟨[['W', 'ǒ']], [['I']]⟩, ⟨[['y', 'ǐ', 'w', 'é', 'i']], [['m', 'i', 's', 't', 'a', 'k', 'e', 'n', 'l', 'y', '.', 'b', 'e', 'l', 'i', 'e', 'v', 'e']]⟩, ⟨[['t', 'ā']], [['h', 'e']]⟩, ⟨[['n', 'á'], ['l', 'e']], [['t', 'a', 'k', 'e', '.', 'a', 'w', 'a', 'y'], ['P', 'E', 'R', 'F']]⟩, ⟨[['s', 'h', 'é', 'n', 'm', 'e']], [['w', 'h', 'a', 't']]⟩, ⟨[['r', 'é', 'n']], [['m', 'a', 'n']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'à', 'n', 'g', 'p', 'i', 'à', 'n']], [['p', 'i', 'c', 't', 'u', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "inSitu"), ("object", "indefinite"), ("creation", "no")] }

def ex28_definite : Datum :=
  { id := "shenhuang2026_ex28_definite"
    source := ⟨"li-1992", "(54)"⟩
    reportedIn := some ⟨"shen-huang-2026", "(28)"⟩
    language := "mand1415"
    primaryText := "Wǒ yǐwéi tā ná-le nà-zhāng shénme rén de xiàngpiàn"
    glossedTokens := [("Wǒ", "I"), ("yǐwéi", "mistakenly.believe"), ("tā", "he"), ("ná-le", "take.away-PERF"), ("nà-zhāng", "that-CL"), ("shénme", "what"), ("rén", "man"), ("de", "DE"), ("xiàngpiàn", "picture")]
    glossedWords := [⟨[['W', 'ǒ']], [['I']]⟩, ⟨[['y', 'ǐ', 'w', 'é', 'i']], [['m', 'i', 's', 't', 'a', 'k', 'e', 'n', 'l', 'y', '.', 'b', 'e', 'l', 'i', 'e', 'v', 'e']]⟩, ⟨[['t', 'ā']], [['h', 'e']]⟩, ⟨[['n', 'á'], ['l', 'e']], [['t', 'a', 'k', 'e', '.', 'a', 'w', 'a', 'y'], ['P', 'E', 'R', 'F']]⟩, ⟨[['n', 'à'], ['z', 'h', 'ā', 'n', 'g']], [['t', 'h', 'a', 't'], ['C', 'L']]⟩, ⟨[['s', 'h', 'é', 'n', 'm', 'e']], [['w', 'h', 'a', 't']]⟩, ⟨[['r', 'é', 'n']], [['m', 'a', 'n']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'i', 'à', 'n', 'g', 'p', 'i', 'à', 'n']], [['p', 'i', 'c', 't', 'u', 'r', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("wh", "inSitu"), ("object", "definite"), ("creation", "no")] }

def all : List Datum := [ex3a, ex3b, ex28_indefinite, ex28_definite]

end ShenHuang2026.Examples
