module

public import Linglib.Data.Examples.Schema

/-!
# `CoppockWechsler2018` — typed example data

Auto-generated from `Linglib/Data/Examples/CoppockWechsler2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CoppockWechsler2018.Examples`.
-/

@[expose] public section

namespace CoppockWechsler2018.Examples

def ex_27 : Datum :=
  { id := "coppockwechsler2018_27"
    source := ⟨"coppock-wechsler-2018", "(27)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "jĩ: a:pwa twan-ā"
    glossedTokens := [("jĩ:", "1.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO")]
    glossedWords := [⟨[['j', 'ĩ']], [['1', '.', 'E', 'R', 'G']]⟩, ⟨[['a', 'p', 'w', 'a']], [['m', 'u', 'c', 'h']]⟩, ⟨[['t', 'w', 'a', 'n'], ['ā']], [['d', 'r', 'i', 'n', 'k'], ['P', 'A', 'S', 'T', '.', 'E', 'G', 'O']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("clause", "declarative"), ("marking", "ego")] }

def ex_28 : Datum :=
  { id := "coppockwechsler2018_28"
    source := ⟨"coppock-wechsler-2018", "(28)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "chã a:pwa twan-ā"
    glossedTokens := [("chã", "2.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO")]
    glossedWords := [⟨[['c', 'h', 'ã']], [['2', '.', 'E', 'R', 'G']]⟩, ⟨[['a', 'p', 'w', 'a']], [['m', 'u', 'c', 'h']]⟩, ⟨[['t', 'w', 'a', 'n'], ['ā']], [['d', 'r', 'i', 'n', 'k'], ['P', 'A', 'S', 'T', '.', 'E', 'G', 'O']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("clause", "declarative"), ("marking", "ego")] }

def ex_34a : Datum :=
  { id := "coppockwechsler2018_34a"
    source := ⟨"coppock-wechsler-2018", "(34a)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "jĩ a:pwa twan-ā lā"
    glossedTokens := [("jĩ", "1.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO"), ("lā", "Q")]
    glossedWords := [⟨[['j', 'ĩ']], [['1', '.', 'E', 'R', 'G']]⟩, ⟨[['a', 'p', 'w', 'a']], [['m', 'u', 'c', 'h']]⟩, ⟨[['t', 'w', 'a', 'n'], ['ā']], [['d', 'r', 'i', 'n', 'k'], ['P', 'A', 'S', 'T', '.', 'E', 'G', 'O']]⟩, ⟨[['l', 'ā']], [['Q']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("clause", "interrogative"), ("marking", "ego")] }

def ex_34b : Datum :=
  { id := "coppockwechsler2018_34b"
    source := ⟨"coppock-wechsler-2018", "(34b)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "jĩ: a:pwa twan-a lā"
    glossedTokens := [("jĩ:", "1.ERG"), ("a:pwa", "much"), ("twan-a", "drink-PERF"), ("lā", "Q")]
    glossedWords := [⟨[['j', 'ĩ']], [['1', '.', 'E', 'R', 'G']]⟩, ⟨[['a', 'p', 'w', 'a']], [['m', 'u', 'c', 'h']]⟩, ⟨[['t', 'w', 'a', 'n'], ['a']], [['d', 'r', 'i', 'n', 'k'], ['P', 'E', 'R', 'F']]⟩, ⟨[['l', 'ā']], [['Q']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("clause", "interrogative"), ("marking", "plain")] }

def ex_35a : Datum :=
  { id := "coppockwechsler2018_35a"
    source := ⟨"coppock-wechsler-2018", "(35a)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "chã a:pwa twan-ā lā"
    glossedTokens := [("chã", "2.ERG"), ("a:pwa", "much"), ("twan-ā", "drink-PAST.EGO"), ("lā", "Q")]
    glossedWords := [⟨[['c', 'h', 'ã']], [['2', '.', 'E', 'R', 'G']]⟩, ⟨[['a', 'p', 'w', 'a']], [['m', 'u', 'c', 'h']]⟩, ⟨[['t', 'w', 'a', 'n'], ['ā']], [['d', 'r', 'i', 'n', 'k'], ['P', 'A', 'S', 'T', '.', 'E', 'G', 'O']]⟩, ⟨[['l', 'ā']], [['Q']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("clause", "interrogative"), ("marking", "ego")] }

def ex_35b : Datum :=
  { id := "coppockwechsler2018_35b"
    source := ⟨"coppock-wechsler-2018", "(35b)"⟩
    reportedIn := none
    language := "newa1246"
    primaryText := "chã a:pwa twan-a lā"
    glossedTokens := [("chã", "2.ERG"), ("a:pwa", "much"), ("twan-a", "drink-PERF"), ("lā", "Q")]
    glossedWords := [⟨[['c', 'h', 'ã']], [['2', '.', 'E', 'R', 'G']]⟩, ⟨[['a', 'p', 'w', 'a']], [['m', 'u', 'c', 'h']]⟩, ⟨[['t', 'w', 'a', 'n'], ['a']], [['d', 'r', 'i', 'n', 'k'], ['P', 'E', 'R', 'F']]⟩, ⟨[['l', 'ā']], [['Q']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("clause", "interrogative"), ("marking", "plain")] }

def all : List Datum := [ex_27, ex_28, ex_34a, ex_34b, ex_35a, ex_35b]

end CoppockWechsler2018.Examples
