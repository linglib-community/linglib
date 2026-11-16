module

public import Linglib.Data.Examples.Schema

/-!
# `Cole1982` — typed example data

Auto-generated from `Linglib/Data/Examples/Cole1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cole1982.Examples`.
-/

@[expose] public section

namespace Cole1982.Examples

def ex_89b : Datum :=
  { id := "cole1982_89b"
    source := ⟨"cole-1982", "p. 30, (89b)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "ari, jatun wasi-ta chari-ni-mi"
    glossedTokens := [("ari", "yes"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-ni-mi", "have-1-validator")]
    glossedWords := [⟨[['a', 'r', 'i']], [['y', 'e', 's']]⟩, ⟨[['j', 'a', 't', 'u', 'n']], [['b', 'i', 'g']]⟩, ⟨[['w', 'a', 's', 'i'], ['t', 'a']], [['h', 'o', 'u', 's', 'e'], ['a', 'c', 'c']]⟩, ⟨[['c', 'h', 'a', 'r', 'i'], ['n', 'i'], ['m', 'i']], [['h', 'a', 'v', 'e'], ['1'], ['v', 'a', 'l', 'i', 'd', 'a', 't', 'o', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_90 : Datum :=
  { id := "cole1982_90"
    source := ⟨"cole-1982", "p. 30, (90)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "mana jatun wasi-ta chari-ni-chu"
    glossedTokens := [("mana", "not"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-ni-chu", "have-1-neg")]
    glossedWords := [⟨[['m', 'a', 'n', 'a']], [['n', 'o', 't']]⟩, ⟨[['j', 'a', 't', 'u', 'n']], [['b', 'i', 'g']]⟩, ⟨[['w', 'a', 's', 'i'], ['t', 'a']], [['h', 'o', 'u', 's', 'e'], ['a', 'c', 'c']]⟩, ⟨[['c', 'h', 'a', 'r', 'i'], ['n', 'i'], ['c', 'h', 'u']], [['h', 'a', 'v', 'e'], ['1'], ['n', 'e', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("affirmative", "cole1982_89b")] }

def ex_332 : Datum :=
  { id := "cole1982_332"
    source := ⟨"cole-1982", "p. 83, (332)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "ñuka wawki mana jatun wasi-ta chari-n-chu"
    glossedTokens := [("ñuka", "my"), ("wawki", "brother"), ("mana", "not"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-n-chu", "have-3-neg")]
    glossedWords := [⟨[['ñ', 'u', 'k', 'a']], [['m', 'y']]⟩, ⟨[['w', 'a', 'w', 'k', 'i']], [['b', 'r', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['m', 'a', 'n', 'a']], [['n', 'o', 't']]⟩, ⟨[['j', 'a', 't', 'u', 'n']], [['b', 'i', 'g']]⟩, ⟨[['w', 'a', 's', 'i'], ['t', 'a']], [['h', 'o', 'u', 's', 'e'], ['a', 'c', 'c']]⟩, ⟨[['c', 'h', 'a', 'r', 'i'], ['n'], ['c', 'h', 'u']], [['h', 'a', 'v', 'e'], ['3'], ['n', 'e', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_333 : Datum :=
  { id := "cole1982_333"
    source := ⟨"cole-1982", "p. 83, (333)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "kan-paj wawki jatun wasi-ta chari-n-chu"
    glossedTokens := [("kan-paj", "you-possessive"), ("wawki", "brother"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-n-chu", "have-3-inter")]
    glossedWords := [⟨[['k', 'a', 'n'], ['p', 'a', 'j']], [['y', 'o', 'u'], ['p', 'o', 's', 's', 'e', 's', 's', 'i', 'v', 'e']]⟩, ⟨[['w', 'a', 'w', 'k', 'i']], [['b', 'r', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[['j', 'a', 't', 'u', 'n']], [['b', 'i', 'g']]⟩, ⟨[['w', 'a', 's', 'i'], ['t', 'a']], [['h', 'o', 'u', 's', 'e'], ['a', 'c', 'c']]⟩, ⟨[['c', 'h', 'a', 'r', 'i'], ['n'], ['c', 'h', 'u']], [['h', 'a', 'v', 'e'], ['3'], ['i', 'n', 't', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_89b, ex_90, ex_332, ex_333]

end Cole1982.Examples
