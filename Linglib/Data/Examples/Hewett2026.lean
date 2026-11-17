module

public import Linglib.Data.Examples.Schema

/-!
# `Hewett2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Hewett2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hewett2026.Examples`.
-/

@[expose] public section

namespace Hewett2026.Examples

def ex1a : Datum :=
  { id := "hewett2026_ex1a"
    source := ⟨"hewett-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They apologized for/*to/*of their behavior."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "apologi"), ("category", "V"), ("prep", "for")] }

def ex1b : Datum :=
  { id := "hewett2026_ex1b"
    source := ⟨"hewett-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Their apology for/*to/*of their behavior was half-hearted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "apologi"), ("category", "N"), ("prep", "for")] }

def ex1c : Datum :=
  { id := "hewett2026_ex1c"
    source := ⟨"hewett-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are apologetic for/*to/*of their behavior."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "apologi"), ("category", "A"), ("prep", "for")] }

def ex2a : Datum :=
  { id := "hewett2026_ex2a"
    source := ⟨"hewett-2026", "(2a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "bftaxir b-/*ʕala/*min zakaːʔ-i."
    glossedTokens := [("bftaxir", "be.proud.1.SG"), ("b-/*ʕala/*min", "in-/*over/*from"), ("zakaːʔ-i", "intelligence-my")]
    glossedWords := [⟨['b', 'f', 't', 'a', 'x', 'i', 'r'], ['b', 'e', '.', 'p', 'r', 'o', 'u', 'd', '.', '1', '.', 'S', 'G'], [⟨['b', 'f', 't', 'a', 'x', 'i', 'r'], ['b', 'e', '.', 'p', 'r', 'o', 'u', 'd', '.', '1', '.', 'S', 'G'], none⟩]⟩, ⟨['b', '-', '/', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'm', 'i', 'n'], ['i', 'n', '-', '/', '*', 'o', 'v', 'e', 'r', '/', '*', 'f', 'r', 'o', 'm'], [⟨['b'], ['i', 'n'], none⟩, ⟨['/', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'm', 'i', 'n'], ['/', '*', 'o', 'v', 'e', 'r', '/', '*', 'f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['z', 'a', 'k', 'a', 'ː', 'ʔ', '-', 'i'], ['i', 'n', 't', 'e', 'l', 'l', 'i', 'g', 'e', 'n', 'c', 'e', '-', 'm', 'y'], [⟨['z', 'a', 'k', 'a', 'ː', 'ʔ'], ['i', 'n', 't', 'e', 'l', 'l', 'i', 'g', 'e', 'n', 'c', 'e'], none⟩, ⟨['i'], ['m', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "fxr"), ("category", "V"), ("prep", "b-")] }

def ex2b : Datum :=
  { id := "hewett2026_ex2b"
    source := ⟨"hewett-2026", "(2b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʕand-i faxr b-/*ʕala/*min zakaːʔ-i."
    glossedTokens := [("ʕand-i", "at-me"), ("faxr", "pride"), ("b-/*ʕala/*min", "in-/*over/*from"), ("zakaːʔ-i", "intelligence-my")]
    glossedWords := [⟨['ʕ', 'a', 'n', 'd', '-', 'i'], ['a', 't', '-', 'm', 'e'], [⟨['ʕ', 'a', 'n', 'd'], ['a', 't'], none⟩, ⟨['i'], ['m', 'e'], some '-'⟩]⟩, ⟨['f', 'a', 'x', 'r'], ['p', 'r', 'i', 'd', 'e'], [⟨['f', 'a', 'x', 'r'], ['p', 'r', 'i', 'd', 'e'], none⟩]⟩, ⟨['b', '-', '/', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'm', 'i', 'n'], ['i', 'n', '-', '/', '*', 'o', 'v', 'e', 'r', '/', '*', 'f', 'r', 'o', 'm'], [⟨['b'], ['i', 'n'], none⟩, ⟨['/', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'm', 'i', 'n'], ['/', '*', 'o', 'v', 'e', 'r', '/', '*', 'f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['z', 'a', 'k', 'a', 'ː', 'ʔ', '-', 'i'], ['i', 'n', 't', 'e', 'l', 'l', 'i', 'g', 'e', 'n', 'c', 'e', '-', 'm', 'y'], [⟨['z', 'a', 'k', 'a', 'ː', 'ʔ'], ['i', 'n', 't', 'e', 'l', 'l', 'i', 'g', 'e', 'n', 'c', 'e'], none⟩, ⟨['i'], ['m', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "fxr"), ("category", "N"), ("prep", "b-")] }

def ex2c : Datum :=
  { id := "hewett2026_ex2c"
    source := ⟨"hewett-2026", "(2c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʔana faxuːre b-/*ʕala/*min zakaːʔ-i."
    glossedTokens := [("ʔana", "I"), ("faxuːre", "proud"), ("b-/*ʕala/*min", "in-/*over/*from"), ("zakaːʔ-i", "intelligence-my")]
    glossedWords := [⟨['ʔ', 'a', 'n', 'a'], ['I'], [⟨['ʔ', 'a', 'n', 'a'], ['I'], none⟩]⟩, ⟨['f', 'a', 'x', 'u', 'ː', 'r', 'e'], ['p', 'r', 'o', 'u', 'd'], [⟨['f', 'a', 'x', 'u', 'ː', 'r', 'e'], ['p', 'r', 'o', 'u', 'd'], none⟩]⟩, ⟨['b', '-', '/', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'm', 'i', 'n'], ['i', 'n', '-', '/', '*', 'o', 'v', 'e', 'r', '/', '*', 'f', 'r', 'o', 'm'], [⟨['b'], ['i', 'n'], none⟩, ⟨['/', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'm', 'i', 'n'], ['/', '*', 'o', 'v', 'e', 'r', '/', '*', 'f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['z', 'a', 'k', 'a', 'ː', 'ʔ', '-', 'i'], ['i', 'n', 't', 'e', 'l', 'l', 'i', 'g', 'e', 'n', 'c', 'e', '-', 'm', 'y'], [⟨['z', 'a', 'k', 'a', 'ː', 'ʔ'], ['i', 'n', 't', 'e', 'l', 'l', 'i', 'g', 'e', 'n', 'c', 'e'], none⟩, ⟨['i'], ['m', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "fxr"), ("category", "A"), ("prep", "b-")] }

def ex5a : Datum :=
  { id := "hewett2026_ex5a"
    source := ⟨"hewett-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She prides herself on/*in/*of her thoroughness."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "prd"), ("category", "V"), ("prep", "on")] }

def ex5b : Datum :=
  { id := "hewett2026_ex5b"
    source := ⟨"hewett-2026", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her pride in/*on/*of her thoroughness is understandable."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "prd"), ("category", "N"), ("prep", "in")] }

def ex5c : Datum :=
  { id := "hewett2026_ex5c"
    source := ⟨"hewett-2026", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is proud of/*on/*in her thoroughness."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "prd"), ("category", "A"), ("prep", "of")] }

def ex6a : Datum :=
  { id := "hewett2026_ex6a"
    source := ⟨"hewett-2026", "(6a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "baːraku-ni b-/*ʕa(la) l-walad."
    glossedTokens := [("baːraku-ni", "congratulated.3.PL-me"), ("b-/*ʕa(la)", "in-/*over"), ("l-walad", "the-baby")]
    glossedWords := [⟨['b', 'a', 'ː', 'r', 'a', 'k', 'u', '-', 'n', 'i'], ['c', 'o', 'n', 'g', 'r', 'a', 't', 'u', 'l', 'a', 't', 'e', 'd', '.', '3', '.', 'P', 'L', '-', 'm', 'e'], [⟨['b', 'a', 'ː', 'r', 'a', 'k', 'u'], ['c', 'o', 'n', 'g', 'r', 'a', 't', 'u', 'l', 'a', 't', 'e', 'd', '.', '3', '.', 'P', 'L'], none⟩, ⟨['n', 'i'], ['m', 'e'], some '-'⟩]⟩, ⟨['b', '-', '/', '*', 'ʕ', 'a', '(', 'l', 'a', ')'], ['i', 'n', '-', '/', '*', 'o', 'v', 'e', 'r'], [⟨['b'], ['i', 'n'], none⟩, ⟨['/', '*', 'ʕ', 'a', 'l', 'a'], ['/', '*', 'o', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['l', '-', 'w', 'a', 'l', 'a', 'd'], ['t', 'h', 'e', '-', 'b', 'a', 'b', 'y'], [⟨['l'], ['t', 'h', 'e'], none⟩, ⟨['w', 'a', 'l', 'a', 'd'], ['b', 'a', 'b', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "brk"), ("category", "V"), ("prep", "b-")] }

def ex6b : Datum :=
  { id := "hewett2026_ex6b"
    source := ⟨"hewett-2026", "(6b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "baʕtu-li mbaːrake ʕa(la)/*b- l-walad."
    glossedTokens := [("baʕtu-li", "sent.3.PL-to.me"), ("mbaːrake", "congratulations"), ("ʕa(la)/*b-", "over/*in-"), ("l-walad", "the-baby")]
    glossedWords := [⟨['b', 'a', 'ʕ', 't', 'u', '-', 'l', 'i'], ['s', 'e', 'n', 't', '.', '3', '.', 'P', 'L', '-', 't', 'o', '.', 'm', 'e'], [⟨['b', 'a', 'ʕ', 't', 'u'], ['s', 'e', 'n', 't', '.', '3', '.', 'P', 'L'], none⟩, ⟨['l', 'i'], ['t', 'o', '.', 'm', 'e'], some '-'⟩]⟩, ⟨['m', 'b', 'a', 'ː', 'r', 'a', 'k', 'e'], ['c', 'o', 'n', 'g', 'r', 'a', 't', 'u', 'l', 'a', 't', 'i', 'o', 'n', 's'], [⟨['m', 'b', 'a', 'ː', 'r', 'a', 'k', 'e'], ['c', 'o', 'n', 'g', 'r', 'a', 't', 'u', 'l', 'a', 't', 'i', 'o', 'n', 's'], none⟩]⟩, ⟨['ʕ', 'a', '(', 'l', 'a', ')', '/', '*', 'b', '-'], ['o', 'v', 'e', 'r', '/', '*', 'i', 'n', '-'], [⟨['ʕ', 'a', 'l', 'a', '/', '*', 'b'], ['o', 'v', 'e', 'r', '/', '*', 'i', 'n'], none⟩]⟩, ⟨['l', '-', 'w', 'a', 'l', 'a', 'd'], ['t', 'h', 'e', '-', 'b', 'a', 'b', 'y'], [⟨['l'], ['t', 'h', 'e'], none⟩, ⟨['w', 'a', 'l', 'a', 'd'], ['b', 'a', 'b', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "brk"), ("category", "N"), ("prep", "ʕala")] }

def ex11a : Datum :=
  { id := "hewett2026_ex11a"
    source := ⟨"hewett-2026", "(11a)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "xaːf min l-ʔasad."
    glossedTokens := [("xaːf", "feared.3.M.SG"), ("min", "from"), ("l-ʔasad", "the-lion")]
    glossedWords := [⟨['x', 'a', 'ː', 'f'], ['f', 'e', 'a', 'r', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], [⟨['x', 'a', 'ː', 'f'], ['f', 'e', 'a', 'r', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['m', 'i', 'n'], ['f', 'r', 'o', 'm'], [⟨['m', 'i', 'n'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['l', '-', 'ʔ', 'a', 's', 'a', 'd'], ['t', 'h', 'e', '-', 'l', 'i', 'o', 'n'], [⟨['l'], ['t', 'h', 'e'], none⟩, ⟨['ʔ', 'a', 's', 'a', 'd'], ['l', 'i', 'o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("root", "xwf"), ("template", "XaYaZ"), ("prep", "min")] }

def ex11b : Datum :=
  { id := "hewett2026_ex11b"
    source := ⟨"hewett-2026", "(11b)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "xawwəf-u min l-ʔasad."
    glossedTokens := [("xawwəf-u", "made.afraid.3.M.SG-him"), ("min", "from"), ("l-ʔasad", "the-lion")]
    glossedWords := [⟨['x', 'a', 'w', 'w', 'ə', 'f', '-', 'u'], ['m', 'a', 'd', 'e', '.', 'a', 'f', 'r', 'a', 'i', 'd', '.', '3', '.', 'M', '.', 'S', 'G', '-', 'h', 'i', 'm'], [⟨['x', 'a', 'w', 'w', 'ə', 'f'], ['m', 'a', 'd', 'e', '.', 'a', 'f', 'r', 'a', 'i', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], none⟩, ⟨['u'], ['h', 'i', 'm'], some '-'⟩]⟩, ⟨['m', 'i', 'n'], ['f', 'r', 'o', 'm'], [⟨['m', 'i', 'n'], ['f', 'r', 'o', 'm'], none⟩]⟩, ⟨['l', '-', 'ʔ', 'a', 's', 'a', 'd'], ['t', 'h', 'e', '-', 'l', 'i', 'o', 'n'], [⟨['l'], ['t', 'h', 'e'], none⟩, ⟨['ʔ', 'a', 's', 'a', 'd'], ['l', 'i', 'o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2"), ("root", "xwf"), ("template", "XaYYaZ"), ("prep", "min")] }

def ex13ai : Datum :=
  { id := "hewett2026_ex13ai"
    source := ⟨"hewett-2026", "(13a.i)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "kraht (*fi) Sami."
    glossedTokens := [("kraht", "hate.1.SG"), ("(*fi)", "(*in)"), ("Sami", "Sami")]
    glossedWords := [⟨['k', 'r', 'a', 'h', 't'], ['h', 'a', 't', 'e', '.', '1', '.', 'S', 'G'], [⟨['k', 'r', 'a', 'h', 't'], ['h', 'a', 't', 'e', '.', '1', '.', 'S', 'G'], none⟩]⟩, ⟨['(', '*', 'f', 'i', ')'], ['(', '*', 'i', 'n', ')'], [⟨['*', 'f', 'i'], ['(', '*', 'i', 'n', ')'], none⟩]⟩, ⟨['S', 'a', 'm', 'i'], ['S', 'a', 'm', 'i'], [⟨['S', 'a', 'm', 'i'], ['S', 'a', 'm', 'i'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "krh"), ("template", "XaYaZ"), ("prep", "none")] }

def ex13aii : Datum :=
  { id := "hewett2026_ex13aii"
    source := ⟨"hewett-2026", "(13a.ii)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "karraht-ha *(fi) Sami."
    glossedTokens := [("karraht-ha", "made.hate.1.SG-her"), ("*(fi)", "*(in)"), ("Sami", "Sami")]
    glossedWords := [⟨['k', 'a', 'r', 'r', 'a', 'h', 't', '-', 'h', 'a'], ['m', 'a', 'd', 'e', '.', 'h', 'a', 't', 'e', '.', '1', '.', 'S', 'G', '-', 'h', 'e', 'r'], [⟨['k', 'a', 'r', 'r', 'a', 'h', 't'], ['m', 'a', 'd', 'e', '.', 'h', 'a', 't', 'e', '.', '1', '.', 'S', 'G'], none⟩, ⟨['h', 'a'], ['h', 'e', 'r'], some '-'⟩]⟩, ⟨['*', '(', 'f', 'i', ')'], ['*', '(', 'i', 'n', ')'], [⟨['*', 'f', 'i'], ['*', '(', 'i', 'n', ')'], none⟩]⟩, ⟨['S', 'a', 'm', 'i'], ['S', 'a', 'm', 'i'], [⟨['S', 'a', 'm', 'i'], ['S', 'a', 'm', 'i'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "krh"), ("template", "XaYYaZ"), ("prep", "fi")] }

def ex13bi : Datum :=
  { id := "hewett2026_ex13bi"
    source := ⟨"hewett-2026", "(13b.i)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "l-ħnaʃ daːr biː-/*ʕliː-k."
    glossedTokens := [("l-ħnaʃ", "the-snake"), ("daːr", "encircled.3.M.SG"), ("biː-/*ʕliː-k", "in-/*over-you")]
    glossedWords := [⟨['l', '-', 'ħ', 'n', 'a', 'ʃ'], ['t', 'h', 'e', '-', 's', 'n', 'a', 'k', 'e'], [⟨['l'], ['t', 'h', 'e'], none⟩, ⟨['ħ', 'n', 'a', 'ʃ'], ['s', 'n', 'a', 'k', 'e'], some '-'⟩]⟩, ⟨['d', 'a', 'ː', 'r'], ['e', 'n', 'c', 'i', 'r', 'c', 'l', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], [⟨['d', 'a', 'ː', 'r'], ['e', 'n', 'c', 'i', 'r', 'c', 'l', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['b', 'i', 'ː', '-', '/', '*', 'ʕ', 'l', 'i', 'ː', '-', 'k'], ['i', 'n', '-', '/', '*', 'o', 'v', 'e', 'r', '-', 'y', 'o', 'u'], [⟨['b', 'i', 'ː'], ['i', 'n'], none⟩, ⟨['/', '*', 'ʕ', 'l', 'i', 'ː'], ['/', '*', 'o', 'v', 'e', 'r'], some '-'⟩, ⟨['k'], ['y', 'o', 'u'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "XaYaZ"), ("prep", "bi-")] }

def ex13bii : Datum :=
  { id := "hewett2026_ex13bii"
    source := ⟨"hewett-2026", "(13b.ii)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "dawwart l-ħnaʃ ʕliː-/*biː-k."
    glossedTokens := [("dawwart", "encircled.1.SG"), ("l-ħnaʃ", "the-snake"), ("ʕliː-/*biː-k", "over-/*in-you")]
    glossedWords := [⟨['d', 'a', 'w', 'w', 'a', 'r', 't'], ['e', 'n', 'c', 'i', 'r', 'c', 'l', 'e', 'd', '.', '1', '.', 'S', 'G'], [⟨['d', 'a', 'w', 'w', 'a', 'r', 't'], ['e', 'n', 'c', 'i', 'r', 'c', 'l', 'e', 'd', '.', '1', '.', 'S', 'G'], none⟩]⟩, ⟨['l', '-', 'ħ', 'n', 'a', 'ʃ'], ['t', 'h', 'e', '-', 's', 'n', 'a', 'k', 'e'], [⟨['l'], ['t', 'h', 'e'], none⟩, ⟨['ħ', 'n', 'a', 'ʃ'], ['s', 'n', 'a', 'k', 'e'], some '-'⟩]⟩, ⟨['ʕ', 'l', 'i', 'ː', '-', '/', '*', 'b', 'i', 'ː', '-', 'k'], ['o', 'v', 'e', 'r', '-', '/', '*', 'i', 'n', '-', 'y', 'o', 'u'], [⟨['ʕ', 'l', 'i', 'ː'], ['o', 'v', 'e', 'r'], none⟩, ⟨['/', '*', 'b', 'i', 'ː'], ['/', '*', 'i', 'n'], some '-'⟩, ⟨['k'], ['y', 'o', 'u'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "XaYYaZ"), ("prep", "ʕla")] }

def ex14a : Datum :=
  { id := "hewett2026_ex14a"
    source := ⟨"hewett-2026", "(14a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ħakam ʕalej-o b-s-siʤn."
    glossedTokens := [("ħakam", "sentenced.3.M.SG"), ("ʕalej-o", "over-him"), ("b-s-siʤn", "in-the-jail")]
    glossedWords := [⟨['ħ', 'a', 'k', 'a', 'm'], ['s', 'e', 'n', 't', 'e', 'n', 'c', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], [⟨['ħ', 'a', 'k', 'a', 'm'], ['s', 'e', 'n', 't', 'e', 'n', 'c', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['ʕ', 'a', 'l', 'e', 'j', '-', 'o'], ['o', 'v', 'e', 'r', '-', 'h', 'i', 'm'], [⟨['ʕ', 'a', 'l', 'e', 'j'], ['o', 'v', 'e', 'r'], none⟩, ⟨['o'], ['h', 'i', 'm'], some '-'⟩]⟩, ⟨['b', '-', 's', '-', 's', 'i', 'ʤ', 'n'], ['i', 'n', '-', 't', 'h', 'e', '-', 'j', 'a', 'i', 'l'], [⟨['b'], ['i', 'n'], none⟩, ⟨['s'], ['t', 'h', 'e'], some '-'⟩, ⟨['s', 'i', 'ʤ', 'n'], ['j', 'a', 'i', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "XaYaZ"), ("prep", "ʕala")] }

def ex14b : Datum :=
  { id := "hewett2026_ex14b"
    source := ⟨"hewett-2026", "(14b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ħakkam (*ʕala/*b-) (l-mubaːreː)."
    glossedTokens := [("ħakkam", "refereed.3.M.SG"), ("(*ʕala/*b-)", "(*over/*in-)"), ("(l-mubaːreː)", "(the-match)")]
    glossedWords := [⟨['ħ', 'a', 'k', 'k', 'a', 'm'], ['r', 'e', 'f', 'e', 'r', 'e', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], [⟨['ħ', 'a', 'k', 'k', 'a', 'm'], ['r', 'e', 'f', 'e', 'r', 'e', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['(', '*', 'ʕ', 'a', 'l', 'a', '/', '*', 'b', '-', ')'], ['(', '*', 'o', 'v', 'e', 'r', '/', '*', 'i', 'n', '-', ')'], []⟩, ⟨['(', 'l', '-', 'm', 'u', 'b', 'a', 'ː', 'r', 'e', 'ː', ')'], ['(', 't', 'h', 'e', '-', 'm', 'a', 't', 'c', 'h', ')'], [⟨['l'], ['(', 't', 'h', 'e'], none⟩, ⟨['m', 'u', 'b', 'a', 'ː', 'r', 'e', 'ː'], ['m', 'a', 't', 'c', 'h', ')'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "XaYYaZ"), ("prep", "none")] }

def ex15a_active : Datum :=
  { id := "hewett2026_ex15a_active"
    source := ⟨"hewett-2026", "(15a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "wasaʔ b- NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "wsʔ"), ("template", "XaYaZ"), ("prep", "b-")] }

def ex15a_nonactive : Datum :=
  { id := "hewett2026_ex15a_nonactive"
    source := ⟨"hewett-2026", "(15a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "nwasaʔ b- NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "wsʔ"), ("template", "nXaYaZ"), ("prep", "b-")] }

def ex15b_active : Datum :=
  { id := "hewett2026_ex15b_active"
    source := ⟨"hewett-2026", "(15b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʤaðab NP1 la-/ʕala NP2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʤðb"), ("template", "XaYaZ"), ("prep", "la-/ʕala")] }

def ex15b_nonactive : Datum :=
  { id := "hewett2026_ex15b_nonactive"
    source := ⟨"hewett-2026", "(15b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "nʤaðab la-/??ʕala NP2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʤðb"), ("template", "nXaYaZ"), ("prep", "la-")] }

def ex15c_active : Datum :=
  { id := "hewett2026_ex15c_active"
    source := ⟨"hewett-2026", "(15c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʃaka NP1 la- NP2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃkw"), ("template", "XaYaZ"), ("prep", "la-")] }

def ex15c_nonactive : Datum :=
  { id := "hewett2026_ex15c_nonactive"
    source := ⟨"hewett-2026", "(15c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "nʃaka ʕala NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃkw"), ("template", "nXaYaZ"), ("prep", "ʕala")] }

def ex16a_active : Datum :=
  { id := "hewett2026_ex16a_active"
    source := ⟨"hewett-2026", "(16a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "dawwar ʕala NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "XaYYaZ"), ("prep", "ʕala")] }

def ex16a_nonactive : Datum :=
  { id := "hewett2026_ex16a_nonactive"
    source := ⟨"hewett-2026", "(16a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ddawwar ʕala NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "tXaYYaZ"), ("prep", "ʕala")] }

def ex16b_active : Datum :=
  { id := "hewett2026_ex16b_active"
    source := ⟨"hewett-2026", "(16b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʃawwaʔ NP2 ʕala/*la- NP1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃwq"), ("template", "XaYYaZ"), ("prep", "ʕala")] }

def ex16b_nonactive : Datum :=
  { id := "hewett2026_ex16b_nonactive"
    source := ⟨"hewett-2026", "(16b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "tʃawwaʔ ʕala/la- NP1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃwq"), ("template", "tXaYYaZ"), ("prep", "ʕala/la-")] }

def ex16c_active : Datum :=
  { id := "hewett2026_ex16c_active"
    source := ⟨"hewett-2026", "(16c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ħakkam"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "XaYYaZ"), ("prep", "none")] }

def ex16c_nonactive : Datum :=
  { id := "hewett2026_ex16c_nonactive"
    source := ⟨"hewett-2026", "(16c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "tħakkam b- NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "tXaYYaZ"), ("prep", "b-")] }

def ex17a : Datum :=
  { id := "hewett2026_ex17a"
    source := ⟨"hewett-2026", "(17a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ṭipel be- NP1"
    glossedTokens := [("ṭipel", "treated"), ("be-", "in-"), ("NP1", "NP1")]
    glossedWords := [⟨['ṭ', 'i', 'p', 'e', 'l'], ['t', 'r', 'e', 'a', 't', 'e', 'd'], [⟨['ṭ', 'i', 'p', 'e', 'l'], ['t', 'r', 'e', 'a', 't', 'e', 'd'], none⟩]⟩, ⟨['b', 'e', '-'], ['i', 'n', '-'], [⟨['b', 'e'], ['i', 'n'], none⟩]⟩, ⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ṭpl"), ("template", "XiYeZ"), ("prep", "be-")] }

def ex17b : Datum :=
  { id := "hewett2026_ex17b"
    source := ⟨"hewett-2026", "(17b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "NP1 ṭupal (al jedej NP2)"
    glossedTokens := [("NP1", "NP1"), ("ṭupal", "was.treated"), ("(al jedej NP2)", "(by NP2)")]
    glossedWords := [⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩, ⟨['ṭ', 'u', 'p', 'a', 'l'], ['w', 'a', 's', '.', 't', 'r', 'e', 'a', 't', 'e', 'd'], [⟨['ṭ', 'u', 'p', 'a', 'l'], ['w', 'a', 's', '.', 't', 'r', 'e', 'a', 't', 'e', 'd'], none⟩]⟩, ⟨['(', 'a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2', ')'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], [⟨['a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ṭpl"), ("template", "XuYaZ"), ("prep", "none")] }

def ex18a : Datum :=
  { id := "hewett2026_ex18a"
    source := ⟨"hewett-2026", "(18a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hišpia al NP1"
    glossedTokens := [("hišpia", "influenced"), ("al", "over"), ("NP1", "NP1")]
    glossedWords := [⟨['h', 'i', 'š', 'p', 'i', 'a'], ['i', 'n', 'f', 'l', 'u', 'e', 'n', 'c', 'e', 'd'], [⟨['h', 'i', 'š', 'p', 'i', 'a'], ['i', 'n', 'f', 'l', 'u', 'e', 'n', 'c', 'e', 'd'], none⟩]⟩, ⟨['a', 'l'], ['o', 'v', 'e', 'r'], [⟨['a', 'l'], ['o', 'v', 'e', 'r'], none⟩]⟩, ⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "špʕ"), ("template", "hiXYiZ"), ("prep", "al")] }

def ex18b : Datum :=
  { id := "hewett2026_ex18b"
    source := ⟨"hewett-2026", "(18b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "NP1 hušpa (al jedej NP2)"
    glossedTokens := [("NP1", "NP1"), ("hušpa", "was.influenced"), ("(al jedej NP2)", "(by NP2)")]
    glossedWords := [⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩, ⟨['h', 'u', 'š', 'p', 'a'], ['w', 'a', 's', '.', 'i', 'n', 'f', 'l', 'u', 'e', 'n', 'c', 'e', 'd'], [⟨['h', 'u', 'š', 'p', 'a'], ['w', 'a', 's', '.', 'i', 'n', 'f', 'l', 'u', 'e', 'n', 'c', 'e', 'd'], none⟩]⟩, ⟨['(', 'a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2', ')'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], [⟨['a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "špʕ"), ("template", "huXYaZ"), ("prep", "none")] }

def ex19a : Datum :=
  { id := "hewett2026_ex19a"
    source := ⟨"hewett-2026", "(19a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "serev le- NP1"
    glossedTokens := [("serev", "rejected"), ("le-", "to-"), ("NP1", "NP1")]
    glossedWords := [⟨['s', 'e', 'r', 'e', 'v'], ['r', 'e', 'j', 'e', 'c', 't', 'e', 'd'], [⟨['s', 'e', 'r', 'e', 'v'], ['r', 'e', 'j', 'e', 'c', 't', 'e', 'd'], none⟩]⟩, ⟨['l', 'e', '-'], ['t', 'o', '-'], [⟨['l', 'e'], ['t', 'o'], none⟩]⟩, ⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "srb"), ("template", "XiYeZ"), ("prep", "le-")] }

def ex19b : Datum :=
  { id := "hewett2026_ex19b"
    source := ⟨"hewett-2026", "(19b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "NP1 surav (al jedej NP2)"
    glossedTokens := [("NP1", "NP1"), ("surav", "was.rejected"), ("(al jedej NP2)", "(by NP2)")]
    glossedWords := [⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩, ⟨['s', 'u', 'r', 'a', 'v'], ['w', 'a', 's', '.', 'r', 'e', 'j', 'e', 'c', 't', 'e', 'd'], [⟨['s', 'u', 'r', 'a', 'v'], ['w', 'a', 's', '.', 'r', 'e', 'j', 'e', 'c', 't', 'e', 'd'], none⟩]⟩, ⟨['(', 'a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2', ')'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], [⟨['a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "srb"), ("template", "XuYaZ")] }

def ex20a : Datum :=
  { id := "hewett2026_ex20a"
    source := ⟨"hewett-2026", "(20a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hirbic le- NP1"
    glossedTokens := [("hirbic", "hit"), ("le-", "to-"), ("NP1", "NP1")]
    glossedWords := [⟨['h', 'i', 'r', 'b', 'i', 'c'], ['h', 'i', 't'], [⟨['h', 'i', 'r', 'b', 'i', 'c'], ['h', 'i', 't'], none⟩]⟩, ⟨['l', 'e', '-'], ['t', 'o', '-'], [⟨['l', 'e'], ['t', 'o'], none⟩]⟩, ⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "rbc"), ("template", "hiXYiZ"), ("prep", "le-")] }

def ex20b : Datum :=
  { id := "hewett2026_ex20b"
    source := ⟨"hewett-2026", "(20b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "NP1 hurbac (al jedej NP2)"
    glossedTokens := [("NP1", "NP1"), ("hurbac", "was.hit"), ("(al jedej NP2)", "(by NP2)")]
    glossedWords := [⟨['N', 'P', '1'], ['N', 'P', '1'], [⟨['N', 'P', '1'], ['N', 'P', '1'], none⟩]⟩, ⟨['h', 'u', 'r', 'b', 'a', 'c'], ['w', 'a', 's', '.', 'h', 'i', 't'], [⟨['h', 'u', 'r', 'b', 'a', 'c'], ['w', 'a', 's', '.', 'h', 'i', 't'], none⟩]⟩, ⟨['(', 'a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2', ')'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], [⟨['a', 'l', ' ', 'j', 'e', 'd', 'e', 'j', ' ', 'N', 'P', '2'], ['(', 'b', 'y', ' ', 'N', 'P', '2', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "rbc"), ("template", "huXYaZ")] }

def ex21a : Datum :=
  { id := "hewett2026_ex21a"
    source := ⟨"hewett-2026", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor can be operated on by experienced doctors."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "oper"), ("construction", "pseudopassive")] }

def ex21b : Datum :=
  { id := "hewett2026_ex21b"
    source := ⟨"hewett-2026", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor is operable (*on) (*by experienced doctors)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "oper"), ("construction", "-able")] }

def ex21c : Datum :=
  { id := "hewett2026_ex21c"
    source := ⟨"hewett-2026", "(21c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor operates on easily/quickly (by experienced doctors)."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "oper"), ("construction", "middle")] }

def ex22a : Datum :=
  { id := "hewett2026_ex22a"
    source := ⟨"hewett-2026", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor can be treated by experienced doctors."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "treat"), ("construction", "passive")] }

def ex22b : Datum :=
  { id := "hewett2026_ex22b"
    source := ⟨"hewett-2026", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor is treatable by experienced doctors."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "treat"), ("construction", "-able")] }

def ex22c : Datum :=
  { id := "hewett2026_ex22c"
    source := ⟨"hewett-2026", "(22c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor treats easily/quickly (*by experienced doctors)."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "treat"), ("construction", "middle")] }

def all : List Datum := [ex1a, ex1b, ex1c, ex2a, ex2b, ex2c, ex5a, ex5b, ex5c, ex6a, ex6b, ex11a, ex11b, ex13ai, ex13aii, ex13bi, ex13bii, ex14a, ex14b, ex15a_active, ex15a_nonactive, ex15b_active, ex15b_nonactive, ex15c_active, ex15c_nonactive, ex16a_active, ex16a_nonactive, ex16b_active, ex16b_nonactive, ex16c_active, ex16c_nonactive, ex17a, ex17b, ex18a, ex18b, ex19a, ex19b, ex20a, ex20b, ex21a, ex21b, ex21c, ex22a, ex22b, ex22c]

end Hewett2026.Examples
