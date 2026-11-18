module

public import Linglib.Data.Examples.Schema

/-!
# `HaslingerEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HaslingerEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HaslingerEtAl2025.Examples`.
-/

@[expose] public section

namespace HaslingerEtAl2025.Examples

def ex1 : Datum :=
  { id := "haslingeretal2025_ex1"
    source := ⟨"haslinger-etal-2025", "(1)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder Hund hat gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Jeder", "each"), ("Hund", "dog"), ("hat", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['J', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], [⟨['J', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['H', 'u', 'n', 'd'], ['d', 'o', 'g'], [⟨['H', 'u', 'n', 'd'], ['d', 'o', 'g'], none⟩]⟩, ⟨['h', 'a', 't'], ['A', 'U', 'X'], [⟨['h', 'a', 't'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], [⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "jederDP"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex2 : Datum :=
  { id := "haslingeretal2025_ex2"
    source := ⟨"haslinger-etal-2025", "(2)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade jeder insgesamt drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("jeder", "each"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], [⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], [⟨['j', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], [⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "jederDistance"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex4a : Datum :=
  { id := "haslingeretal2025_ex4a"
    source := ⟨"haslinger-etal-2025", "(4a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Alle Hunde haben gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Alle", "all"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['A', 'l', 'l', 'e'], ['a', 'l', 'l'], [⟨['A', 'l', 'l', 'e'], ['a', 'l', 'l'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], [⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], [⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "alle"), ("trueIn3a", "yes"), ("trueIn3b", "yes"), ("trueIn3c", "no")] }

def ex4b : Datum :=
  { id := "haslingeretal2025_ex4b"
    source := ⟨"haslinger-etal-2025", "(4b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Drei Hunde haben gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Drei", "three"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['D', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['D', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], [⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], [⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "numeralIndefinite"), ("trueIn3a", "yes"), ("trueIn3b", "yes"), ("trueIn3c", "no")] }

def ex4c : Datum :=
  { id := "haslingeretal2025_ex4c"
    source := ⟨"haslinger-etal-2025", "(4c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade insgesamt drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("insgesamt", "in.total"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], [⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], [⟨['i', 'n', 's', 'g', 'e', 's', 'a', 'm', 't'], ['i', 'n', '.', 't', 'o', 't', 'a', 'l'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("item", "definitePlural"), ("trueIn3a", "yes"), ("trueIn3b", "yes"), ("trueIn3c", "yes")] }

def ex22a : Datum :=
  { id := "haslingeretal2025_ex22a"
    source := ⟨"haslinger-etal-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade jeweils drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("jeweils", "each"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], [⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['e', 'a', 'c', 'h'], [⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jeweils"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex22b : Datum :=
  { id := "haslingeretal2025_ex22b"
    source := ⟨"haslinger-etal-2025", "(22b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder Hund hat gerade drei Würste gegessen."
    glossedTokens := [("Jeder", "each"), ("Hund", "dog"), ("hat", "AUX"), ("gerade", "just"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['J', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], [⟨['J', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['H', 'u', 'n', 'd'], ['d', 'o', 'g'], [⟨['H', 'u', 'n', 'd'], ['d', 'o', 'g'], none⟩]⟩, ⟨['h', 'a', 't'], ['A', 'U', 'X'], [⟨['h', 'a', 't'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDP"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex22c : Datum :=
  { id := "haslingeretal2025_ex22c"
    source := ⟨"haslinger-etal-2025", "(22c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Hunde haben gerade jeder drei Würste gegessen."
    glossedTokens := [("Die", "the"), ("Hunde", "dogs"), ("haben", "AUX"), ("gerade", "just"), ("jeder", "each"), ("drei", "three"), ("Würste", "sausages"), ("gegessen.", "eaten")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], [⟨['h', 'a', 'b', 'e', 'n'], ['A', 'U', 'X'], none⟩]⟩, ⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], [⟨['g', 'e', 'r', 'a', 'd', 'e'], ['j', 'u', 's', 't'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], [⟨['j', 'e', 'd', 'e', 'r'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], [⟨['d', 'r', 'e', 'i'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], [⟨['W', 'ü', 'r', 's', 't', 'e'], ['s', 'a', 'u', 's', 'a', 'g', 'e', 's'], none⟩]⟩, ⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n', '.'], ['e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 'g', 'e', 's', 's', 'e', 'n'], ['e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Three dogs: Abe, Bert, Carl. (3a) Abe ate three sausages, Bert ate three sausages, Carl ate three sausages. (3b) Abe ate one sausage, Bert ate one sausage, Carl ate one sausage. (3c) Abe ate three sausages, Bert ate three sausages, Carl didn't eat any sausages."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDistance"), ("trueIn3a", "yes"), ("trueIn3b", "no"), ("trueIn3c", "no")] }

def ex23b : Datum :=
  { id := "haslingeretal2025_ex23b"
    source := ⟨"haslinger-etal-2025", "(23b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "In den Boxen sind jeweils zwei Magnete!"
    glossedTokens := [("In", "in"), ("den", "the"), ("Boxen", "boxes"), ("sind", "are"), ("jeweils", "each"), ("zwei", "two"), ("Magnete!", "magnets")]
    glossedWords := [⟨['I', 'n'], ['i', 'n'], [⟨['I', 'n'], ['i', 'n'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e'], [⟨['d', 'e', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['B', 'o', 'x', 'e', 'n'], ['b', 'o', 'x', 'e', 's'], [⟨['B', 'o', 'x', 'e', 'n'], ['b', 'o', 'x', 'e', 's'], none⟩]⟩, ⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], [⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], none⟩]⟩, ⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['e', 'a', 'c', 'h'], [⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], [⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], none⟩]⟩, ⟨['M', 'a', 'g', 'n', 'e', 't', 'e', '!'], ['m', 'a', 'g', 'n', 'e', 't', 's'], [⟨['M', 'a', 'g', 'n', 'e', 't', 'e'], ['m', 'a', 'g', 'n', 'e', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Anna distributed 9 strong magnets, which should not be stored together, in 5 boxes. Four boxes contain two magnets, the fifth contains one. On the way home, Anna's co-driver reads the instructions to her. They say: ‘Each magnet absolutely needs to be stored separately, even just two magnets in the same box can trigger a horrible explosion.’ Anna exclaims: Oh no, we have to turn around ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jeweils"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex23c : Datum :=
  { id := "haslingeretal2025_ex23c"
    source := ⟨"haslinger-etal-2025", "(23c)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "In jeder Box sind zwei Magnete!"
    glossedTokens := [("In", "in"), ("jeder", "every"), ("Box", "box"), ("sind", "are"), ("zwei", "two"), ("Magnete!", "magnets")]
    glossedWords := [⟨['I', 'n'], ['i', 'n'], [⟨['I', 'n'], ['i', 'n'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['B', 'o', 'x'], ['b', 'o', 'x'], [⟨['B', 'o', 'x'], ['b', 'o', 'x'], none⟩]⟩, ⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], [⟨['s', 'i', 'n', 'd'], ['a', 'r', 'e'], none⟩]⟩, ⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], [⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], none⟩]⟩, ⟨['M', 'a', 'g', 'n', 'e', 't', 'e', '!'], ['m', 'a', 'g', 'n', 'e', 't', 's'], [⟨['M', 'a', 'g', 'n', 'e', 't', 'e'], ['m', 'a', 'g', 'n', 'e', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Anna distributed 9 strong magnets, which should not be stored together, in 5 boxes. Four boxes contain two magnets, the fifth contains one. On the way home, Anna's co-driver reads the instructions to her. They say: ‘Each magnet absolutely needs to be stored separately, even just two magnets in the same box can trigger a horrible explosion.’ Anna exclaims: Oh no, we have to turn around ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDP"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex24b : Datum :=
  { id := "haslingeretal2025_ex24b"
    source := ⟨"haslinger-etal-2025", "(24b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "Die Freiwilligen haben jeweils zwei Hunde an der Leine!"
    glossedTokens := [("Die", "the"), ("Freiwilligen", "volunteers"), ("haben", "have"), ("jeweils", "each"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e', 'n'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r', 's'], [⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e', 'n'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['e', 'a', 'c', 'h'], [⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['e', 'a', 'c', 'h'], none⟩]⟩, ⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], [⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['a', 'n'], ['o', 'n'], [⟨['a', 'n'], ['o', 'n'], none⟩]⟩, ⟨['d', 'e', 'r'], ['t', 'h', 'e'], [⟨['d', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['L', 'e', 'i', 'n', 'e', '!'], ['l', 'e', 'a', 's', 'h'], [⟨['L', 'e', 'i', 'n', 'e'], ['l', 'e', 'a', 's', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jeweils"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex24c : Datum :=
  { id := "haslingeretal2025_ex24c"
    source := ⟨"haslinger-etal-2025", "(24c)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "Die Freiwilligen haben jeder zwei Hunde an der Leine!"
    glossedTokens := [("Die", "the"), ("Freiwilligen", "volunteers"), ("haben", "have"), ("jeder", "every"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    glossedWords := [⟨['D', 'i', 'e'], ['t', 'h', 'e'], [⟨['D', 'i', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e', 'n'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r', 's'], [⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e', 'n'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], [⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['a', 'n'], ['o', 'n'], [⟨['a', 'n'], ['o', 'n'], none⟩]⟩, ⟨['d', 'e', 'r'], ['t', 'h', 'e'], [⟨['d', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['L', 'e', 'i', 'n', 'e', '!'], ['l', 'e', 'a', 's', 'h'], [⟨['L', 'e', 'i', 'n', 'e'], ['l', 'e', 'a', 's', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDistance"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex24d : Datum :=
  { id := "haslingeretal2025_ex24d"
    source := ⟨"haslinger-etal-2025", "(24d)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1295"
    primaryText := "Jeder Freiwillige hat zwei Hunde an der Leine!"
    glossedTokens := [("Jeder", "every"), ("Freiwillige", "volunteer"), ("hat", "has"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    glossedWords := [⟨['J', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['J', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r'], [⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], [⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['a', 'n'], ['o', 'n'], [⟨['a', 'n'], ['o', 'n'], none⟩]⟩, ⟨['d', 'e', 'r'], ['t', 'h', 'e'], [⟨['d', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['L', 'e', 'i', 'n', 'e', '!'], ['l', 'e', 'a', 's', 'h'], [⟨['L', 'e', 'i', 'n', 'e'], ['l', 'e', 'a', 's', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("item", "jederDP"), ("scenario", "nonMaximal"), ("questionnaire", "yes")] }

def ex26 : Datum :=
  { id := "haslingeretal2025_ex26"
    source := ⟨"haslinger-etal-2025", "(26)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Fünf Freiwillige haben (jeweils) zwei Hunde an der Leine!"
    glossedTokens := [("Fünf", "five"), ("Freiwillige", "volunteers"), ("haben", "have"), ("(jeweils)", "(each)"), ("zwei", "two"), ("Hunde", "dogs"), ("an", "on"), ("der", "the"), ("Leine!", "leash")]
    glossedWords := [⟨['F', 'ü', 'n', 'f'], ['f', 'i', 'v', 'e'], [⟨['F', 'ü', 'n', 'f'], ['f', 'i', 'v', 'e'], none⟩]⟩, ⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r', 's'], [⟨['F', 'r', 'e', 'i', 'w', 'i', 'l', 'l', 'i', 'g', 'e'], ['v', 'o', 'l', 'u', 'n', 't', 'e', 'e', 'r', 's'], none⟩]⟩, ⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', 'e', 'n'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['(', 'j', 'e', 'w', 'e', 'i', 'l', 's', ')'], ['(', 'e', 'a', 'c', 'h', ')'], [⟨['j', 'e', 'w', 'e', 'i', 'l', 's'], ['(', 'e', 'a', 'c', 'h', ')'], none⟩]⟩, ⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], [⟨['z', 'w', 'e', 'i'], ['t', 'w', 'o'], none⟩]⟩, ⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], [⟨['H', 'u', 'n', 'd', 'e'], ['d', 'o', 'g', 's'], none⟩]⟩, ⟨['a', 'n'], ['o', 'n'], [⟨['a', 'n'], ['o', 'n'], none⟩]⟩, ⟨['d', 'e', 'r'], ['t', 'h', 'e'], [⟨['d', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['L', 'e', 'i', 'n', 'e', '!'], ['l', 'e', 'a', 's', 'h'], [⟨['L', 'e', 'i', 'n', 'e'], ['l', 'e', 'a', 's', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "At the animal shelter, there is a section for attack dogs with 9 dogs. Today, 5 volunteers showed up to walk the dogs. Billie gives the first four volunteers two dogs each; the fifth gets just one dog. Afterwards, Billie learns that one should under no circumstances let someone walk more than one of the dogs, because the dogs will have terrible fights. Billie: Good heavens ..."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("item", "numeralIndefinite"), ("scenario", "nonMaximal")] }

def all : List Datum := [ex1, ex2, ex4a, ex4b, ex4c, ex22a, ex22b, ex22c, ex23b, ex23c, ex24b, ex24c, ex24d, ex26]

end HaslingerEtAl2025.Examples
