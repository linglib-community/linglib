module

public import Linglib.Data.Examples.Schema

/-!
# `Snyder2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Snyder2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Snyder2026.Examples`.
-/

@[expose] public section

namespace Snyder2026.Examples

def ex_1a : Datum :=
  { id := "snyder2026_1a"
    source := ⟨"snyder-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mars's moons are two (in number)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "predicative")] }

def ex_1b : Datum :=
  { id := "snyder2026_1b"
    source := ⟨"snyder-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Those are (Mars's) two moons."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "attributive")] }

def ex_1c : Datum :=
  { id := "snyder2026_1c"
    source := ⟨"snyder-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mars has two moons."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "quantificational")] }

def ex_1d : Datum :=
  { id := "snyder2026_1d"
    source := ⟨"snyder-2026", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The number of Mars's moons is two."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "specificational")] }

def ex_1e : Datum :=
  { id := "snyder2026_1e"
    source := ⟨"snyder-2026", "(1e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two is an even number."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "numeral")] }

def ex_1f : Datum :=
  { id := "snyder2026_1f"
    source := ⟨"snyder-2026", "(1f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The number two is even."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "closeAppositive")] }

def ex_4a : Datum :=
  { id := "snyder2026_4a"
    source := ⟨"snyder-2026", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each (kind of) two belongs to a different number system."
    glossedTokens := []
    context := "On the board four number systems, the natural numbers, the integers, the rationals and the reals, are illustrated with examples of numbers belonging to them."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "taxonomic")] }

def ex_4b : Datum :=
  { id := "snyder2026_4b"
    source := ⟨"snyder-2026", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two comes in several varieties: the natural number two, the rational number two, etc."
    glossedTokens := []
    context := "On the board four number systems, the natural numbers, the integers, the rationals and the reals, are illustrated with examples of numbers belonging to them."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "kindRef")] }

def ex_20a : Datum :=
  { id := "snyder2026_20a"
    source := ⟨"snyder-2026", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The von Neumann ordinal two is two-membered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "closeAppositive")] }

def ex_20b : Datum :=
  { id := "snyder2026_20b"
    source := ⟨"snyder-2026", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Zermelo ordinal two is not two-membered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "closeAppositive")] }

def ex_76g : Datum :=
  { id := "snyder2026_76g"
    source := ⟨"snyder-2026", "(76g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two is next to a five on the board."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "tokenRef")] }

def ex_76h : Datum :=
  { id := "snyder2026_76h"
    source := ⟨"snyder-2026", "(76h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That two is next to a five on the board."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "tokenPredicate")] }

def ex_83 : Datum :=
  { id := "snyder2026_83"
    source := ⟨"snyder-2026", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two is that set."
    glossedTokens := []
    context := "Mary is taking a set theory class where the natural numbers are modeled as finite von Neumann ordinals; John asks which of the sets on the board is the number two, and Mary points at {∅, {∅}}. In a second context the natural numbers are modeled as Zermelo ordinals and Mary points at {{∅}}."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "numeral")] }

def ex_94a : Datum :=
  { id := "snyder2026_94a"
    source := ⟨"snyder-2026", "(94a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That (kind of) red is used to paint barns."
    glossedTokens := []
    context := "Mary is looking at three paint swatches, each displaying a different shade of red, and points at the first."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "taxonomic")] }

def ex_94b : Datum :=
  { id := "snyder2026_94b"
    source := ⟨"snyder-2026", "(94b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "{Red/The color red} comes in several varieties: crimson, maroon, ..."
    glossedTokens := []
    context := "Mary is looking at three paint swatches, each displaying a different shade of red."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "kindRef")] }

def ex_98 : Datum :=
  { id := "snyder2026_98"
    source := ⟨"snyder-2026", "(98)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(The color) red is {next to (the color) green/fading/barely visible}."
    glossedTokens := []
    context := "Mary is looking at a paint swatch exhibiting three colors of paint: a shade of red, a shade of green, and a shade of blue."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("function", "tokenRef")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_1e, ex_1f, ex_4a, ex_4b, ex_20a, ex_20b, ex_76g, ex_76h, ex_83, ex_94a, ex_94b, ex_98]

end Snyder2026.Examples
