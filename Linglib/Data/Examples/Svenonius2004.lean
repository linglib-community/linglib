module

public import Linglib.Data.Examples.Schema

/-!
# `Svenonius2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Svenonius2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Svenonius2004.Examples`.
-/

@[expose] public section

namespace Svenonius2004.Examples

def ex_1a : Datum :=
  { id := "svenonius2004_1a"
    source := ⟨"svenonius-2004", "(1a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Helder za-brosil mjač v vorota angličan."
    glossedTokens := [("Helder", "Helder"), ("za-brosil", "into-threw"), ("mjač", "ball"), ("v", "in"), ("vorota", "goal"), ("angličan", "English")]
    glossedWords := [⟨['H', 'e', 'l', 'd', 'e', 'r'], ['H', 'e', 'l', 'd', 'e', 'r'], [⟨['H', 'e', 'l', 'd', 'e', 'r'], ['H', 'e', 'l', 'd', 'e', 'r'], none⟩]⟩, ⟨['z', 'a', '-', 'b', 'r', 'o', 's', 'i', 'l'], ['i', 'n', 't', 'o', '-', 't', 'h', 'r', 'e', 'w'], [⟨['z', 'a'], ['i', 'n', 't', 'o'], none⟩, ⟨['b', 'r', 'o', 's', 'i', 'l'], ['t', 'h', 'r', 'e', 'w'], some '-'⟩]⟩, ⟨['m', 'j', 'a', 'č'], ['b', 'a', 'l', 'l'], [⟨['m', 'j', 'a', 'č'], ['b', 'a', 'l', 'l'], none⟩]⟩, ⟨['v'], ['i', 'n'], [⟨['v'], ['i', 'n'], none⟩]⟩, ⟨['v', 'o', 'r', 'o', 't', 'a'], ['g', 'o', 'a', 'l'], [⟨['v', 'o', 'r', 'o', 't', 'a'], ['g', 'o', 'a', 'l'], none⟩]⟩, ⟨['a', 'n', 'g', 'l', 'i', 'č', 'a', 'n'], ['E', 'n', 'g', 'l', 'i', 's', 'h'], [⟨['a', 'n', 'g', 'l', 'i', 'č', 'a', 'n'], ['E', 'n', 'g', 'l', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Spatial-resultative za-: the goal is the endpoint of the ball's path."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "svenonius2004_1b"
    source := ⟨"svenonius-2004", "(1b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "David sovsem za-brosil futbol."
    glossedTokens := [("David", "David"), ("sovsem", "completely"), ("za-brosil", "into-threw"), ("futbol", "soccer")]
    glossedWords := [⟨['D', 'a', 'v', 'i', 'd'], ['D', 'a', 'v', 'i', 'd'], [⟨['D', 'a', 'v', 'i', 'd'], ['D', 'a', 'v', 'i', 'd'], none⟩]⟩, ⟨['s', 'o', 'v', 's', 'e', 'm'], ['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', 'l', 'y'], [⟨['s', 'o', 'v', 's', 'e', 'm'], ['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', 'l', 'y'], none⟩]⟩, ⟨['z', 'a', '-', 'b', 'r', 'o', 's', 'i', 'l'], ['i', 'n', 't', 'o', '-', 't', 'h', 'r', 'e', 'w'], [⟨['z', 'a'], ['i', 'n', 't', 'o'], none⟩, ⟨['b', 'r', 'o', 's', 'i', 'l'], ['t', 'h', 'r', 'e', 'w'], some '-'⟩]⟩, ⟨['f', 'u', 't', 'b', 'o', 'l'], ['s', 'o', 'c', 'c', 'e', 'r'], [⟨['f', 'u', 't', 'b', 'o', 'l'], ['s', 'o', 'c', 'c', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Idiomatic use of the same lexical za- as in the spatial (1a): idiosyncratic meaning is available to lexical prefixes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1c : Datum :=
  { id := "svenonius2004_1c"
    source := ⟨"svenonius-2004", "(1c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ricardo nervno za-brosal mjač."
    glossedTokens := [("Ricardo", "Ricardo"), ("nervno", "nervously"), ("za-brosal", "incp-threw"), ("mjač", "ball")]
    glossedWords := [⟨['R', 'i', 'c', 'a', 'r', 'd', 'o'], ['R', 'i', 'c', 'a', 'r', 'd', 'o'], [⟨['R', 'i', 'c', 'a', 'r', 'd', 'o'], ['R', 'i', 'c', 'a', 'r', 'd', 'o'], none⟩]⟩, ⟨['n', 'e', 'r', 'v', 'n', 'o'], ['n', 'e', 'r', 'v', 'o', 'u', 's', 'l', 'y'], [⟨['n', 'e', 'r', 'v', 'n', 'o'], ['n', 'e', 'r', 'v', 'o', 'u', 's', 'l', 'y'], none⟩]⟩, ⟨['z', 'a', '-', 'b', 'r', 'o', 's', 'a', 'l'], ['i', 'n', 'c', 'p', '-', 't', 'h', 'r', 'e', 'w'], [⟨['z', 'a'], ['i', 'n', 'c', 'p'], none⟩, ⟨['b', 'r', 'o', 's', 'a', 'l'], ['t', 'h', 'r', 'e', 'w'], some '-'⟩]⟩, ⟨['m', 'j', 'a', 'č'], ['b', 'a', 'l', 'l'], [⟨['m', 'j', 'a', 'č'], ['b', 'a', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Inceptive (superlexical) za- on the imperfective stem brosat', versus the lexical za- of (1a)/(1b) on perfective brosit'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_1b, ex_1c]

end Svenonius2004.Examples
