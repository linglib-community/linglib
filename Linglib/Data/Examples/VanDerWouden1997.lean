module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerWouden1997` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerWouden1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerWouden1997.Examples`.
-/

@[expose] public section

namespace VanDerWouden1997.Examples

def ex_184a : Datum :=
  { id := "vanderwouden1997_184a"
    source := ⟨"vanderwouden-1997", "(184a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Een van de kinderen gaat ooit bij oma op bezoek."
    glossedTokens := [("Een", "one"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    glossedWords := [⟨['E', 'e', 'n'], ['o', 'n', 'e'], [⟨['E', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['g', 'a', 'a', 't'], ['g', 'o', 'e', 's'], [⟨['g', 'a', 'a', 't'], ['g', 'o', 'e', 's'], none⟩]⟩, ⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], [⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], none⟩]⟩, ⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], [⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], [⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], [⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "notMonotoneDecreasing")] }

def ex_184b : Datum :=
  { id := "vanderwouden1997_184b"
    source := ⟨"vanderwouden-1997", "(184b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Weinig kinderen gaan ooit bij oma op bezoek."
    glossedTokens := [("Weinig", "few"), ("kinderen", "children"), ("gaan", "go"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    glossedWords := [⟨['W', 'e', 'i', 'n', 'i', 'g'], ['f', 'e', 'w'], [⟨['W', 'e', 'i', 'n', 'i', 'g'], ['f', 'e', 'w'], none⟩]⟩, ⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['g', 'a', 'a', 'n'], ['g', 'o'], [⟨['g', 'a', 'a', 'n'], ['g', 'o'], none⟩]⟩, ⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], [⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], none⟩]⟩, ⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], [⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], [⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], [⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "monotoneDecreasing")] }

def ex_184c : Datum :=
  { id := "vanderwouden1997_184c"
    source := ⟨"vanderwouden-1997", "(184c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Geen van de kinderen gaat ooit bij oma op bezoek."
    glossedTokens := [("Geen", "none"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    glossedWords := [⟨['G', 'e', 'e', 'n'], ['n', 'o', 'n', 'e'], [⟨['G', 'e', 'e', 'n'], ['n', 'o', 'n', 'e'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['g', 'a', 'a', 't'], ['g', 'o', 'e', 's'], [⟨['g', 'a', 'a', 't'], ['g', 'o', 'e', 's'], none⟩]⟩, ⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], [⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], none⟩]⟩, ⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], [⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], [⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], [⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "antiAdditive")] }

def ex_184d : Datum :=
  { id := "vanderwouden1997_184d"
    source := ⟨"vanderwouden-1997", "(184d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Een van de kinderen gaat niet ooit bij oma op bezoek."
    glossedTokens := [("Een", "one"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("niet", "not"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    glossedWords := [⟨['E', 'e', 'n'], ['o', 'n', 'e'], [⟨['E', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['v', 'a', 'n'], ['o', 'f'], [⟨['v', 'a', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['k', 'i', 'n', 'd', 'e', 'r', 'e', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['g', 'a', 'a', 't'], ['g', 'o', 'e', 's'], [⟨['g', 'a', 'a', 't'], ['g', 'o', 'e', 's'], none⟩]⟩, ⟨['n', 'i', 'e', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'e', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], [⟨['o', 'o', 'i', 't'], ['e', 'v', 'e', 'r'], none⟩]⟩, ⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], [⟨['b', 'i', 'j'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], [⟨['o', 'm', 'a'], ['g', 'r', 'a', 'n', 'n', 'y'], none⟩]⟩, ⟨['o', 'p'], ['o', 'n'], [⟨['o', 'p'], ['o', 'n'], none⟩]⟩, ⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], [⟨['b', 'e', 'z', 'o', 'e', 'k'], ['v', 'i', 's', 'i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "antimorphic")] }

def ex_228b : Datum :=
  { id := "vanderwouden1997_228b"
    source := ⟨"vanderwouden-1997", "(228b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Alle boeren die geslagen hoeven te worden bezitten een ezel."
    glossedTokens := [("Alle", "All"), ("boeren", "farmers"), ("die", "that"), ("geslagen", "beaten"), ("hoeven", "need"), ("te", "to"), ("worden", "become"), ("bezitten", "own"), ("een", "a"), ("ezel", "donkey")]
    glossedWords := [⟨['A', 'l', 'l', 'e'], ['A', 'l', 'l'], [⟨['A', 'l', 'l', 'e'], ['A', 'l', 'l'], none⟩]⟩, ⟨['b', 'o', 'e', 'r', 'e', 'n'], ['f', 'a', 'r', 'm', 'e', 'r', 's'], [⟨['b', 'o', 'e', 'r', 'e', 'n'], ['f', 'a', 'r', 'm', 'e', 'r', 's'], none⟩]⟩, ⟨['d', 'i', 'e'], ['t', 'h', 'a', 't'], [⟨['d', 'i', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e', 's', 'l', 'a', 'g', 'e', 'n'], ['b', 'e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 's', 'l', 'a', 'g', 'e', 'n'], ['b', 'e', 'a', 't', 'e', 'n'], none⟩]⟩, ⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], [⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['w', 'o', 'r', 'd', 'e', 'n'], ['b', 'e', 'c', 'o', 'm', 'e'], [⟨['w', 'o', 'r', 'd', 'e', 'n'], ['b', 'e', 'c', 'o', 'm', 'e'], none⟩]⟩, ⟨['b', 'e', 'z', 'i', 't', 't', 'e', 'n'], ['o', 'w', 'n'], [⟨['b', 'e', 'z', 'i', 't', 't', 'e', 'n'], ['o', 'w', 'n'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['e', 'z', 'e', 'l'], ['d', 'o', 'n', 'k', 'e', 'y'], [⟨['e', 'z', 'e', 'l'], ['d', 'o', 'n', 'k', 'e', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "universalRestrictor")] }

def ex_228d : Datum :=
  { id := "vanderwouden1997_228d"
    source := ⟨"vanderwouden-1997", "(228d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Geen boer die een ezel hoeft te bezitten wordt geslagen."
    glossedTokens := [("Geen", "No"), ("boer", "farmer"), ("die", "who"), ("een", "a"), ("ezel", "donkey"), ("hoeft", "needs"), ("te", "to"), ("bezitten", "own"), ("wordt", "is"), ("geslagen", "beaten")]
    glossedWords := [⟨['G', 'e', 'e', 'n'], ['N', 'o'], [⟨['G', 'e', 'e', 'n'], ['N', 'o'], none⟩]⟩, ⟨['b', 'o', 'e', 'r'], ['f', 'a', 'r', 'm', 'e', 'r'], [⟨['b', 'o', 'e', 'r'], ['f', 'a', 'r', 'm', 'e', 'r'], none⟩]⟩, ⟨['d', 'i', 'e'], ['w', 'h', 'o'], [⟨['d', 'i', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['e', 'z', 'e', 'l'], ['d', 'o', 'n', 'k', 'e', 'y'], [⟨['e', 'z', 'e', 'l'], ['d', 'o', 'n', 'k', 'e', 'y'], none⟩]⟩, ⟨['h', 'o', 'e', 'f', 't'], ['n', 'e', 'e', 'd', 's'], [⟨['h', 'o', 'e', 'f', 't'], ['n', 'e', 'e', 'd', 's'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['b', 'e', 'z', 'i', 't', 't', 'e', 'n'], ['o', 'w', 'n'], [⟨['b', 'e', 'z', 'i', 't', 't', 'e', 'n'], ['o', 'w', 'n'], none⟩]⟩, ⟨['w', 'o', 'r', 'd', 't'], ['i', 's'], [⟨['w', 'o', 'r', 'd', 't'], ['i', 's'], none⟩]⟩, ⟨['g', 'e', 's', 'l', 'a', 'g', 'e', 'n'], ['b', 'e', 'a', 't', 'e', 'n'], [⟨['g', 'e', 's', 'l', 'a', 'g', 'e', 'n'], ['b', 'e', 'a', 't', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "noRestrictor")] }

def ex_229b : Datum :=
  { id := "vanderwouden1997_229b"
    source := ⟨"vanderwouden-1997", "(229b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hoef je huiswerk te maken?"
    glossedTokens := [("Hoef", "Need"), ("je", "you"), ("huiswerk", "homework"), ("te", "to"), ("maken", "do")]
    glossedWords := [⟨['H', 'o', 'e', 'f'], ['N', 'e', 'e', 'd'], [⟨['H', 'o', 'e', 'f'], ['N', 'e', 'e', 'd'], none⟩]⟩, ⟨['j', 'e'], ['y', 'o', 'u'], [⟨['j', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['h', 'u', 'i', 's', 'w', 'e', 'r', 'k'], ['h', 'o', 'm', 'e', 'w', 'o', 'r', 'k'], [⟨['h', 'u', 'i', 's', 'w', 'e', 'r', 'k'], ['h', 'o', 'm', 'e', 'w', 'o', 'r', 'k'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['m', 'a', 'k', 'e', 'n'], ['d', 'o'], [⟨['m', 'a', 'k', 'e', 'n'], ['d', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "question")] }

def ex_229d : Datum :=
  { id := "vanderwouden1997_229d"
    source := ⟨"vanderwouden-1997", "(229d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Als je huiswerk hoeft te maken mag je geen tv kijken."
    glossedTokens := [("Als", "If"), ("je", "you"), ("huiswerk", "homework"), ("hoeft", "need"), ("te", "to"), ("maken", "do"), ("mag", "may"), ("je", "you"), ("geen", "no"), ("tv", "tv"), ("kijken", "watch")]
    glossedWords := [⟨['A', 'l', 's'], ['I', 'f'], [⟨['A', 'l', 's'], ['I', 'f'], none⟩]⟩, ⟨['j', 'e'], ['y', 'o', 'u'], [⟨['j', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['h', 'u', 'i', 's', 'w', 'e', 'r', 'k'], ['h', 'o', 'm', 'e', 'w', 'o', 'r', 'k'], [⟨['h', 'u', 'i', 's', 'w', 'e', 'r', 'k'], ['h', 'o', 'm', 'e', 'w', 'o', 'r', 'k'], none⟩]⟩, ⟨['h', 'o', 'e', 'f', 't'], ['n', 'e', 'e', 'd'], [⟨['h', 'o', 'e', 'f', 't'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['m', 'a', 'k', 'e', 'n'], ['d', 'o'], [⟨['m', 'a', 'k', 'e', 'n'], ['d', 'o'], none⟩]⟩, ⟨['m', 'a', 'g'], ['m', 'a', 'y'], [⟨['m', 'a', 'g'], ['m', 'a', 'y'], none⟩]⟩, ⟨['j', 'e'], ['y', 'o', 'u'], [⟨['j', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['g', 'e', 'e', 'n'], ['n', 'o'], [⟨['g', 'e', 'e', 'n'], ['n', 'o'], none⟩]⟩, ⟨['t', 'v'], ['t', 'v'], [⟨['t', 'v'], ['t', 'v'], none⟩]⟩, ⟨['k', 'i', 'j', 'k', 'e', 'n'], ['w', 'a', 't', 'c', 'h'], [⟨['k', 'i', 'j', 'k', 'e', 'n'], ['w', 'a', 't', 'c', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "conditionalAntecedent")] }

def ex_232a : Datum :=
  { id := "vanderwouden1997_232a"
    source := ⟨"vanderwouden-1997", "(232a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hij rijdt harder dan hij hoeft."
    glossedTokens := [("Hij", "He"), ("rijdt", "drives"), ("harder", "faster"), ("dan", "than"), ("hij", "he"), ("hoeft", "needs")]
    glossedWords := [⟨['H', 'i', 'j'], ['H', 'e'], [⟨['H', 'i', 'j'], ['H', 'e'], none⟩]⟩, ⟨['r', 'i', 'j', 'd', 't'], ['d', 'r', 'i', 'v', 'e', 's'], [⟨['r', 'i', 'j', 'd', 't'], ['d', 'r', 'i', 'v', 'e', 's'], none⟩]⟩, ⟨['h', 'a', 'r', 'd', 'e', 'r'], ['f', 'a', 's', 't', 'e', 'r'], [⟨['h', 'a', 'r', 'd', 'e', 'r'], ['f', 'a', 's', 't', 'e', 'r'], none⟩]⟩, ⟨['d', 'a', 'n'], ['t', 'h', 'a', 'n'], [⟨['d', 'a', 'n'], ['t', 'h', 'a', 'n'], none⟩]⟩, ⟨['h', 'i', 'j'], ['h', 'e'], [⟨['h', 'i', 'j'], ['h', 'e'], none⟩]⟩, ⟨['h', 'o', 'e', 'f', 't'], ['n', 'e', 'e', 'd', 's'], [⟨['h', 'o', 'e', 'f', 't'], ['n', 'e', 'e', 'd', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "clausalComparative")] }

def ex_233a : Datum :=
  { id := "vanderwouden1997_233a"
    source := ⟨"vanderwouden-1997", "(233a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Dit is de laatste student die we hoeven te bestraffen."
    glossedTokens := [("Dit", "This"), ("is", "is"), ("de", "the"), ("laatste", "last"), ("student", "student"), ("die", ""), ("we", "we"), ("hoeven", "need"), ("te", "to"), ("bestraffen", "punish")]
    glossedWords := [⟨['D', 'i', 't'], ['T', 'h', 'i', 's'], [⟨['D', 'i', 't'], ['T', 'h', 'i', 's'], none⟩]⟩, ⟨['i', 's'], ['i', 's'], [⟨['i', 's'], ['i', 's'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'a', 'a', 't', 's', 't', 'e'], ['l', 'a', 's', 't'], [⟨['l', 'a', 'a', 't', 's', 't', 'e'], ['l', 'a', 's', 't'], none⟩]⟩, ⟨['s', 't', 'u', 'd', 'e', 'n', 't'], ['s', 't', 'u', 'd', 'e', 'n', 't'], [⟨['s', 't', 'u', 'd', 'e', 'n', 't'], ['s', 't', 'u', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['d', 'i', 'e'], [], []⟩, ⟨['w', 'e'], ['w', 'e'], [⟨['w', 'e'], ['w', 'e'], none⟩]⟩, ⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], [⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['b', 'e', 's', 't', 'r', 'a', 'f', 'f', 'e', 'n'], ['p', 'u', 'n', 'i', 's', 'h'], [⟨['b', 'e', 's', 't', 'r', 'a', 'f', 'f', 'e', 'n'], ['p', 'u', 'n', 'i', 's', 'h'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "superlative")] }

def ex_234a : Datum :=
  { id := "vanderwouden1997_234a"
    source := ⟨"vanderwouden-1997", "(234a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Alles wat we hoeven te weten staat in dit boek."
    glossedTokens := [("Alles", "Everything"), ("wat", "which"), ("we", "we"), ("hoeven", "need"), ("te", "to"), ("weten", "know"), ("staat", "stands"), ("in", "in"), ("dit", "this"), ("boek", "book")]
    glossedWords := [⟨['A', 'l', 'l', 'e', 's'], ['E', 'v', 'e', 'r', 'y', 't', 'h', 'i', 'n', 'g'], [⟨['A', 'l', 'l', 'e', 's'], ['E', 'v', 'e', 'r', 'y', 't', 'h', 'i', 'n', 'g'], none⟩]⟩, ⟨['w', 'a', 't'], ['w', 'h', 'i', 'c', 'h'], [⟨['w', 'a', 't'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['w', 'e'], ['w', 'e'], [⟨['w', 'e'], ['w', 'e'], none⟩]⟩, ⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], [⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['w', 'e', 't', 'e', 'n'], ['k', 'n', 'o', 'w'], [⟨['w', 'e', 't', 'e', 'n'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['s', 't', 'a', 'a', 't'], ['s', 't', 'a', 'n', 'd', 's'], [⟨['s', 't', 'a', 'a', 't'], ['s', 't', 'a', 'n', 'd', 's'], none⟩]⟩, ⟨['i', 'n'], ['i', 'n'], [⟨['i', 'n'], ['i', 'n'], none⟩]⟩, ⟨['d', 'i', 't'], ['t', 'h', 'i', 's'], [⟨['d', 'i', 't'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['b', 'o', 'e', 'k'], ['b', 'o', 'o', 'k'], [⟨['b', 'o', 'e', 'k'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "universalRestrictor")] }

def ex_234c : Datum :=
  { id := "vanderwouden1997_234c"
    source := ⟨"vanderwouden-1997", "(234c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik geloof niet, dat we nog iemand hoeven te waarschuwen."
    glossedTokens := [("Ik", "I"), ("geloof", "believe"), ("niet", "not"), ("dat", "that"), ("we", "we"), ("nog", "still"), ("iemand", "anybody"), ("hoeven", "need"), ("te", "to"), ("waarschuwen", "warn")]
    glossedWords := [⟨['I', 'k'], ['I'], [⟨['I', 'k'], ['I'], none⟩]⟩, ⟨['g', 'e', 'l', 'o', 'o', 'f'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], [⟨['g', 'e', 'l', 'o', 'o', 'f'], ['b', 'e', 'l', 'i', 'e', 'v', 'e'], none⟩]⟩, ⟨['n', 'i', 'e', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'e', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['w', 'e'], ['w', 'e'], [⟨['w', 'e'], ['w', 'e'], none⟩]⟩, ⟨['n', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['n', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['i', 'e', 'm', 'a', 'n', 'd'], ['a', 'n', 'y', 'b', 'o', 'd', 'y'], [⟨['i', 'e', 'm', 'a', 'n', 'd'], ['a', 'n', 'y', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], [⟨['h', 'o', 'e', 'v', 'e', 'n'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['t', 'e'], ['t', 'o'], [⟨['t', 'e'], ['t', 'o'], none⟩]⟩, ⟨['w', 'a', 'a', 'r', 's', 'c', 'h', 'u', 'w', 'e', 'n'], ['w', 'a', 'r', 'n'], [⟨['w', 'a', 'a', 'r', 's', 'c', 'h', 'u', 'w', 'e', 'n'], ['w', 'a', 'r', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "superordinateNegation")] }

def ex_234e : Datum :=
  { id := "vanderwouden1997_234e"
    source := ⟨"vanderwouden-1997", "(234e)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb nog een uur voordat ik weg hoef."
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("nog", "still"), ("een", "an"), ("uur", "hour"), ("voordat", "before"), ("ik", "I"), ("weg", "away"), ("hoef", "need")]
    glossedWords := [⟨['I', 'k'], ['I'], [⟨['I', 'k'], ['I'], none⟩]⟩, ⟨['h', 'e', 'b'], ['h', 'a', 'v', 'e'], [⟨['h', 'e', 'b'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['n', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['n', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a', 'n'], [⟨['e', 'e', 'n'], ['a', 'n'], none⟩]⟩, ⟨['u', 'u', 'r'], ['h', 'o', 'u', 'r'], [⟨['u', 'u', 'r'], ['h', 'o', 'u', 'r'], none⟩]⟩, ⟨['v', 'o', 'o', 'r', 'd', 'a', 't'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['v', 'o', 'o', 'r', 'd', 'a', 't'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['i', 'k'], ['I'], [⟨['i', 'k'], ['I'], none⟩]⟩, ⟨['w', 'e', 'g'], ['a', 'w', 'a', 'y'], [⟨['w', 'e', 'g'], ['a', 'w', 'a', 'y'], none⟩]⟩, ⟨['h', 'o', 'e', 'f'], ['n', 'e', 'e', 'd'], [⟨['h', 'o', 'e', 'f'], ['n', 'e', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "hoeven"), ("context", "beforeClause")] }

def all : List Datum := [ex_184a, ex_184b, ex_184c, ex_184d, ex_228b, ex_228d, ex_229b, ex_229d, ex_232a, ex_233a, ex_234a, ex_234c, ex_234e]

end VanDerWouden1997.Examples
