module

public import Linglib.Data.Examples.Schema

/-!
# `Boskovic2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Boskovic2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Boskovic2018.Examples`.
-/

@[expose] public section

namespace Boskovic2018.Examples

def ex17 : Datum :=
  { id := "boskovic2018_ex17"
    source := ⟨"boskovic-2018", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wonder who friends of hired Mary."
    glossedTokens := []
    context := "Extraction from a subject that has raised from the specifier of vP."
    judgment := .nearlyUngrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex20 : Datum :=
  { id := "boskovic2018_ex20"
    source := ⟨"boskovic-2018", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kiss Mary Jane did."
    glossedTokens := []
    context := "Remnant vP fronting after the subject has raised out of vP."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex22a : Datum :=
  { id := "boskovic2018_ex22a"
    source := ⟨"boskovic-2018", "(22a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "... weil den Peter mag niemand allgemein bekannt ist."
    glossedTokens := [("weil", "since"), ("den", "the.ACC"), ("Peter", "Peter"), ("mag", "likes"), ("niemand", "nobody.NOM"), ("allgemein", "commonly"), ("bekannt", "known"), ("ist", "is")]
    glossedWords := [⟨['w', 'e', 'i', 'l'], ['s', 'i', 'n', 'c', 'e'], [⟨['w', 'e', 'i', 'l'], ['s', 'i', 'n', 'c', 'e'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['m', 'a', 'g'], ['l', 'i', 'k', 'e', 's'], [⟨['m', 'a', 'g'], ['l', 'i', 'k', 'e', 's'], none⟩]⟩, ⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y', '.', 'N', 'O', 'M'], [⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['a', 'l', 'l', 'g', 'e', 'm', 'e', 'i', 'n'], ['c', 'o', 'm', 'm', 'o', 'n', 'l', 'y'], [⟨['a', 'l', 'l', 'g', 'e', 'm', 'e', 'i', 'n'], ['c', 'o', 'm', 'm', 'o', 'n', 'l', 'y'], none⟩]⟩, ⟨['b', 'e', 'k', 'a', 'n', 'n', 't'], ['k', 'n', 'o', 'w', 'n'], [⟨['b', 'e', 'k', 'a', 'n', 'n', 't'], ['k', 'n', 'o', 'w', 'n'], none⟩]⟩, ⟨['i', 's', 't'], ['i', 's'], [⟨['i', 's', 't'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A verb-second clause moved to Spec,IP."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex22c : Datum :=
  { id := "boskovic2018_ex22c"
    source := ⟨"boskovic-2018", "(22c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie sagte den Peter mag niemand."
    glossedTokens := [("Sie", "she"), ("sagte", "said"), ("den", "the.ACC"), ("Peter", "Peter"), ("mag", "likes"), ("niemand", "nobody.NOM")]
    glossedWords := [⟨['S', 'i', 'e'], ['s', 'h', 'e'], [⟨['S', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['s', 'a', 'g', 't', 'e'], ['s', 'a', 'i', 'd'], [⟨['s', 'a', 'g', 't', 'e'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['d', 'e', 'n'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], [⟨['P', 'e', 't', 'e', 'r'], ['P', 'e', 't', 'e', 'r'], none⟩]⟩, ⟨['m', 'a', 'g'], ['l', 'i', 'k', 'e', 's'], [⟨['m', 'a', 'g'], ['l', 'i', 'k', 'e', 's'], none⟩]⟩, ⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y', '.', 'N', 'O', 'M'], [⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y', '.', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A verb-second clause in situ."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex24 : Datum :=
  { id := "boskovic2018_ex24"
    source := ⟨"boskovic-2018", "(24)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jovanovu je on vidio sliku."
    glossedTokens := [("Jovanovu", "John's.ACC.FEM.SG"), ("je", "is"), ("on", "he"), ("vidio", "seen"), ("sliku", "picture.ACC.FEM.SG")]
    glossedWords := [⟨['J', 'o', 'v', 'a', 'n', 'o', 'v', 'u'], ['J', 'o', 'h', 'n', '\'', 's', '.', 'A', 'C', 'C', '.', 'F', 'E', 'M', '.', 'S', 'G'], [⟨['J', 'o', 'v', 'a', 'n', 'o', 'v', 'u'], ['J', 'o', 'h', 'n', '\'', 's', '.', 'A', 'C', 'C', '.', 'F', 'E', 'M', '.', 'S', 'G'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['o', 'n'], ['h', 'e'], [⟨['o', 'n'], ['h', 'e'], none⟩]⟩, ⟨['v', 'i', 'd', 'i', 'o'], ['s', 'e', 'e', 'n'], [⟨['v', 'i', 'd', 'i', 'o'], ['s', 'e', 'e', 'n'], none⟩]⟩, ⟨['s', 'l', 'i', 'k', 'u'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '.', 'A', 'C', 'C', '.', 'F', 'E', 'M', '.', 'S', 'G'], [⟨['s', 'l', 'i', 'k', 'u'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '.', 'A', 'C', 'C', '.', 'F', 'E', 'M', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A possessor extracted from an object in its base position."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex25a : Datum :=
  { id := "boskovic2018_ex25a"
    source := ⟨"boskovic-2018", "(25a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jovanovu je on sliku vidio."
    glossedTokens := [("Jovanovu", "John's.ACC"), ("je", "is"), ("on", "he"), ("sliku", "picture.ACC"), ("vidio", "seen")]
    glossedWords := [⟨['J', 'o', 'v', 'a', 'n', 'o', 'v', 'u'], ['J', 'o', 'h', 'n', '\'', 's', '.', 'A', 'C', 'C'], [⟨['J', 'o', 'v', 'a', 'n', 'o', 'v', 'u'], ['J', 'o', 'h', 'n', '\'', 's', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['o', 'n'], ['h', 'e'], [⟨['o', 'n'], ['h', 'e'], none⟩]⟩, ⟨['s', 'l', 'i', 'k', 'u'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '.', 'A', 'C', 'C'], [⟨['s', 'l', 'i', 'k', 'u'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['v', 'i', 'd', 'i', 'o'], ['s', 'e', 'e', 'n'], [⟨['v', 'i', 'd', 'i', 'o'], ['s', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A possessor extracted from a fronted object."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex27 : Datum :=
  { id := "boskovic2018_ex27"
    source := ⟨"boskovic-2018", "(27)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jovanovu sliku je on vidio."
    glossedTokens := [("Jovanovu", "John's.ACC"), ("sliku", "picture.ACC"), ("je", "is"), ("on", "he"), ("vidio", "seen")]
    glossedWords := [⟨['J', 'o', 'v', 'a', 'n', 'o', 'v', 'u'], ['J', 'o', 'h', 'n', '\'', 's', '.', 'A', 'C', 'C'], [⟨['J', 'o', 'v', 'a', 'n', 'o', 'v', 'u'], ['J', 'o', 'h', 'n', '\'', 's', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['s', 'l', 'i', 'k', 'u'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '.', 'A', 'C', 'C'], [⟨['s', 'l', 'i', 'k', 'u'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['j', 'e'], ['i', 's'], [⟨['j', 'e'], ['i', 's'], none⟩]⟩, ⟨['o', 'n'], ['h', 'e'], [⟨['o', 'n'], ['h', 'e'], none⟩]⟩, ⟨['v', 'i', 'd', 'i', 'o'], ['s', 'e', 'e', 'n'], [⟨['v', 'i', 'd', 'i', 'o'], ['s', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "An object fronted with the possessor in its specifier."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex42a : Datum :=
  { id := "boskovic2018_ex42a"
    source := ⟨"boskovic-2018", "(42a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Waar had jij dan mee gedacht dat je de vis zou moeten snijden?"
    glossedTokens := [("Waar", "where"), ("had", "had"), ("jij", "you"), ("dan", "then"), ("mee", "with"), ("gedacht", "thought"), ("dat", "that"), ("je", "you"), ("de", "the"), ("vis", "fish"), ("zou", "would"), ("moeten", "must"), ("snijden", "cut")]
    glossedWords := [⟨['W', 'a', 'a', 'r'], ['w', 'h', 'e', 'r', 'e'], [⟨['W', 'a', 'a', 'r'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['h', 'a', 'd'], ['h', 'a', 'd'], [⟨['h', 'a', 'd'], ['h', 'a', 'd'], none⟩]⟩, ⟨['j', 'i', 'j'], ['y', 'o', 'u'], [⟨['j', 'i', 'j'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'a', 'n'], ['t', 'h', 'e', 'n'], [⟨['d', 'a', 'n'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['m', 'e', 'e'], ['w', 'i', 't', 'h'], [⟨['m', 'e', 'e'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['g', 'e', 'd', 'a', 'c', 'h', 't'], ['t', 'h', 'o', 'u', 'g', 'h', 't'], [⟨['g', 'e', 'd', 'a', 'c', 'h', 't'], ['t', 'h', 'o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'e'], ['y', 'o', 'u'], [⟨['j', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['d', 'e'], ['t', 'h', 'e'], [⟨['d', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 's'], ['f', 'i', 's', 'h'], [⟨['v', 'i', 's'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['z', 'o', 'u'], ['w', 'o', 'u', 'l', 'd'], [⟨['z', 'o', 'u'], ['w', 'o', 'u', 'l', 'd'], none⟩]⟩, ⟨['m', 'o', 'e', 't', 'e', 'n'], ['m', 'u', 's', 't'], [⟨['m', 'o', 'e', 't', 'e', 'n'], ['m', 'u', 's', 't'], none⟩]⟩, ⟨['s', 'n', 'i', 'j', 'd', 'e', 'n'], ['c', 'u', 't'], [⟨['s', 'n', 'i', 'j', 'd', 'e', 'n'], ['c', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "An r-pronoun extracted from a PP moved out of the embedded clause."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex17, ex20, ex22a, ex22c, ex24, ex25a, ex27, ex42a]

end Boskovic2018.Examples
