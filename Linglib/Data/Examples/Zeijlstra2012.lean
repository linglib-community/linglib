module

public import Linglib.Data.Examples.Schema

/-!
# `Zeijlstra2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Zeijlstra2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zeijlstra2012.Examples`.
-/

@[expose] public section

namespace Zeijlstra2012.Examples

def ex_20a : Datum :=
  { id := "zeijlstra2012_20a"
    source := ⟨"zeijlstra-2012", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said Mary was ill"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sequence of tense")] }

def ex_20b : Datum :=
  { id := "zeijlstra2012_20b"
    source := ⟨"zeijlstra-2012", "(20b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan zei dat Marie ziek was"
    glossedTokens := [("Jan", "John"), ("zei", "said"), ("dat", "that"), ("Marie", "Mary"), ("ziek", "ill"), ("was", "was")]
    glossedWords := [⟨['J', 'a', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['z', 'e', 'i'], ['s', 'a', 'i', 'd'], [⟨['z', 'e', 'i'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['z', 'i', 'e', 'k'], ['i', 'l', 'l'], [⟨['z', 'i', 'e', 'k'], ['i', 'l', 'l'], none⟩]⟩, ⟨['w', 'a', 's'], ['w', 'a', 's'], [⟨['w', 'a', 's'], ['w', 'a', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sequence of tense")] }

def ex_21 : Datum :=
  { id := "zeijlstra2012_21"
    source := ⟨"zeijlstra-2012", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wolfgang played tennis on every Sunday"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "tense scope")] }

def ex_50a : Datum :=
  { id := "zeijlstra2012_50a"
    source := ⟨"zeijlstra-2012", "(50a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non ha detto niente a nessuno"
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("ha", "has"), ("detto", "said"), ("niente", "n-thing"), ("a", "to"), ("nessuno", "n-body")]
    glossedWords := [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['n', 'o', 'n'], ['N', 'E', 'G'], [⟨['n', 'o', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 't', 't', 'o'], ['s', 'a', 'i', 'd'], [⟨['d', 'e', 't', 't', 'o'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['n', 'i', 'e', 'n', 't', 'e'], ['n', '-', 't', 'h', 'i', 'n', 'g'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['n', 'e', 's', 's', 'u', 'n', 'o'], ['n', '-', 'b', 'o', 'd', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("type", "non-strict")] }

def ex_51a : Datum :=
  { id := "zeijlstra2012_51a"
    source := ⟨"zeijlstra-2012", "(51a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dnes nikdo nevolá nikomu"
    glossedTokens := [("Dnes", "today"), ("nikdo", "n-body"), ("nevolá", "NEG.calls"), ("nikomu", "n-body")]
    glossedWords := [⟨['D', 'n', 'e', 's'], ['t', 'o', 'd', 'a', 'y'], [⟨['D', 'n', 'e', 's'], ['t', 'o', 'd', 'a', 'y'], none⟩]⟩, ⟨['n', 'i', 'k', 'd', 'o'], ['n', '-', 'b', 'o', 'd', 'y'], []⟩, ⟨['n', 'e', 'v', 'o', 'l', 'á'], ['N', 'E', 'G', '.', 'c', 'a', 'l', 'l', 's'], [⟨['n', 'e', 'v', 'o', 'l', 'á'], ['N', 'E', 'G', '.', 'c', 'a', 'l', 'l', 's'], none⟩]⟩, ⟨['n', 'i', 'k', 'o', 'm', 'u'], ['n', '-', 'b', 'o', 'd', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("type", "strict")] }

def ex_53 : Datum :=
  { id := "zeijlstra2012_53"
    source := ⟨"zeijlstra-2012", "(53)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non ha detto che ha telefonato a nessuno"
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("ha", "has"), ("detto", "said"), ("che", "that"), ("ha", "has"), ("telefonato", "called"), ("a", "to"), ("nessuno", "n-body")]
    glossedWords := [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['n', 'o', 'n'], ['N', 'E', 'G'], [⟨['n', 'o', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 't', 't', 'o'], ['s', 'a', 'i', 'd'], [⟨['d', 'e', 't', 't', 'o'], ['s', 'a', 'i', 'd'], none⟩]⟩, ⟨['c', 'h', 'e'], ['t', 'h', 'a', 't'], [⟨['c', 'h', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 's'], [⟨['h', 'a'], ['h', 'a', 's'], none⟩]⟩, ⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'a', 't', 'o'], ['c', 'a', 'l', 'l', 'e', 'd'], [⟨['t', 'e', 'l', 'e', 'f', 'o', 'n', 'a', 't', 'o'], ['c', 'a', 'l', 'l', 'e', 'd'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['n', 'e', 's', 's', 'u', 'n', 'o'], ['n', '-', 'b', 'o', 'd', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("locality", "across CP")] }

def all : List Datum := [ex_20a, ex_20b, ex_21, ex_50a, ex_51a, ex_53]

end Zeijlstra2012.Examples
