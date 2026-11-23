module

public import Linglib.Data.Examples.Schema
public import Mathlib.Tactic.DeriveFintype

/-!
# `BillEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/BillEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BillEtAl2025.Examples`.
-/

@[expose] public section

namespace BillEtAl2025.Examples

def ex_1a : Datum :=
  { id := "billetal2025_1a"
    source := ⟨"bill-etal-2025", "(1a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az alma és a banán az asztal-on van."
    glossedTokens := [("Az", "the"), ("alma", "apple"), ("és", "J"), ("a", "the"), ("banán", "banana"), ("az", "the"), ("asztal-on", "table-LOC"), ("van.", "is")]
    glossedWords := [⟨['A', 'z'], ['t', 'h', 'e'], [⟨['A', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'l', 'm', 'a'], ['a', 'p', 'p', 'l', 'e'], [⟨['a', 'l', 'm', 'a'], ['a', 'p', 'p', 'l', 'e'], none⟩]⟩, ⟨['é', 's'], ['J'], [⟨['é', 's'], ['J'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'n', 'á', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['b', 'a', 'n', 'á', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 's', 'z', 't', 'a', 'l', '-', 'o', 'n'], ['t', 'a', 'b', 'l', 'e', '-', 'L', 'O', 'C'], [⟨['a', 's', 'z', 't', 'a', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['o', 'n'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['v', 'a', 'n', '.'], ['i', 's'], [⟨['v', 'a', 'n'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "j", some "es"⟩]
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "billetal2025_1b"
    source := ⟨"bill-etal-2025", "(1b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az alma is, a banán is az asztal-on van."
    glossedTokens := [("Az", "the"), ("alma", "apple"), ("is,", "MU"), ("a", "the"), ("banán", "banana"), ("is", "MU"), ("az", "the"), ("asztal-on", "table-LOC"), ("van.", "is")]
    glossedWords := [⟨['A', 'z'], ['t', 'h', 'e'], [⟨['A', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'l', 'm', 'a'], ['a', 'p', 'p', 'l', 'e'], [⟨['a', 'l', 'm', 'a'], ['a', 'p', 'p', 'l', 'e'], none⟩]⟩, ⟨['i', 's', ','], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'n', 'á', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['b', 'a', 'n', 'á', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩, ⟨['i', 's'], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 's', 'z', 't', 'a', 'l', '-', 'o', 'n'], ['t', 'a', 'b', 'l', 'e', '-', 'L', 'O', 'C'], [⟨['a', 's', 'z', 't', 'a', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['o', 'n'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['v', 'a', 'n', '.'], ['i', 's'], [⟨['v', 'a', 'n'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "mu-first", some "is"⟩, ⟨5, 1, "mu-second", some "is"⟩]
    paperFeatures := [] }

def ex_1c : Datum :=
  { id := "billetal2025_1c"
    source := ⟨"bill-etal-2025", "(1c)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az alma is és a banán is az asztal-on van."
    glossedTokens := [("Az", "the"), ("alma", "apple"), ("is", "MU"), ("és", "J"), ("a", "the"), ("banán", "banana"), ("is", "MU"), ("az", "the"), ("asztal-on", "table-LOC"), ("van.", "is")]
    glossedWords := [⟨['A', 'z'], ['t', 'h', 'e'], [⟨['A', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'l', 'm', 'a'], ['a', 'p', 'p', 'l', 'e'], [⟨['a', 'l', 'm', 'a'], ['a', 'p', 'p', 'l', 'e'], none⟩]⟩, ⟨['i', 's'], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['é', 's'], ['J'], [⟨['é', 's'], ['J'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['b', 'a', 'n', 'á', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], [⟨['b', 'a', 'n', 'á', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩]⟩, ⟨['i', 's'], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 's', 'z', 't', 'a', 'l', '-', 'o', 'n'], ['t', 'a', 'b', 'l', 'e', '-', 'L', 'O', 'C'], [⟨['a', 's', 'z', 't', 'a', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['o', 'n'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['v', 'a', 'n', '.'], ['i', 's'], [⟨['v', 'a', 'n'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "mu-first", some "is"⟩, ⟨3, 1, "j", some "es"⟩, ⟨6, 1, "mu-second", some "is"⟩]
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "billetal2025_2a"
    source := ⟨"bill-etal-2025", "(2a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vashl-i da banan-i aris magida-ze."
    glossedTokens := [("vashl-i", "apple-NOM"), ("da", "J"), ("banan-i", "banana-NOM"), ("aris", "is"), ("magida-ze.", "table-on")]
    glossedWords := [⟨['v', 'a', 's', 'h', 'l', '-', 'i'], ['a', 'p', 'p', 'l', 'e', '-', 'N', 'O', 'M'], [⟨['v', 'a', 's', 'h', 'l'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['d', 'a'], ['J'], [⟨['d', 'a'], ['J'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'n', '-', 'i'], ['b', 'a', 'n', 'a', 'n', 'a', '-', 'N', 'O', 'M'], [⟨['b', 'a', 'n', 'a', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 'd', 'a', '-', 'z', 'e', '.'], ['t', 'a', 'b', 'l', 'e', '-', 'o', 'n'], [⟨['m', 'a', 'g', 'i', 'd', 'a'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "j", some "da"⟩]
    paperFeatures := [] }

def ex_2b : Datum :=
  { id := "billetal2025_2b"
    source := ⟨"bill-etal-2025", "(2b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vashl-i-c, banan-i-c aris magida-ze."
    glossedTokens := [("vashl-i-c,", "apple-NOM-MU"), ("banan-i-c", "banana-NOM-MU"), ("aris", "is"), ("magida-ze.", "table-on")]
    glossedWords := [⟨['v', 'a', 's', 'h', 'l', '-', 'i', '-', 'c', ','], ['a', 'p', 'p', 'l', 'e', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['v', 'a', 's', 'h', 'l'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['b', 'a', 'n', 'a', 'n', '-', 'i', '-', 'c'], ['b', 'a', 'n', 'a', 'n', 'a', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['b', 'a', 'n', 'a', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 'd', 'a', '-', 'z', 'e', '.'], ['t', 'a', 'b', 'l', 'e', '-', 'o', 'n'], [⟨['m', 'a', 'g', 'i', 'd', 'a'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "mu-first", some "c"⟩, ⟨1, 1, "mu-second", some "c"⟩]
    paperFeatures := [] }

def ex_2c : Datum :=
  { id := "billetal2025_2c"
    source := ⟨"bill-etal-2025", "(2c)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "vashl-i-c da banan-i-c aris magida-ze."
    glossedTokens := [("vashl-i-c", "apple-NOM-MU"), ("da", "J"), ("banan-i-c", "banana-NOM-MU"), ("aris", "is"), ("magida-ze.", "table-on")]
    glossedWords := [⟨['v', 'a', 's', 'h', 'l', '-', 'i', '-', 'c'], ['a', 'p', 'p', 'l', 'e', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['v', 'a', 's', 'h', 'l'], ['a', 'p', 'p', 'l', 'e'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['d', 'a'], ['J'], [⟨['d', 'a'], ['J'], none⟩]⟩, ⟨['b', 'a', 'n', 'a', 'n', '-', 'i', '-', 'c'], ['b', 'a', 'n', 'a', 'n', 'a', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['b', 'a', 'n', 'a', 'n'], ['b', 'a', 'n', 'a', 'n', 'a'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 'd', 'a', '-', 'z', 'e', '.'], ['t', 'a', 'b', 'l', 'e', '-', 'o', 'n'], [⟨['m', 'a', 'g', 'i', 'd', 'a'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "mu-first", some "c"⟩, ⟨1, 1, "j", some "da"⟩, ⟨2, 1, "mu-second", some "c"⟩]
    paperFeatures := [] }

def ex_5a : Datum :=
  { id := "billetal2025_5a"
    source := ⟨"bill-etal-2025", "(5a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "k’ovz-i da saban-i aris magida-ze."
    glossedTokens := [("k’ovz-i", "spoon-NOM"), ("da", "J"), ("saban-i", "blanket-NOM"), ("aris", "is"), ("magida-ze.", "table-on")]
    glossedWords := [⟨['k', '’', 'o', 'v', 'z', '-', 'i'], ['s', 'p', 'o', 'o', 'n', '-', 'N', 'O', 'M'], [⟨['k', '’', 'o', 'v', 'z'], ['s', 'p', 'o', 'o', 'n'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['d', 'a'], ['J'], [⟨['d', 'a'], ['J'], none⟩]⟩, ⟨['s', 'a', 'b', 'a', 'n', '-', 'i'], ['b', 'l', 'a', 'n', 'k', 'e', 't', '-', 'N', 'O', 'M'], [⟨['s', 'a', 'b', 'a', 'n'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 'd', 'a', '-', 'z', 'e', '.'], ['t', 'a', 'b', 'l', 'e', '-', 'o', 'n'], [⟨['m', 'a', 'g', 'i', 'd', 'a'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "j", some "da"⟩]
    paperFeatures := [] }

def ex_5b : Datum :=
  { id := "billetal2025_5b"
    source := ⟨"bill-etal-2025", "(5b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "k’ovz-i-c, saban-i-c aris magida-ze."
    glossedTokens := [("k’ovz-i-c,", "spoon-NOM-MU"), ("saban-i-c", "blanket-NOM-MU"), ("aris", "is"), ("magida-ze.", "table-on")]
    glossedWords := [⟨['k', '’', 'o', 'v', 'z', '-', 'i', '-', 'c', ','], ['s', 'p', 'o', 'o', 'n', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['k', '’', 'o', 'v', 'z'], ['s', 'p', 'o', 'o', 'n'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['s', 'a', 'b', 'a', 'n', '-', 'i', '-', 'c'], ['b', 'l', 'a', 'n', 'k', 'e', 't', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['s', 'a', 'b', 'a', 'n'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 'd', 'a', '-', 'z', 'e', '.'], ['t', 'a', 'b', 'l', 'e', '-', 'o', 'n'], [⟨['m', 'a', 'g', 'i', 'd', 'a'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "mu-first", some "c"⟩, ⟨1, 1, "mu-second", some "c"⟩]
    paperFeatures := [] }

def ex_5c : Datum :=
  { id := "billetal2025_5c"
    source := ⟨"bill-etal-2025", "(5c)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "k’ovz-i-c da saban-i-c aris magida-ze."
    glossedTokens := [("k’ovz-i-c", "spoon-NOM-MU"), ("da", "J"), ("saban-i-c", "blanket-NOM-MU"), ("aris", "is"), ("magida-ze.", "table-on")]
    glossedWords := [⟨['k', '’', 'o', 'v', 'z', '-', 'i', '-', 'c'], ['s', 'p', 'o', 'o', 'n', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['k', '’', 'o', 'v', 'z'], ['s', 'p', 'o', 'o', 'n'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['d', 'a'], ['J'], [⟨['d', 'a'], ['J'], none⟩]⟩, ⟨['s', 'a', 'b', 'a', 'n', '-', 'i', '-', 'c'], ['b', 'l', 'a', 'n', 'k', 'e', 't', '-', 'N', 'O', 'M', '-', 'M', 'U'], [⟨['s', 'a', 'b', 'a', 'n'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], none⟩, ⟨['i'], ['N', 'O', 'M'], some '-'⟩, ⟨['c'], ['M', 'U'], some '-'⟩]⟩, ⟨['a', 'r', 'i', 's'], ['i', 's'], [⟨['a', 'r', 'i', 's'], ['i', 's'], none⟩]⟩, ⟨['m', 'a', 'g', 'i', 'd', 'a', '-', 'z', 'e', '.'], ['t', 'a', 'b', 'l', 'e', '-', 'o', 'n'], [⟨['m', 'a', 'g', 'i', 'd', 'a'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['z', 'e'], ['o', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "mu-first", some "c"⟩, ⟨1, 1, "j", some "da"⟩, ⟨2, 1, "mu-second", some "c"⟩]
    paperFeatures := [] }

def ex_6a : Datum :=
  { id := "billetal2025_6a"
    source := ⟨"bill-etal-2025", "(6a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A kanál és a takaró az asztal-on van."
    glossedTokens := [("A", "the"), ("kanál", "spoon"), ("és", "J"), ("a", "the"), ("takaró", "blanket"), ("az", "the"), ("asztal-on", "table-LOC"), ("van.", "is")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'a', 'n', 'á', 'l'], ['s', 'p', 'o', 'o', 'n'], [⟨['k', 'a', 'n', 'á', 'l'], ['s', 'p', 'o', 'o', 'n'], none⟩]⟩, ⟨['é', 's'], ['J'], [⟨['é', 's'], ['J'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'k', 'a', 'r', 'ó'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], [⟨['t', 'a', 'k', 'a', 'r', 'ó'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 's', 'z', 't', 'a', 'l', '-', 'o', 'n'], ['t', 'a', 'b', 'l', 'e', '-', 'L', 'O', 'C'], [⟨['a', 's', 'z', 't', 'a', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['o', 'n'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['v', 'a', 'n', '.'], ['i', 's'], [⟨['v', 'a', 'n'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "j", some "es"⟩]
    paperFeatures := [] }

def ex_6b : Datum :=
  { id := "billetal2025_6b"
    source := ⟨"bill-etal-2025", "(6b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A kanál is, a takaró is az asztal-on van."
    glossedTokens := [("A", "the"), ("kanál", "spoon"), ("is,", "MU"), ("a", "the"), ("takaró", "blanket"), ("is", "MU"), ("az", "the"), ("asztal-on", "table-LOC"), ("van.", "is")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'a', 'n', 'á', 'l'], ['s', 'p', 'o', 'o', 'n'], [⟨['k', 'a', 'n', 'á', 'l'], ['s', 'p', 'o', 'o', 'n'], none⟩]⟩, ⟨['i', 's', ','], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'k', 'a', 'r', 'ó'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], [⟨['t', 'a', 'k', 'a', 'r', 'ó'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], none⟩]⟩, ⟨['i', 's'], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 's', 'z', 't', 'a', 'l', '-', 'o', 'n'], ['t', 'a', 'b', 'l', 'e', '-', 'L', 'O', 'C'], [⟨['a', 's', 'z', 't', 'a', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['o', 'n'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['v', 'a', 'n', '.'], ['i', 's'], [⟨['v', 'a', 'n'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "mu-first", some "is"⟩, ⟨5, 1, "mu-second", some "is"⟩]
    paperFeatures := [] }

def ex_6c : Datum :=
  { id := "billetal2025_6c"
    source := ⟨"bill-etal-2025", "(6c)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A kanál is és a takaró is az asztal-on van."
    glossedTokens := [("A", "the"), ("kanál", "spoon"), ("is", "MU"), ("és", "J"), ("a", "the"), ("takaró", "blanket"), ("is", "MU"), ("az", "the"), ("asztal-on", "table-LOC"), ("van.", "is")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'a', 'n', 'á', 'l'], ['s', 'p', 'o', 'o', 'n'], [⟨['k', 'a', 'n', 'á', 'l'], ['s', 'p', 'o', 'o', 'n'], none⟩]⟩, ⟨['i', 's'], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['é', 's'], ['J'], [⟨['é', 's'], ['J'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'k', 'a', 'r', 'ó'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], [⟨['t', 'a', 'k', 'a', 'r', 'ó'], ['b', 'l', 'a', 'n', 'k', 'e', 't'], none⟩]⟩, ⟨['i', 's'], ['M', 'U'], [⟨['i', 's'], ['M', 'U'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 's', 'z', 't', 'a', 'l', '-', 'o', 'n'], ['t', 'a', 'b', 'l', 'e', '-', 'L', 'O', 'C'], [⟨['a', 's', 'z', 't', 'a', 'l'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['o', 'n'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['v', 'a', 'n', '.'], ['i', 's'], [⟨['v', 'a', 'n'], ['i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "mu-first", some "is"⟩, ⟨3, 1, "j", some "es"⟩, ⟨6, 1, "mu-second", some "is"⟩]
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_2a, ex_2b, ex_2c, ex_5a, ex_5b, ex_5c, ex_6a, ex_6b, ex_6c]

/-- The heads of the conjunction that the words of a row pronounce. -/
inductive SpanLabel where
  /-- j: the J particle, between the conjuncts -/
  | j
  /-- mu-first: the MU particle of the first conjunct -/
  | muFirst
  /-- mu-second: the MU particle of the second conjunct -/
  | muSecond
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("j", .j), ("mu-first", .muFirst), ("mu-second", .muSecond)]

/-- The conjunctive particles of the two languages. -/
inductive Lexeme where
  /-- da: Georgian da -/
  | da
  /-- c: Georgian -c -/
  | c
  /-- es: Hungarian és -/
  | es
  /-- is: Hungarian is -/
  | is
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("da", .da), ("c", .c), ("es", .es), ("is", .is)])

end BillEtAl2025.Examples
