module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Rakosi2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Rakosi2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rakosi2020.Examples`.
-/

@[expose] public section

namespace Rakosi2020.Examples

def ex_1a : Datum :=
  { id := "rakosi2020_1a"
    source := ⟨"rakosi-2020", "(1a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látták egymás-t a tükörben."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látták", "saw.3PL"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k', '-', 'e', 'k'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['e', 'k'], ['P', 'L'], some '-'⟩]⟩, ⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], [⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n', '.'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], [⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "plural")] }

def ex_1b : Datum :=
  { id := "rakosi2020_1b"
    source := ⟨"rakosi-2020", "(1b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látták maguk-at a tükörben."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látták", "saw.3PL"), ("maguk-at", "themselves-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k', '-', 'e', 'k'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['e', 'k'], ['P', 'L'], some '-'⟩]⟩, ⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], [⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', '-', 'a', 't'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'k'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n', '.'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], [⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "plural")] }

def ex_2a : Datum :=
  { id := "rakosi2020_2a"
    source := ⟨"rakosi-2020", "(2a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek látta egymás-t a tükörben."
    glossedTokens := [("A", "the"), ("gyerek", "child"), ("látta", "saw.3SG"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], [⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n', '.'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], [⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨3, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "atomic")] }

def ex_2b : Datum :=
  { id := "rakosi2020_2b"
    source := ⟨"rakosi-2020", "(2b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek látta magá-t a tükörben."
    glossedTokens := [("A", "the"), ("gyerek", "child"), ("látta", "saw.3SG"), ("magá-t", "oneself-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], [⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'á', '-', 't'], ['o', 'n', 'e', 's', 'e', 'l', 'f', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'á'], ['o', 'n', 'e', 's', 'e', 'l', 'f'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n', '.'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], [⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "anaphor", some "maga"⟩]
    paperFeatures := [("antecedent", "atomic")] }

def ex_3a : Datum :=
  { id := "rakosi2020_3a"
    source := ⟨"rakosi-2020", "(3a)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Látom magunk-at ülni az autóban."
    glossedTokens := [("Látom", "see.1SG"), ("magunk-at", "ourselves-ACC"), ("ülni", "sit.INF"), ("az", "the"), ("autóban.", "car.in")]
    glossedWords := [⟨['L', 'á', 't', 'o', 'm'], ['s', 'e', 'e', '.', '1', 'S', 'G'], [⟨['L', 'á', 't', 'o', 'm'], ['s', 'e', 'e', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'n', 'k', '-', 'a', 't'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'n', 'k'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['ü', 'l', 'n', 'i'], ['s', 'i', 't', '.', 'I', 'N', 'F'], [⟨['ü', 'l', 'n', 'i'], ['s', 'i', 't', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'u', 't', 'ó', 'b', 'a', 'n', '.'], ['c', 'a', 'r', '.', 'i', 'n'], [⟨['a', 'u', 't', 'ó', 'b', 'a', 'n'], ['c', 'a', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "anaphor", some "magunk"⟩]
    paperFeatures := [("antecedent", "inclusive")] }

def ex_3b : Datum :=
  { id := "rakosi2020_3b"
    source := ⟨"rakosi-2020", "(3b)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Sokszor sajnálom magunk-at."
    glossedTokens := [("Sokszor", "often"), ("sajnálom", "feel_sorry.1SG"), ("magunk-at.", "ourselves-ACC")]
    glossedWords := [⟨['S', 'o', 'k', 's', 'z', 'o', 'r'], ['o', 'f', 't', 'e', 'n'], [⟨['S', 'o', 'k', 's', 'z', 'o', 'r'], ['o', 'f', 't', 'e', 'n'], none⟩]⟩, ⟨['s', 'a', 'j', 'n', 'á', 'l', 'o', 'm'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'S', 'G'], [⟨['s', 'a', 'j', 'n', 'á', 'l', 'o', 'm'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'n', 'k', '-', 'a', 't', '.'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'n', 'k'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "anaphor", some "magunk"⟩]
    paperFeatures := [("antecedent", "inclusive")] }

def ex_4a : Datum :=
  { id := "rakosi2020_4a"
    source := ⟨"rakosi-2020", "(4a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Csak én sajnálom magunk-at."
    glossedTokens := [("Csak", "only"), ("én", "I"), ("sajnálom", "feel_sorry.1SG"), ("magunk-at.", "ourselves-ACC")]
    glossedWords := [⟨['C', 's', 'a', 'k'], ['o', 'n', 'l', 'y'], [⟨['C', 's', 'a', 'k'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['é', 'n'], ['I'], [⟨['é', 'n'], ['I'], none⟩]⟩, ⟨['s', 'a', 'j', 'n', 'á', 'l', 'o', 'm'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'S', 'G'], [⟨['s', 'a', 'j', 'n', 'á', 'l', 'o', 'm'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'n', 'k', '-', 'a', 't', '.'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'n', 'k'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("referential", .acceptable), ("bound variable", .ungrammatical)]
    spans := [⟨3, 1, "anaphor", some "magunk"⟩]
    paperFeatures := [("antecedent", "inclusive")] }

def ex_4b : Datum :=
  { id := "rakosi2020_4b"
    source := ⟨"rakosi-2020", "(4b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Csak mi sajnáljuk magunk-at."
    glossedTokens := [("Csak", "only"), ("mi", "we"), ("sajnáljuk", "feel_sorry.1PL"), ("magunk-at.", "ourselves-ACC")]
    glossedWords := [⟨['C', 's', 'a', 'k'], ['o', 'n', 'l', 'y'], [⟨['C', 's', 'a', 'k'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['m', 'i'], ['w', 'e'], [⟨['m', 'i'], ['w', 'e'], none⟩]⟩, ⟨['s', 'a', 'j', 'n', 'á', 'l', 'j', 'u', 'k'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'P', 'L'], [⟨['s', 'a', 'j', 'n', 'á', 'l', 'j', 'u', 'k'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'P', 'L'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'n', 'k', '-', 'a', 't', '.'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'n', 'k'], ['o', 'u', 'r', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("bound variable", .acceptable)]
    spans := [⟨3, 1, "anaphor", some "magunk"⟩]
    paperFeatures := [("antecedent", "plural")] }

def ex_4c : Datum :=
  { id := "rakosi2020_4c"
    source := ⟨"rakosi-2020", "(4c)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Csak mi sajnáljuk egymás-t."
    glossedTokens := [("Csak", "only"), ("mi", "we"), ("sajnáljuk", "feel_sorry.1PL"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['C', 's', 'a', 'k'], ['o', 'n', 'l', 'y'], [⟨['C', 's', 'a', 'k'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['m', 'i'], ['w', 'e'], [⟨['m', 'i'], ['w', 'e'], none⟩]⟩, ⟨['s', 'a', 'j', 'n', 'á', 'l', 'j', 'u', 'k'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'P', 'L'], [⟨['s', 'a', 'j', 'n', 'á', 'l', 'j', 'u', 'k'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'P', 'L'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("bound variable", .acceptable)]
    spans := [⟨3, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "plural")] }

def ex_5a : Datum :=
  { id := "rakosi2020_5a"
    source := ⟨"rakosi-2020", "(5a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek jól viselték maguk-at."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("jól", "well"), ("viselték", "behave.3PL"), ("maguk-at.", "themselves-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k', '-', 'e', 'k'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['e', 'k'], ['P', 'L'], some '-'⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['v', 'i', 's', 'e', 'l', 't', 'é', 'k'], ['b', 'e', 'h', 'a', 'v', 'e', '.', '3', 'P', 'L'], [⟨['v', 'i', 's', 'e', 'l', 't', 'é', 'k'], ['b', 'e', 'h', 'a', 'v', 'e', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', '-', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'k'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "plural")] }

def ex_5b : Datum :=
  { id := "rakosi2020_5b"
    source := ⟨"rakosi-2020", "(5b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek jól viselte maguk-at."
    glossedTokens := [("A", "the"), ("gyerek", "child"), ("jól", "well"), ("viselte", "behave.3SG"), ("maguk-at.", "themselves-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['v', 'i', 's', 'e', 'l', 't', 'e'], ['b', 'e', 'h', 'a', 'v', 'e', '.', '3', 'S', 'G'], [⟨['v', 'i', 's', 'e', 'l', 't', 'e'], ['b', 'e', 'h', 'a', 'v', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', '-', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'k'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "atomic")] }

def ex_6 : Datum :=
  { id := "rakosi2020_6"
    source := ⟨"rakosi-2020", "(6)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Sokszor sajnálom egymás-t."
    glossedTokens := [("Sokszor", "often"), ("sajnálom", "feel_sorry.1SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['S', 'o', 'k', 's', 'z', 'o', 'r'], ['o', 'f', 't', 'e', 'n'], [⟨['S', 'o', 'k', 's', 'z', 'o', 'r'], ['o', 'f', 't', 'e', 'n'], none⟩]⟩, ⟨['s', 'a', 'j', 'n', 'á', 'l', 'o', 'm'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'S', 'G'], [⟨['s', 'a', 'j', 'n', 'á', 'l', 'o', 'm'], ['f', 'e', 'e', 'l', '_', 's', 'o', 'r', 'r', 'y', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨2, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "inclusive")] }

def ex_7a : Datum :=
  { id := "rakosi2020_7a"
    source := ⟨"rakosi-2020", "(7a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látták a kép-et."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látták", "saw.3PL"), ("a", "the"), ("kép-et.", "picture-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k', '-', 'e', 'k'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['e', 'k'], ['P', 'L'], some '-'⟩]⟩, ⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], [⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 'p', '-', 'e', 't', '.'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'A', 'C', 'C'], [⟨['k', 'é', 'p'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩, ⟨['e', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "plural")] }

def ex_7a_ : Datum :=
  { id := "rakosi2020_7a_"
    source := ⟨"rakosi-2020", "(7a')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látta a kép-et."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látta", "saw.3SG"), ("a", "the"), ("kép-et.", "picture-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k', '-', 'e', 'k'], ['c', 'h', 'i', 'l', 'd', '-', 'P', 'L'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['e', 'k'], ['P', 'L'], some '-'⟩]⟩, ⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], [⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 'p', '-', 'e', 't', '.'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'A', 'C', 'C'], [⟨['k', 'é', 'p'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩, ⟨['e', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "plural")] }

def ex_7b : Datum :=
  { id := "rakosi2020_7b"
    source := ⟨"rakosi-2020", "(7b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Két gyerek látta a kép-et."
    glossedTokens := [("Két", "two"), ("gyerek", "child"), ("látta", "saw.3SG"), ("a", "the"), ("kép-et.", "picture-ACC")]
    glossedWords := [⟨['K', 'é', 't'], ['t', 'w', 'o'], [⟨['K', 'é', 't'], ['t', 'w', 'o'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], [⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 'p', '-', 'e', 't', '.'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'A', 'C', 'C'], [⟨['k', 'é', 'p'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩, ⟨['e', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Minden gyerek látta a kép-et.", .acceptable), ("Néhány gyerek látta a kép-et.", .acceptable), ("Két gyerek-ek látta a kép-et.", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "quantified")] }

def ex_7b_ : Datum :=
  { id := "rakosi2020_7b_"
    source := ⟨"rakosi-2020", "(7b')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Két gyerek látták a kép-et."
    glossedTokens := [("Két", "two"), ("gyerek", "child"), ("látták", "saw.3PL"), ("a", "the"), ("kép-et.", "picture-ACC")]
    glossedWords := [⟨['K', 'é', 't'], ['t', 'w', 'o'], [⟨['K', 'é', 't'], ['t', 'w', 'o'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], [⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 'p', '-', 'e', 't', '.'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'A', 'C', 'C'], [⟨['k', 'é', 'p'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩, ⟨['e', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "quantified")] }

def ex_8a : Datum :=
  { id := "rakosi2020_8a"
    source := ⟨"rakosi-2020", "(8a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A két gyerek jól érezte magá-t."
    glossedTokens := [("A", "the"), ("két", "two"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("magá-t.", "oneself-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 't'], ['t', 'w', 'o'], [⟨['k', 'é', 't'], ['t', 'w', 'o'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], [⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'á', '-', 't', '.'], ['o', 'n', 'e', 's', 'e', 'l', 'f', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'á'], ['o', 'n', 'e', 's', 'e', 'l', 'f'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "maga"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_8a_ : Datum :=
  { id := "rakosi2020_8a_"
    source := ⟨"rakosi-2020", "(8a')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A két gyerek jól érezte maguk-at."
    glossedTokens := [("A", "the"), ("két", "two"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("maguk-at.", "themselves-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 't'], ['t', 'w', 'o'], [⟨['k', 'é', 't'], ['t', 'w', 'o'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], [⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', '-', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'k'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_8b : Datum :=
  { id := "rakosi2020_8b"
    source := ⟨"rakosi-2020", "(8b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Néhány gyerek jól érezte magá-t."
    glossedTokens := [("Néhány", "some"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("magá-t.", "oneself-ACC")]
    glossedWords := [⟨['N', 'é', 'h', 'á', 'n', 'y'], ['s', 'o', 'm', 'e'], [⟨['N', 'é', 'h', 'á', 'n', 'y'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], [⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'á', '-', 't', '.'], ['o', 'n', 'e', 's', 'e', 'l', 'f', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'á'], ['o', 'n', 'e', 's', 'e', 'l', 'f'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maga"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_8b_ : Datum :=
  { id := "rakosi2020_8b_"
    source := ⟨"rakosi-2020", "(8b')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Néhány gyerek jól érezte maguk-at."
    glossedTokens := [("Néhány", "some"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("maguk-at.", "themselves-ACC")]
    glossedWords := [⟨['N', 'é', 'h', 'á', 'n', 'y'], ['s', 'o', 'm', 'e'], [⟨['N', 'é', 'h', 'á', 'n', 'y'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], [⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', '-', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'k'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_9a : Datum :=
  { id := "rakosi2020_9a"
    source := ⟨"rakosi-2020", "(9a)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A szobában három kisgyerek kergeti egymás-t."
    glossedTokens := [("A", "the"), ("szobában", "room.in"), ("három", "three"), ("kisgyerek", "little.child"), ("kergeti", "chase.3SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'o', 'b', 'á', 'b', 'a', 'n'], ['r', 'o', 'o', 'm', '.', 'i', 'n'], [⟨['s', 'z', 'o', 'b', 'á', 'b', 'a', 'n'], ['r', 'o', 'o', 'm', '.', 'i', 'n'], none⟩]⟩, ⟨['h', 'á', 'r', 'o', 'm'], ['t', 'h', 'r', 'e', 'e'], [⟨['h', 'á', 'r', 'o', 'm'], ['t', 'h', 'r', 'e', 'e'], none⟩]⟩, ⟨['k', 'i', 's', 'g', 'y', 'e', 'r', 'e', 'k'], ['l', 'i', 't', 't', 'l', 'e', '.', 'c', 'h', 'i', 'l', 'd'], [⟨['k', 'i', 's', 'g', 'y', 'e', 'r', 'e', 'k'], ['l', 'i', 't', 't', 'l', 'e', '.', 'c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['k', 'e', 'r', 'g', 'e', 't', 'i'], ['c', 'h', 'a', 's', 'e', '.', '3', 'S', 'G'], [⟨['k', 'e', 'r', 'g', 'e', 't', 'i'], ['c', 'h', 'a', 's', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_9b : Datum :=
  { id := "rakosi2020_9b"
    source := ⟨"rakosi-2020", "(9b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Néhány szomszéd gyerek nagyon szereti egymás-t."
    glossedTokens := [("Néhány", "some"), ("szomszéd", "neighbour"), ("gyerek", "child"), ("nagyon", "much"), ("szereti", "love.3SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['N', 'é', 'h', 'á', 'n', 'y'], ['s', 'o', 'm', 'e'], [⟨['N', 'é', 'h', 'á', 'n', 'y'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['s', 'z', 'o', 'm', 's', 'z', 'é', 'd'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r'], [⟨['s', 'z', 'o', 'm', 's', 'z', 'é', 'd'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r'], none⟩]⟩, ⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], [⟨['g', 'y', 'e', 'r', 'e', 'k'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['n', 'a', 'g', 'y', 'o', 'n'], ['m', 'u', 'c', 'h'], [⟨['n', 'a', 'g', 'y', 'o', 'n'], ['m', 'u', 'c', 'h'], none⟩]⟩, ⟨['s', 'z', 'e', 'r', 'e', 't', 'i'], ['l', 'o', 'v', 'e', '.', '3', 'S', 'G'], [⟨['s', 'z', 'e', 'r', 'e', 't', 'i'], ['l', 'o', 'v', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_9c : Datum :=
  { id := "rakosi2020_9c"
    source := ⟨"rakosi-2020", "(9c)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Otthon mindenki szerette egymás-t."
    glossedTokens := [("Otthon", "home"), ("mindenki", "everyone"), ("szerette", "loved.3SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['O', 't', 't', 'h', 'o', 'n'], ['h', 'o', 'm', 'e'], [⟨['O', 't', 't', 'h', 'o', 'n'], ['h', 'o', 'm', 'e'], none⟩]⟩, ⟨['m', 'i', 'n', 'd', 'e', 'n', 'k', 'i'], ['e', 'v', 'e', 'r', 'y', 'o', 'n', 'e'], [⟨['m', 'i', 'n', 'd', 'e', 'n', 'k', 'i'], ['e', 'v', 'e', 'r', 'y', 'o', 'n', 'e'], none⟩]⟩, ⟨['s', 'z', 'e', 'r', 'e', 't', 't', 'e'], ['l', 'o', 'v', 'e', 'd', '.', '3', 'S', 'G'], [⟨['s', 'z', 'e', 'r', 'e', 't', 't', 'e'], ['l', 'o', 'v', 'e', 'd', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_9d : Datum :=
  { id := "rakosi2020_9d"
    source := ⟨"rakosi-2020", "(9d)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A sokaságban senki se keresi egymás-t."
    glossedTokens := [("A", "the"), ("sokaságban", "crowd.in"), ("senki", "nobody"), ("se", "not"), ("keresi", "search_for.3SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'o', 'k', 'a', 's', 'á', 'g', 'b', 'a', 'n'], ['c', 'r', 'o', 'w', 'd', '.', 'i', 'n'], [⟨['s', 'o', 'k', 'a', 's', 'á', 'g', 'b', 'a', 'n'], ['c', 'r', 'o', 'w', 'd', '.', 'i', 'n'], none⟩]⟩, ⟨['s', 'e', 'n', 'k', 'i'], ['n', 'o', 'b', 'o', 'd', 'y'], [⟨['s', 'e', 'n', 'k', 'i'], ['n', 'o', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['s', 'e'], ['n', 'o', 't'], [⟨['s', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['k', 'e', 'r', 'e', 's', 'i'], ['s', 'e', 'a', 'r', 'c', 'h', '_', 'f', 'o', 'r', '.', '3', 'S', 'G'], [⟨['k', 'e', 'r', 'e', 's', 'i'], ['s', 'e', 'a', 'r', 'c', 'h', '_', 'f', 'o', 'r', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "quantified")] }

def ex_10 : Datum :=
  { id := "rakosi2020_10"
    source := ⟨"rakosi-2020", "(10)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látta a képet."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látta", "saw.3SG"), ("a", "the"), ("képet.", "picture-ACC")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], [⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 'p', 'e', 't', '.'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'A', 'C', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "coordinate")] }

def ex_10_ : Datum :=
  { id := "rakosi2020_10_"
    source := ⟨"rakosi-2020", "(10')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látták a képet."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látták", "saw.3PL"), ("a", "the"), ("képet.", "picture-ACC")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], [⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['k', 'é', 'p', 'e', 't', '.'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 'A', 'C', 'C'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "coordinate")] }

def ex_11a : Datum :=
  { id := "rakosi2020_11a"
    source := ⟨"rakosi-2020", "(11a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzta magát."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzta", "out.drew.3SG"), ("magát.", "herself")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['k', 'i', 'h', 'ú', 'z', 't', 'a'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'S', 'G'], [⟨['k', 'i', 'h', 'ú', 'z', 't', 'a'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'á', 't', '.'], ['h', 'e', 'r', 's', 'e', 'l', 'f'], [⟨['m', 'a', 'g', 'á', 't'], ['h', 'e', 'r', 's', 'e', 'l', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maga"⟩]
    paperFeatures := [("antecedent", "coordinate")] }

def ex_11a_ : Datum :=
  { id := "rakosi2020_11a_"
    source := ⟨"rakosi-2020", "(11a')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzta magukat."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzta", "out.drew.3SG"), ("magukat.", "themselves")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['k', 'i', 'h', 'ú', 'z', 't', 'a'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'S', 'G'], [⟨['k', 'i', 'h', 'ú', 'z', 't', 'a'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], [⟨['m', 'a', 'g', 'u', 'k', 'a', 't'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "coordinate")] }

def ex_11b : Datum :=
  { id := "rakosi2020_11b"
    source := ⟨"rakosi-2020", "(11b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzták magukat."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzták", "out.drew.3PL"), ("magukat.", "themselves")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['k', 'i', 'h', 'ú', 'z', 't', 'á', 'k'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'P', 'L'], [⟨['k', 'i', 'h', 'ú', 'z', 't', 'á', 'k'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], [⟨['m', 'a', 'g', 'u', 'k', 'a', 't'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "coordinate")] }

def ex_11b_ : Datum :=
  { id := "rakosi2020_11b_"
    source := ⟨"rakosi-2020", "(11b')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzták magát."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzták", "out.drew.3PL"), ("magát.", "herself")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['k', 'i', 'h', 'ú', 'z', 't', 'á', 'k'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'P', 'L'], [⟨['k', 'i', 'h', 'ú', 'z', 't', 'á', 'k'], ['o', 'u', 't', '.', 'd', 'r', 'e', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['m', 'a', 'g', 'á', 't', '.'], ['h', 'e', 'r', 's', 'e', 'l', 'f'], [⟨['m', 'a', 'g', 'á', 't'], ['h', 'e', 'r', 's', 'e', 'l', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "maga"⟩]
    paperFeatures := [("antecedent", "coordinate")] }

def ex_12 : Datum :=
  { id := "rakosi2020_12"
    source := ⟨"rakosi-2020", "(12)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látta egymás-t a tükörben."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látta", "saw.3SG"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], [⟨['l', 'á', 't', 't', 'a'], ['s', 'a', 'w', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n', '.'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], [⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "coordinate")] }

def ex_12_ : Datum :=
  { id := "rakosi2020_12_"
    source := ⟨"rakosi-2020", "(12')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látták egymás-t a tükörben."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látták", "saw.3PL"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    glossedWords := [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'i'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], [⟨['l', 'á', 't', 't', 'á', 'k'], ['s', 'a', 'w', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n', '.'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], [⟨['t', 'ü', 'k', 'ö', 'r', 'b', 'e', 'n'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "coordinate")] }

def ex_13 : Datum :=
  { id := "rakosi2020_13"
    source := ⟨"rakosi-2020", "(13)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A személyzet úgy gondolta, hogy ők már eleget dolgoztak."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("úgy", "so"), ("gondolta,", "thought.3SG"), ("hogy", "that"), ("ők", "they"), ("már", "already"), ("eleget", "enough"), ("dolgoztak.", "worked.3PL")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], [⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], none⟩]⟩, ⟨['ú', 'g', 'y'], ['s', 'o'], [⟨['ú', 'g', 'y'], ['s', 'o'], none⟩]⟩, ⟨['g', 'o', 'n', 'd', 'o', 'l', 't', 'a', ','], ['t', 'h', 'o', 'u', 'g', 'h', 't', '.', '3', 'S', 'G'], [⟨['g', 'o', 'n', 'd', 'o', 'l', 't', 'a'], ['t', 'h', 'o', 'u', 'g', 'h', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['h', 'o', 'g', 'y'], ['t', 'h', 'a', 't'], [⟨['h', 'o', 'g', 'y'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ő', 'k'], ['t', 'h', 'e', 'y'], [⟨['ő', 'k'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['m', 'á', 'r'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], [⟨['m', 'á', 'r'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], none⟩]⟩, ⟨['e', 'l', 'e', 'g', 'e', 't'], ['e', 'n', 'o', 'u', 'g', 'h'], [⟨['e', 'l', 'e', 'g', 'e', 't'], ['e', 'n', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['d', 'o', 'l', 'g', 'o', 'z', 't', 'a', 'k', '.'], ['w', 'o', 'r', 'k', 'e', 'd', '.', '3', 'P', 'L'], [⟨['d', 'o', 'l', 'g', 'o', 'z', 't', 'a', 'k'], ['w', 'o', 'r', 'k', 'e', 'd', '.', '3', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_14 : Datum :=
  { id := "rakosi2020_14"
    source := ⟨"rakosi-2020", "(14)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A személyzet fáradt volt."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("fáradt", "tired"), ("volt.", "was.3SG")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], [⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], none⟩]⟩, ⟨['f', 'á', 'r', 'a', 'd', 't'], ['t', 'i', 'r', 'e', 'd'], [⟨['f', 'á', 'r', 'a', 'd', 't'], ['t', 'i', 'r', 'e', 'd'], none⟩]⟩, ⟨['v', 'o', 'l', 't', '.'], ['w', 'a', 's', '.', '3', 'S', 'G'], [⟨['v', 'o', 'l', 't'], ['w', 'a', 's', '.', '3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "collective")] }

def ex_14_ : Datum :=
  { id := "rakosi2020_14_"
    source := ⟨"rakosi-2020", "(14')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A személyzet fáradt voltak."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("fáradt", "tired"), ("voltak.", "were.3PL")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], [⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], none⟩]⟩, ⟨['f', 'á', 'r', 'a', 'd', 't'], ['t', 'i', 'r', 'e', 'd'], [⟨['f', 'á', 'r', 'a', 'd', 't'], ['t', 'i', 'r', 'e', 'd'], none⟩]⟩, ⟨['v', 'o', 'l', 't', 'a', 'k', '.'], ['w', 'e', 'r', 'e', '.', '3', 'P', 'L'], [⟨['v', 'o', 'l', 't', 'a', 'k'], ['w', 'e', 'r', 'e', '.', '3', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "collective")] }

def ex_15a : Datum :=
  { id := "rakosi2020_15a"
    source := ⟨"rakosi-2020", "(15a)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A személyzet riadtan nézte egymás-t."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("riadtan", "frightened"), ("nézte", "watch.3SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], [⟨['s', 'z', 'e', 'm', 'é', 'l', 'y', 'z', 'e', 't'], ['s', 't', 'a', 'f', 'f'], none⟩]⟩, ⟨['r', 'i', 'a', 'd', 't', 'a', 'n'], ['f', 'r', 'i', 'g', 'h', 't', 'e', 'n', 'e', 'd'], [⟨['r', 'i', 'a', 'd', 't', 'a', 'n'], ['f', 'r', 'i', 'g', 'h', 't', 'e', 'n', 'e', 'd'], none⟩]⟩, ⟨['n', 'é', 'z', 't', 'e'], ['w', 'a', 't', 'c', 'h', '.', '3', 'S', 'G'], [⟨['n', 'é', 'z', 't', 'e'], ['w', 'a', 't', 'c', 'h', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨4, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "collective")] }

def ex_15b : Datum :=
  { id := "rakosi2020_15b"
    source := ⟨"rakosi-2020", "(15b)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A Facebookon szidta egymás-t a család."
    glossedTokens := [("A", "the"), ("Facebookon", "Facebook.on"), ("szidta", "cursed.3SG"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("család.", "family")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['F', 'a', 'c', 'e', 'b', 'o', 'o', 'k', 'o', 'n'], ['F', 'a', 'c', 'e', 'b', 'o', 'o', 'k', '.', 'o', 'n'], [⟨['F', 'a', 'c', 'e', 'b', 'o', 'o', 'k', 'o', 'n'], ['F', 'a', 'c', 'e', 'b', 'o', 'o', 'k', '.', 'o', 'n'], none⟩]⟩, ⟨['s', 'z', 'i', 'd', 't', 'a'], ['c', 'u', 'r', 's', 'e', 'd', '.', '3', 'S', 'G'], [⟨['s', 'z', 'i', 'd', 't', 'a'], ['c', 'u', 'r', 's', 'e', 'd', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['a'], ['t', 'h', 'e'], [⟨['a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 's', 'a', 'l', 'á', 'd', '.'], ['f', 'a', 'm', 'i', 'l', 'y'], [⟨['c', 's', 'a', 'l', 'á', 'd'], ['f', 'a', 'm', 'i', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "collective")] }

def ex_15c : Datum :=
  { id := "rakosi2020_15c"
    source := ⟨"rakosi-2020", "(15c)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A pár az interneten találta meg egymás-t."
    glossedTokens := [("A", "the"), ("pár", "couple"), ("az", "the"), ("interneten", "internet.on"), ("találta", "found.3SG"), ("meg", "PRT"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['A'], ['t', 'h', 'e'], [⟨['A'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'á', 'r'], ['c', 'o', 'u', 'p', 'l', 'e'], [⟨['p', 'á', 'r'], ['c', 'o', 'u', 'p', 'l', 'e'], none⟩]⟩, ⟨['a', 'z'], ['t', 'h', 'e'], [⟨['a', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 'n', 't', 'e', 'r', 'n', 'e', 't', 'e', 'n'], ['i', 'n', 't', 'e', 'r', 'n', 'e', 't', '.', 'o', 'n'], [⟨['i', 'n', 't', 'e', 'r', 'n', 'e', 't', 'e', 'n'], ['i', 'n', 't', 'e', 'r', 'n', 'e', 't', '.', 'o', 'n'], none⟩]⟩, ⟨['t', 'a', 'l', 'á', 'l', 't', 'a'], ['f', 'o', 'u', 'n', 'd', '.', '3', 'S', 'G'], [⟨['t', 'a', 'l', 'á', 'l', 't', 'a'], ['f', 'o', 'u', 'n', 'd', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'e', 'g'], ['P', 'R', 'T'], [⟨['m', 'e', 'g'], ['P', 'R', 'T'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "collective")] }

def ex_16 : Datum :=
  { id := "rakosi2020_16"
    source := ⟨"rakosi-2020", "(16)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az egész család jól érezte magá-t."
    glossedTokens := [("Az", "the"), ("egész", "whole"), ("család", "family"), ("jól", "well"), ("érezte", "felt.3SG"), ("magá-t.", "itself-ACC")]
    glossedWords := [⟨['A', 'z'], ['t', 'h', 'e'], [⟨['A', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'g', 'é', 's', 'z'], ['w', 'h', 'o', 'l', 'e'], [⟨['e', 'g', 'é', 's', 'z'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['c', 's', 'a', 'l', 'á', 'd'], ['f', 'a', 'm', 'i', 'l', 'y'], [⟨['c', 's', 'a', 'l', 'á', 'd'], ['f', 'a', 'm', 'i', 'l', 'y'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], [⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'á', '-', 't', '.'], ['i', 't', 's', 'e', 'l', 'f', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'á'], ['i', 't', 's', 'e', 'l', 'f'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "maga"⟩]
    paperFeatures := [("antecedent", "collective")] }

def ex_16_ : Datum :=
  { id := "rakosi2020_16_"
    source := ⟨"rakosi-2020", "(16')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az egész család jól érezte maguk-at."
    glossedTokens := [("Az", "the"), ("egész", "whole"), ("család", "family"), ("jól", "well"), ("érezte", "felt.3SG"), ("maguk-at.", "themselves-ACC")]
    glossedWords := [⟨['A', 'z'], ['t', 'h', 'e'], [⟨['A', 'z'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'g', 'é', 's', 'z'], ['w', 'h', 'o', 'l', 'e'], [⟨['e', 'g', 'é', 's', 'z'], ['w', 'h', 'o', 'l', 'e'], none⟩]⟩, ⟨['c', 's', 'a', 'l', 'á', 'd'], ['f', 'a', 'm', 'i', 'l', 'y'], [⟨['c', 's', 'a', 'l', 'á', 'd'], ['f', 'a', 'm', 'i', 'l', 'y'], none⟩]⟩, ⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], [⟨['j', 'ó', 'l'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], [⟨['é', 'r', 'e', 'z', 't', 'e'], ['f', 'e', 'l', 't', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['m', 'a', 'g', 'u', 'k', '-', 'a', 't', '.'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'g', 'u', 'k'], ['t', 'h', 'e', 'm', 's', 'e', 'l', 'v', 'e', 's'], none⟩, ⟨['a', 't'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨5, 1, "anaphor", some "maguk"⟩]
    paperFeatures := [("antecedent", "collective")] }

def ex_17 : Datum :=
  { id := "rakosi2020_17"
    source := ⟨"rakosi-2020", "(17)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Péter és Éva az-t gondolja, hogy szereti egymás-t."
    glossedTokens := [("Péter", "Péter"), ("és", "and"), ("Éva", "Éva"), ("az-t", "that-ACC"), ("gondolja,", "think.3SG"), ("hogy", "that"), ("szereti", "love.3SG"), ("egymás-t.", "each_other-ACC")]
    glossedWords := [⟨['P', 'é', 't', 'e', 'r'], ['P', 'é', 't', 'e', 'r'], [⟨['P', 'é', 't', 'e', 'r'], ['P', 'é', 't', 'e', 'r'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['a', 'z', '-', 't'], ['t', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['a', 'z'], ['t', 'h', 'a', 't'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['g', 'o', 'n', 'd', 'o', 'l', 'j', 'a', ','], ['t', 'h', 'i', 'n', 'k', '.', '3', 'S', 'G'], [⟨['g', 'o', 'n', 'd', 'o', 'l', 'j', 'a'], ['t', 'h', 'i', 'n', 'k', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['h', 'o', 'g', 'y'], ['t', 'h', 'a', 't'], [⟨['h', 'o', 'g', 'y'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'z', 'e', 'r', 'e', 't', 'i'], ['l', 'o', 'v', 'e', '.', '3', 'S', 'G'], [⟨['s', 'z', 'e', 'r', 'e', 't', 'i'], ['l', 'o', 'v', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Péter és Éva az-t gondolja, hogy ő szereti egymás-t.", .ungrammatical)]
    readings := [("broad scope", .acceptable)]
    spans := [⟨7, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "boundPro")] }

def ex_18 : Datum :=
  { id := "rakosi2020_18"
    source := ⟨"rakosi-2020", "(18)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Álmomban két macska voltam, és játszottam egymás-sal."
    glossedTokens := [("Álmomban", "dream.POSS.1SG.in"), ("két", "two"), ("macska", "cat"), ("voltam,", "was.1SG"), ("és", "and"), ("játszottam", "played.1SG"), ("egymás-sal.", "each_other-with")]
    glossedWords := [⟨['Á', 'l', 'm', 'o', 'm', 'b', 'a', 'n'], ['d', 'r', 'e', 'a', 'm', '.', 'P', 'O', 'S', 'S', '.', '1', 'S', 'G', '.', 'i', 'n'], [⟨['Á', 'l', 'm', 'o', 'm', 'b', 'a', 'n'], ['d', 'r', 'e', 'a', 'm', '.', 'P', 'O', 'S', 'S', '.', '1', 'S', 'G', '.', 'i', 'n'], none⟩]⟩, ⟨['k', 'é', 't'], ['t', 'w', 'o'], [⟨['k', 'é', 't'], ['t', 'w', 'o'], none⟩]⟩, ⟨['m', 'a', 'c', 's', 'k', 'a'], ['c', 'a', 't'], [⟨['m', 'a', 'c', 's', 'k', 'a'], ['c', 'a', 't'], none⟩]⟩, ⟨['v', 'o', 'l', 't', 'a', 'm', ','], ['w', 'a', 's', '.', '1', 'S', 'G'], [⟨['v', 'o', 'l', 't', 'a', 'm'], ['w', 'a', 's', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['j', 'á', 't', 's', 'z', 'o', 't', 't', 'a', 'm'], ['p', 'l', 'a', 'y', 'e', 'd', '.', '1', 'S', 'G'], [⟨['j', 'á', 't', 's', 'z', 'o', 't', 't', 'a', 'm'], ['p', 'l', 'a', 'y', 'e', 'd', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 's', 'a', 'l', '.'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r', '-', 'w', 'i', 't', 'h'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['e', 'a', 'c', 'h', '_', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['s', 'a', 'l'], ['w', 'i', 't', 'h'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Álmomban két macska voltam, és én játszottam egymás-sal.", .ungrammatical)]
    readings := []
    spans := [⟨6, 1, "anaphor", some "egymas"⟩]
    paperFeatures := [("antecedent", "boundPro")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6, ex_7a, ex_7a_, ex_7b, ex_7b_, ex_8a, ex_8a_, ex_8b, ex_8b_, ex_9a, ex_9b, ex_9c, ex_9d, ex_10, ex_10_, ex_11a, ex_11a_, ex_11b, ex_11b_, ex_12, ex_12_, ex_13, ex_14, ex_14_, ex_15a, ex_15b, ex_15c, ex_16, ex_16_, ex_17, ex_18]

/-- The subject antecedents the paper compares. -/
inductive Antecedent where
  /-- atomic: a singular noun phrase denoting one individual -/
  | atomic
  /-- plural: a plural noun phrase -/
  | plural
  /-- inclusive: a singular subject included in the reference of a plural reflexive (§2) -/
  | inclusive
  /-- quantified: a quantified noun phrase, whose noun head is singular (§3) -/
  | quantified
  /-- coordinate: two conjoined singular noun phrases (§4) -/
  | coordinate
  /-- collective: a singular collective noun (§5) -/
  | collective
  /-- boundPro: a singular null pronoun bound by a plural in a higher clause (§6) -/
  | boundPro
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `antecedent`. -/
def antecedent (e : Datum) : Option Antecedent :=
  e.parse? "antecedent" [("atomic", .atomic), ("plural", .plural), ("inclusive", .inclusive),
    ("quantified", .quantified), ("coordinate", .coordinate), ("collective", .collective),
    ("boundPro", .boundPro)]

/-- The readings the paper tests an anaphor for. -/
inductive Reading where
  /-- referential: the anaphor refers, as a pronoun does -/
  | referential
  /-- bound variable: the anaphor is a variable bound by its antecedent -/
  | boundVariable
  /-- broad scope: the reciprocal takes scope over the matrix verb -/
  | broadScope
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .referential => "referential"
  | .boundVariable => "bound variable"
  | .broadScope => "broad scope"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- anaphor: the reflexive or reciprocal anaphor under test -/
  | anaphor
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("anaphor", .anaphor)]

/-- The anaphors under test. -/
inductive Lexeme where
  /-- egymas: the reciprocal egymás 'each other' -/
  | egymas
  /-- maga: the third person singular reflexive maga -/
  | maga
  /-- maguk: the third person plural reflexive maguk -/
  | maguk
  /-- magunk: the first person plural reflexive magunk -/
  | magunk
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("egymas", .egymas), ("maga", .maga), ("maguk", .maguk), ("magunk", .magunk)])

end Rakosi2020.Examples
