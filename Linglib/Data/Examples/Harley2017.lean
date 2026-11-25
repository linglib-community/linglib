module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Harley2017` — typed example data

Auto-generated from `Linglib/Data/Examples/Harley2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Harley2017.Examples`.
-/

@[expose] public section

namespace Harley2017.Examples

def ex_47a : Datum :=
  { id := "harley2017_47a"
    source := ⟨"harley-2017", "(47a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Mario Alle-ta uka karo-ta wee-tua-ria-k."
    glossedTokens := [("Mario", "Mario"), ("Alle-ta", "Alex-ACC"), ("uka", "that"), ("karo-ta", "car-ACC"), ("wee-tua-ria-k", "go-CAUS-APPL-PRF")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], none⟩]⟩, ⟨['A', 'l', 'l', 'e', '-', 't', 'a'], ['A', 'l', 'e', 'x', '-', 'A', 'C', 'C'], [⟨['A', 'l', 'l', 'e'], ['A', 'l', 'e', 'x'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['u', 'k', 'a'], ['t', 'h', 'a', 't'], [⟨['u', 'k', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'a', 'r', 'o', '-', 't', 'a'], ['c', 'a', 'r', '-', 'A', 'C', 'C'], [⟨['k', 'a', 'r', 'o'], ['c', 'a', 'r'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['w', 'e', 'e', '-', 't', 'u', 'a', '-', 'r', 'i', 'a', '-', 'k'], ['g', 'o', '-', 'C', 'A', 'U', 'S', '-', 'A', 'P', 'P', 'L', '-', 'P', 'R', 'F'], [⟨['w', 'e', 'e'], ['g', 'o'], none⟩, ⟨['t', 'u', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['r', 'i', 'a'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['k'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.4.3"), ("base", "unaccusative")] }

def ex_47b : Datum :=
  { id := "harley2017_47b"
    source := ⟨"harley-2017", "(47b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Mario usi-ta uka vakot-ta sim-tua-ria-k."
    glossedTokens := [("Mario", "Mario"), ("usi-ta", "child-ACC"), ("uka", "the"), ("vakot-ta", "snake-ACC"), ("sim-tua-ria-k", "leave-CAUS-APPL-PRF")]
    glossedWords := [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], none⟩]⟩, ⟨['u', 's', 'i', '-', 't', 'a'], ['c', 'h', 'i', 'l', 'd', '-', 'A', 'C', 'C'], [⟨['u', 's', 'i'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['u', 'k', 'a'], ['t', 'h', 'e'], [⟨['u', 'k', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'a', 'k', 'o', 't', '-', 't', 'a'], ['s', 'n', 'a', 'k', 'e', '-', 'A', 'C', 'C'], [⟨['v', 'a', 'k', 'o', 't'], ['s', 'n', 'a', 'k', 'e'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'i', 'm', '-', 't', 'u', 'a', '-', 'r', 'i', 'a', '-', 'k'], ['l', 'e', 'a', 'v', 'e', '-', 'C', 'A', 'U', 'S', '-', 'A', 'P', 'P', 'L', '-', 'P', 'R', 'F'], [⟨['s', 'i', 'm'], ['l', 'e', 'a', 'v', 'e'], none⟩, ⟨['t', 'u', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['r', 'i', 'a'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['k'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.4.3"), ("base", "unaccusative")] }

def ex_48a : Datum :=
  { id := "harley2017_48a"
    source := ⟨"harley-2017", "(48a)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Jose Maria-ta uka kavai-ta chepti-tua-ria-k."
    glossedTokens := [("Jose", "Jose"), ("Maria-ta", "Maria-ACC"), ("uka", "that"), ("kavai-ta", "horse-ACC"), ("chepti-tua-ria-k", "jump-CAUS-APPL-PRF")]
    glossedWords := [⟨['J', 'o', 's', 'e'], ['J', 'o', 's', 'e'], [⟨['J', 'o', 's', 'e'], ['J', 'o', 's', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 't', 'a'], ['M', 'a', 'r', 'i', 'a', '-', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['u', 'k', 'a'], ['t', 'h', 'a', 't'], [⟨['u', 'k', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'a', 'v', 'a', 'i', '-', 't', 'a'], ['h', 'o', 'r', 's', 'e', '-', 'A', 'C', 'C'], [⟨['k', 'a', 'v', 'a', 'i'], ['h', 'o', 'r', 's', 'e'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['c', 'h', 'e', 'p', 't', 'i', '-', 't', 'u', 'a', '-', 'r', 'i', 'a', '-', 'k'], ['j', 'u', 'm', 'p', '-', 'C', 'A', 'U', 'S', '-', 'A', 'P', 'P', 'L', '-', 'P', 'R', 'F'], [⟨['c', 'h', 'e', 'p', 't', 'i'], ['j', 'u', 'm', 'p'], none⟩, ⟨['t', 'u', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['r', 'i', 'a'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['k'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.4.3"), ("base", "unergative")] }

def ex_48b : Datum :=
  { id := "harley2017_48b"
    source := ⟨"harley-2017", "(48b)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Nee mala-ta Mario-ta yi'i-tua-ria-k."
    glossedTokens := [("Nee", "I"), ("mala-ta", "mother-ACC"), ("Mario-ta", "Mario-ACC"), ("yi'i-tua-ria-k", "dance-CAUS-APPL-PRF")]
    glossedWords := [⟨['N', 'e', 'e'], ['I'], [⟨['N', 'e', 'e'], ['I'], none⟩]⟩, ⟨['m', 'a', 'l', 'a', '-', 't', 'a'], ['m', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['m', 'a', 'l', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'i', 'o', '-', 't', 'a'], ['M', 'a', 'r', 'i', 'o', '-', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'i', 'o'], ['M', 'a', 'r', 'i', 'o'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['y', 'i', '\'', 'i', '-', 't', 'u', 'a', '-', 'r', 'i', 'a', '-', 'k'], ['d', 'a', 'n', 'c', 'e', '-', 'C', 'A', 'U', 'S', '-', 'A', 'P', 'P', 'L', '-', 'P', 'R', 'F'], [⟨['y', 'i', '\'', 'i'], ['d', 'a', 'n', 'c', 'e'], none⟩, ⟨['t', 'u', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['r', 'i', 'a'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['k'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.4.3"), ("base", "unergative")] }

def ex_48c : Datum :=
  { id := "harley2017_48c"
    source := ⟨"harley-2017", "(48c)"⟩
    reportedIn := none
    language := "yaqu1251"
    primaryText := "Jose yoemia-ta uka hamut-ta nok-tua-ria-k."
    glossedTokens := [("Jose", "Jose"), ("yoemia-ta", "people-ACC"), ("uka", "the"), ("hamut-ta", "woman-ACC"), ("nok-tua-ria-k", "speak-CAUS-APPL-PRF")]
    glossedWords := [⟨['J', 'o', 's', 'e'], ['J', 'o', 's', 'e'], [⟨['J', 'o', 's', 'e'], ['J', 'o', 's', 'e'], none⟩]⟩, ⟨['y', 'o', 'e', 'm', 'i', 'a', '-', 't', 'a'], ['p', 'e', 'o', 'p', 'l', 'e', '-', 'A', 'C', 'C'], [⟨['y', 'o', 'e', 'm', 'i', 'a'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['u', 'k', 'a'], ['t', 'h', 'e'], [⟨['u', 'k', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['h', 'a', 'm', 'u', 't', '-', 't', 'a'], ['w', 'o', 'm', 'a', 'n', '-', 'A', 'C', 'C'], [⟨['h', 'a', 'm', 'u', 't'], ['w', 'o', 'm', 'a', 'n'], none⟩, ⟨['t', 'a'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['n', 'o', 'k', '-', 't', 'u', 'a', '-', 'r', 'i', 'a', '-', 'k'], ['s', 'p', 'e', 'a', 'k', '-', 'C', 'A', 'U', 'S', '-', 'A', 'P', 'P', 'L', '-', 'P', 'R', 'F'], [⟨['n', 'o', 'k'], ['s', 'p', 'e', 'a', 'k'], none⟩, ⟨['t', 'u', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['r', 'i', 'a'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['k'], ['P', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.4.3"), ("base", "unergative")] }

def all : List Datum := [ex_47a, ex_47b, ex_48a, ex_48b, ex_48c]

/-- The class of the verb a causative is built on, as the paper heads its examples. -/
inductive Base where
  /-- unaccusative: an unaccusative verb -/
  | unaccusative
  /-- unergative: an unergative verb -/
  | unergative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `base`. -/
def base (e : Datum) : Option Base :=
  e.parse? "base" [("unaccusative", .unaccusative), ("unergative", .unergative)]

end Harley2017.Examples
