module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Knick2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Knick2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Knick2026.Examples`.
-/

@[expose] public section

namespace Knick2026.Examples

def ex_7a : Datum :=
  { id := "knick2026_7a"
    source := ⟨"knick-2026", "(7a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Tselmeg odoo shüleg unsh-ina."
    glossedTokens := [("Tselmeg", "Tselmeg"), ("odoo", "now"), ("shüleg", "poem"), ("unsh-ina", "read-nA")]
    glossedWords := [⟨['T', 's', 'e', 'l', 'm', 'e', 'g'], ['T', 's', 'e', 'l', 'm', 'e', 'g'], [⟨['T', 's', 'e', 'l', 'm', 'e', 'g'], ['T', 's', 'e', 'l', 'm', 'e', 'g'], none⟩]⟩, ⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], [⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], none⟩]⟩, ⟨['s', 'h', 'ü', 'l', 'e', 'g'], ['p', 'o', 'e', 'm'], [⟨['s', 'h', 'ü', 'l', 'e', 'g'], ['p', 'o', 'e', 'm'], none⟩]⟩, ⟨['u', 'n', 's', 'h', '-', 'i', 'n', 'a'], ['r', 'e', 'a', 'd', '-', 'n', 'A'], [⟨['u', 'n', 's', 'h'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i', 'n', 'a'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "eventive"), ("adverbial", "now")] }

def ex_7b : Datum :=
  { id := "knick2026_7b"
    source := ⟨"knick-2026", "(7b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Tselmeg margaash shüleg unsh-ina."
    glossedTokens := [("Tselmeg", "Tselmeg"), ("margaash", "tomorrow"), ("shüleg", "poem"), ("unsh-ina", "read-nA")]
    glossedWords := [⟨['T', 's', 'e', 'l', 'm', 'e', 'g'], ['T', 's', 'e', 'l', 'm', 'e', 'g'], [⟨['T', 's', 'e', 'l', 'm', 'e', 'g'], ['T', 's', 'e', 'l', 'm', 'e', 'g'], none⟩]⟩, ⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['s', 'h', 'ü', 'l', 'e', 'g'], ['p', 'o', 'e', 'm'], [⟨['s', 'h', 'ü', 'l', 'e', 'g'], ['p', 'o', 'e', 'm'], none⟩]⟩, ⟨['u', 'n', 's', 'h', '-', 'i', 'n', 'a'], ['r', 'e', 'a', 'd', '-', 'n', 'A'], [⟨['u', 'n', 's', 'h'], ['r', 'e', 'a', 'd'], none⟩, ⟨['i', 'n', 'a'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "eventive"), ("adverbial", "tomorrow")] }

def ex_7c : Datum :=
  { id := "knick2026_7c"
    source := ⟨"knick-2026", "(7c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Suvdmaa odoo büjigle-ne."
    glossedTokens := [("Suvdmaa", "Suvdmaa"), ("odoo", "now"), ("büjigle-ne", "dance-nA")]
    glossedWords := [⟨['S', 'u', 'v', 'd', 'm', 'a', 'a'], ['S', 'u', 'v', 'd', 'm', 'a', 'a'], [⟨['S', 'u', 'v', 'd', 'm', 'a', 'a'], ['S', 'u', 'v', 'd', 'm', 'a', 'a'], none⟩]⟩, ⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], [⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], none⟩]⟩, ⟨['b', 'ü', 'j', 'i', 'g', 'l', 'e', '-', 'n', 'e'], ['d', 'a', 'n', 'c', 'e', '-', 'n', 'A'], [⟨['b', 'ü', 'j', 'i', 'g', 'l', 'e'], ['d', 'a', 'n', 'c', 'e'], none⟩, ⟨['n', 'e'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "eventive"), ("adverbial", "now")] }

def ex_7d : Datum :=
  { id := "knick2026_7d"
    source := ⟨"knick-2026", "(7d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Suvdmaa margaash büjigle-ne."
    glossedTokens := [("Suvdmaa", "Suvdmaa"), ("margaash", "tomorrow"), ("büjigle-ne", "dance-nA")]
    glossedWords := [⟨['S', 'u', 'v', 'd', 'm', 'a', 'a'], ['S', 'u', 'v', 'd', 'm', 'a', 'a'], [⟨['S', 'u', 'v', 'd', 'm', 'a', 'a'], ['S', 'u', 'v', 'd', 'm', 'a', 'a'], none⟩]⟩, ⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['b', 'ü', 'j', 'i', 'g', 'l', 'e', '-', 'n', 'e'], ['d', 'a', 'n', 'c', 'e', '-', 'n', 'A'], [⟨['b', 'ü', 'j', 'i', 'g', 'l', 'e'], ['d', 'a', 'n', 'c', 'e'], none⟩, ⟨['n', 'e'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "eventive"), ("adverbial", "tomorrow")] }

def ex_8a : Datum :=
  { id := "knick2026_8a"
    source := ⟨"knick-2026", "(8a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Bat odoo minii nuuts-iig med-ne."
    glossedTokens := [("Bat", "Bat"), ("odoo", "now"), ("minii", "1SG.POSS"), ("nuuts-iig", "secret-ACC"), ("med-ne", "know-nA")]
    glossedWords := [⟨['B', 'a', 't'], ['B', 'a', 't'], [⟨['B', 'a', 't'], ['B', 'a', 't'], none⟩]⟩, ⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], [⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], none⟩]⟩, ⟨['m', 'i', 'n', 'i', 'i'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], [⟨['m', 'i', 'n', 'i', 'i'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], none⟩]⟩, ⟨['n', 'u', 'u', 't', 's', '-', 'i', 'i', 'g'], ['s', 'e', 'c', 'r', 'e', 't', '-', 'A', 'C', 'C'], [⟨['n', 'u', 'u', 't', 's'], ['s', 'e', 'c', 'r', 'e', 't'], none⟩, ⟨['i', 'i', 'g'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'e', 'd', '-', 'n', 'e'], ['k', 'n', 'o', 'w', '-', 'n', 'A'], [⟨['m', 'e', 'd'], ['k', 'n', 'o', 'w'], none⟩, ⟨['n', 'e'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "stative"), ("adverbial", "now")] }

def ex_8b : Datum :=
  { id := "knick2026_8b"
    source := ⟨"knick-2026", "(8b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Bat margaash minii nuuts-iig med-ne."
    glossedTokens := [("Bat", "Bat"), ("margaash", "tomorrow"), ("minii", "1SG.POSS"), ("nuuts-iig", "secret-ACC"), ("med-ne", "know-nA")]
    glossedWords := [⟨['B', 'a', 't'], ['B', 'a', 't'], [⟨['B', 'a', 't'], ['B', 'a', 't'], none⟩]⟩, ⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['m', 'i', 'n', 'i', 'i'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], [⟨['m', 'i', 'n', 'i', 'i'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S'], none⟩]⟩, ⟨['n', 'u', 'u', 't', 's', '-', 'i', 'i', 'g'], ['s', 'e', 'c', 'r', 'e', 't', '-', 'A', 'C', 'C'], [⟨['n', 'u', 'u', 't', 's'], ['s', 'e', 'c', 'r', 'e', 't'], none⟩, ⟨['i', 'i', 'g'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'e', 'd', '-', 'n', 'e'], ['k', 'n', 'o', 'w', '-', 'n', 'A'], [⟨['m', 'e', 'd'], ['k', 'n', 'o', 'w'], none⟩, ⟨['n', 'e'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "stative"), ("adverbial", "tomorrow")] }

def ex_8c : Datum :=
  { id := "knick2026_8c"
    source := ⟨"knick-2026", "(8c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Khöshöö odoo uul-in oroi-d bairla-na."
    glossedTokens := [("Khöshöö", "statue"), ("odoo", "now"), ("uul-in", "mountain-GEN"), ("oroi-d", "top-DAT"), ("bairla-na", "be.placed-nA")]
    glossedWords := [⟨['K', 'h', 'ö', 's', 'h', 'ö', 'ö'], ['s', 't', 'a', 't', 'u', 'e'], [⟨['K', 'h', 'ö', 's', 'h', 'ö', 'ö'], ['s', 't', 'a', 't', 'u', 'e'], none⟩]⟩, ⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], [⟨['o', 'd', 'o', 'o'], ['n', 'o', 'w'], none⟩]⟩, ⟨['u', 'u', 'l', '-', 'i', 'n'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n', '-', 'G', 'E', 'N'], [⟨['u', 'u', 'l'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['o', 'r', 'o', 'i', '-', 'd'], ['t', 'o', 'p', '-', 'D', 'A', 'T'], [⟨['o', 'r', 'o', 'i'], ['t', 'o', 'p'], none⟩, ⟨['d'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'a', 'i', 'r', 'l', 'a', '-', 'n', 'a'], ['b', 'e', '.', 'p', 'l', 'a', 'c', 'e', 'd', '-', 'n', 'A'], [⟨['b', 'a', 'i', 'r', 'l', 'a'], ['b', 'e', '.', 'p', 'l', 'a', 'c', 'e', 'd'], none⟩, ⟨['n', 'a'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "stative"), ("adverbial", "now")] }

def ex_8d : Datum :=
  { id := "knick2026_8d"
    source := ⟨"knick-2026", "(8d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "halh1238"
    primaryText := "Khöshöö margaash uul-in oroi-d bairla-na."
    glossedTokens := [("Khöshöö", "statue"), ("margaash", "tomorrow"), ("uul-in", "mountain-GEN"), ("oroi-d", "top-DAT"), ("bairla-na", "be.placed-nA")]
    glossedWords := [⟨['K', 'h', 'ö', 's', 'h', 'ö', 'ö'], ['s', 't', 'a', 't', 'u', 'e'], [⟨['K', 'h', 'ö', 's', 'h', 'ö', 'ö'], ['s', 't', 'a', 't', 'u', 'e'], none⟩]⟩, ⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'a', 'r', 'g', 'a', 'a', 's', 'h'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['u', 'u', 'l', '-', 'i', 'n'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n', '-', 'G', 'E', 'N'], [⟨['u', 'u', 'l'], ['m', 'o', 'u', 'n', 't', 'a', 'i', 'n'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['o', 'r', 'o', 'i', '-', 'd'], ['t', 'o', 'p', '-', 'D', 'A', 'T'], [⟨['o', 'r', 'o', 'i'], ['t', 'o', 'p'], none⟩, ⟨['d'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['b', 'a', 'i', 'r', 'l', 'a', '-', 'n', 'a'], ['b', 'e', '.', 'p', 'l', 'a', 'c', 'e', 'd', '-', 'n', 'A'], [⟨['b', 'a', 'i', 'r', 'l', 'a'], ['b', 'e', '.', 'p', 'l', 'a', 'c', 'e', 'd'], none⟩, ⟨['n', 'a'], ['n', 'A'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aktionsart", "stative"), ("adverbial", "tomorrow")] }

def all : List Datum := [ex_7a, ex_7b, ex_7c, ex_7d, ex_8a, ex_8b, ex_8c, ex_8d]

/-- The aspectual class of the predicate. -/
inductive Aktionsart where
  /-- eventive: an eventive predicate -/
  | eventive
  /-- stative: a stative predicate -/
  | stative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `aktionsart`. -/
def aktionsart (e : Datum) : Option Aktionsart :=
  e.parse? "aktionsart" [("eventive", .eventive), ("stative", .stative)]

/-- The temporal adverbial of the sentence. -/
inductive Adverbial where
  /-- now: *odoo* 'now' -/
  | now
  /-- tomorrow: *margaash* 'tomorrow' -/
  | tomorrow
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `adverbial`. -/
def adverbial (e : Datum) : Option Adverbial :=
  e.parse? "adverbial" [("now", .now), ("tomorrow", .tomorrow)]

end Knick2026.Examples
