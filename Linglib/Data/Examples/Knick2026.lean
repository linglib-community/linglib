module

public import Linglib.Data.Examples.Schema

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
    context := ""
    judgment := .unacceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
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
    context := ""
    judgment := .unacceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
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
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aktionsart", "stative"), ("adverbial", "tomorrow")] }

def all : List Datum := [ex_7a, ex_7b, ex_7c, ex_7d, ex_8a, ex_8b, ex_8c, ex_8d]

end Knick2026.Examples
