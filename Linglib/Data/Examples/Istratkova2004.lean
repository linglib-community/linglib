module

public import Linglib.Data.Examples.Schema

/-!
# `Istratkova2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Istratkova2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Istratkova2004.Examples`.
-/

@[expose] public section

namespace Istratkova2004.Examples

def ex_10 : Datum :=
  { id := "istratkova2004_10"
    source := ⟨"istratkova-2004", "(10)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Maria jade jabəlka edin čas/*za edin čas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "a homogeneous verb heads a non-quantized VP whatever its object")] }

def ex_17a : Datum :=
  { id := "istratkova2004_17a"
    source := ⟨"istratkova-2004", "(17a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Započna da raz-proda-va."
    glossedTokens := [("Započna", "started.F.SG"), ("da", "to"), ("raz-proda-va", "raz-sell-IMPF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "raz- 'in excess' embeds under a phase verb")] }

def ex_17b : Datum :=
  { id := "istratkova2004_17b"
    source := ⟨"istratkova-2004", "(17b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Započna da iz-proda-va."
    glossedTokens := [("Započna", "started.F.SG"), ("da", "to"), ("iz-proda-va", "iz-sell-IMPF")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "iz- 'completely' is incompatible with beginning")] }

def ex_20g : Datum :=
  { id := "istratkova2004_20g"
    source := ⟨"istratkova-2004", "(20g)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Na-prodadoh cvetja(*-ta)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "na- means 'a lot', not 'all': no definite object")] }

def all : List Datum := [ex_10, ex_17a, ex_17b, ex_20g]

end Istratkova2004.Examples
