module

public import Linglib.Data.Examples.Schema

/-!
# `Maier2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Maier2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Maier2015.Examples`.
-/

@[expose] public section

namespace Maier2015.Examples

def ex_42 : Datum :=
  { id := "maier2015_42"
    source := ⟨"maier-2015", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill believed that Fred had been beating his wife and he hoped that Fred would stop beating her."
    glossedTokens := []
    context := "The presupposition of stop, that Fred had been beating his wife, is filtered: it is not the speaker's."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "doxasticFirst"), ("attitudes", "believe;hope"), ("trigger", "stop")] }

def ex_7a : Datum :=
  { id := "maier2015_7a"
    source := ⟨"maier-2015", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that Mary will come. He hopes that SUE will come too."
    glossedTokens := []
    context := "The presupposition of too is filtered by the belief."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "doxasticFirst"), ("attitudes", "believe;hope"), ("trigger", "too")] }

def ex_7b : Datum :=
  { id := "maier2015_7b"
    source := ⟨"maier-2015", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John hopes that Mary will come. He believes that SUE will come too."
    glossedTokens := []
    context := "The presupposition of too finds no antecedent in the belief and projects."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("order", "parasiticFirst"), ("attitudes", "hope;believe"), ("trigger", "too")] }

def ex_22a : Datum :=
  { id := "maier2015_22a"
    source := ⟨"maier-2015", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that Mary will come to his party. Last night he imagined that HER SISTER would come too."
    glossedTokens := []
    context := "A representational attitude without a preference component is parasitic on belief in the same way."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "doxasticFirst"), ("attitudes", "believe;imagine"), ("trigger", "too")] }

def ex_22b : Datum :=
  { id := "maier2015_22b"
    source := ⟨"maier-2015", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last night John imagined that Mary would come to his party. He believes that HER SISTER will come too."
    glossedTokens := []
    context := "The reverse order does not filter."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("order", "parasiticFirst"), ("attitudes", "imagine;believe"), ("trigger", "too")] }

def all : List Datum := [ex_42, ex_7a, ex_7b, ex_22a, ex_22b]

end Maier2015.Examples
