module

public import Linglib.Data.Examples.Schema

/-!
# `Krifka2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka2026.Examples`.
-/

@[expose] public section

namespace Krifka2026.Examples

def ex3a : Datum :=
  { id := "krifka2026_ex3a"
    source := ⟨"krifka-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John killed a spider because they are ugly."
    glossedTokens := []
    context := "Kind anaphora to an object-referring antecedent, with a number mismatch between the singular antecedent and the plural anaphor."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "count"), ("anaphor", "they")] }

def ex3b : Datum :=
  { id := "krifka2026_ex3b"
    source := ⟨"krifka-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drank some milk even though he is allergic to it."
    glossedTokens := []
    context := "Kind anaphora to a mass antecedent."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "mass"), ("anaphor", "it")] }

def ex5a : Datum :=
  { id := "krifka2026_ex5a"
    source := ⟨"krifka-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't own a dog. He is afraid of them. But Mary owns one."
    glossedTokens := []
    context := "Kind anaphora and one-anaphora reach a concept introduced under negation."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "they")] }

def ex5b : Datum :=
  { id := "krifka2026_ex5b"
    source := ⟨"krifka-2026", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't buy any milk. She cannot digest it. But John bought some."
    glossedTokens := []
    context := "Kind anaphora and some-anaphora reach a mass concept introduced under negation."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "mass"), ("island", "negation"), ("anaphor", "it")] }

def ex5c : Datum :=
  { id := "krifka2026_ex5c"
    source := ⟨"krifka-2026", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't own a dog. It is friendly."
    glossedTokens := []
    context := "An entity pronoun cannot reach a referent introduced under negation."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "entityPronoun")] }

def ex7a : Datum :=
  { id := "krifka2026_ex7a"
    source := ⟨"krifka-2026", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John noticed a spider in the bathroom. He has a phobia against them."
    glossedTokens := []
    context := "A count antecedent, singular or plural, requires the plural kind anaphor."
    judgment := .acceptable
    contrasts := [("He has a phobia against it.", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "count"), ("anaphor", "they")] }

def ex7b : Datum :=
  { id := "krifka2026_ex7b"
    source := ⟨"krifka-2026", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John noticed mold in the bathroom. He is allergic against it."
    glossedTokens := []
    context := "A mass antecedent requires the singular kind anaphor."
    judgment := .acceptable
    contrasts := [("He is allergic against them.", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "mass"), ("anaphor", "it")] }

def ex8a : Datum :=
  { id := "krifka2026_ex8a"
    source := ⟨"krifka-2026", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a lot of pollen in the air. I am allergic against it."
    glossedTokens := []
    context := "The same individuals under a mass noun take the singular kind anaphor."
    judgment := .acceptable
    contrasts := [("I am allergic against them.", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "mass"), ("anaphor", "it")] }

def ex8b : Datum :=
  { id := "krifka2026_ex8b"
    source := ⟨"krifka-2026", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are a lot of pollen grains in the air. I am allergic against them."
    glossedTokens := []
    context := "The same individuals under a count noun take the plural kind anaphor."
    judgment := .acceptable
    contrasts := [("I am allergic against it.", .questionable)]
    readings := []
    paperFeatures := [("antecedent", "count"), ("anaphor", "they")] }

def ex19a : Datum :=
  { id := "krifka2026_ex19a"
    source := ⟨"krifka-2026", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't get a dog from the animal shelter downtown. He is afraid of them."
    glossedTokens := []
    context := "Kind anaphora: John is afraid of dogs, since dogs from the shelter downtown do not form a kind."
    judgment := .acceptable
    contrasts := []
    readings := [("afraid of dogs", .acceptable)]
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "they")] }

def ex19b : Datum :=
  { id := "krifka2026_ex19b"
    source := ⟨"krifka-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't get a dog from the animal shelter downtown. But Mary got one."
    glossedTokens := []
    context := "Concept anaphora: Mary got a dog from the shelter downtown, the full property of the antecedent."
    judgment := .acceptable
    contrasts := []
    readings := [("a dog from the shelter downtown", .acceptable)]
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "one")] }

def all : List Datum := [ex3a, ex3b, ex5a, ex5b, ex5c, ex7a, ex7b, ex8a, ex8b, ex19a, ex19b]

end Krifka2026.Examples
