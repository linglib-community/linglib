module

public import Linglib.Data.Examples.Schema

/-!
# `AckemaNeeleman2018` — typed example data

Auto-generated from `Linglib/Data/Examples/AckemaNeeleman2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AckemaNeeleman2018.Examples`.
-/

@[expose] public section

namespace AckemaNeeleman2018.Examples

def ex_2a : Datum :=
  { id := "ackemaneeleman2018_2a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Mary has left for Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")] }

def ex_2b : Datum :=
  { id := "ackemaneeleman2018_2b"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is raining again in Edinburgh."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")] }

def ex_20a : Datum :=
  { id := "ackemaneeleman2018_20a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck!"
    glossedTokens := []
    context := "John discovers he has a winning lottery ticket and talks to himself."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk"), ("roles", "i and u co-incide")] }

def ex_21a : Datum :=
  { id := "ackemaneeleman2018_21a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck! If we hurry, we can still collect the money today."
    glossedTokens := []
    context := "John discovers he has a winning lottery ticket and talks to himself."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk"), ("person", "first plural")] }

def ex_24a : Datum :=
  { id := "ackemaneeleman2018_24a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Vitesse won."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("It seem that Vitesse won.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")] }

def ex_24b_i : Datum :=
  { id := "ackemaneeleman2018_24b_i"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I seem that Vitesse won."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "first")] }

def ex_24b_you : Datum :=
  { id := "ackemaneeleman2018_24b_you"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You seem that Vitesse won."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "second")] }

def ex_25 : Datum :=
  { id := "ackemaneeleman2018_25"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren is naar een oplossing gezocht."
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("is", "be.3SG"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    glossedWords := [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], [⟨['N', 'o', 'g'], ['s', 't', 'i', 'l', 'l'], none⟩]⟩, ⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], [⟨['j', 'a', 'r', 'e', 'n'], ['y', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['i', 's'], ['b', 'e', '.', '3', 'S', 'G'], [⟨['i', 's'], ['b', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], [⟨['n', 'a', 'a', 'r'], ['f', 'o', 'r'], none⟩]⟩, ⟨['e', 'e', 'n'], ['a'], [⟨['e', 'e', 'n'], ['a'], none⟩]⟩, ⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], [⟨['o', 'p', 'l', 'o', 's', 's', 'i', 'n', 'g'], ['s', 'o', 'l', 'u', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], [⟨['g', 'e', 'z', 'o', 'c', 'h', 't'], ['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Nog jaren ben naar een oplossing gezocht.", .ungrammatical), ("Nog jaren bent naar een oplossing gezocht.", .ungrammatical), ("Nog jaren zijn naar een oplossing gezocht.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "default agreement"), ("construction", "impersonal passive")] }

def ex_30 : Datum :=
  { id := "ackemaneeleman2018_30"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (30)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Men schijnt dat men regent."
    glossedTokens := [("Men", "one"), ("schijnt", "seems"), ("dat", "that"), ("men", "one"), ("regent", "rains")]
    glossedWords := [⟨['M', 'e', 'n'], ['o', 'n', 'e'], [⟨['M', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['s', 'c', 'h', 'i', 'j', 'n', 't'], ['s', 'e', 'e', 'm', 's'], [⟨['s', 'c', 'h', 'i', 'j', 'n', 't'], ['s', 'e', 'e', 'm', 's'], none⟩]⟩, ⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 't'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'e', 'n'], ['o', 'n', 'e'], [⟨['m', 'e', 'n'], ['o', 'n', 'e'], none⟩]⟩, ⟨['r', 'e', 'g', 'e', 'n', 't'], ['r', 'a', 'i', 'n', 's'], [⟨['r', 'e', 'g', 'e', 'n', 't'], ['r', 'a', 'i', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "featureless")] }

def all : List Datum := [ex_2a, ex_2b, ex_20a, ex_21a, ex_24a, ex_24b_i, ex_24b_you, ex_25, ex_30]

end AckemaNeeleman2018.Examples
