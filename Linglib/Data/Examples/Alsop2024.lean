module

public import Linglib.Data.Examples.Schema

/-!
# `Alsop2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Alsop2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Alsop2024.Examples`.
-/

@[expose] public section

namespace Alsop2024.Examples

def ex_1a : Datum :=
  { id := "alsop2024_1a"
    source := ⟨"alsop-2024", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may read any book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .acceptable)]
    paperFeatures := [("logicalForm", "∀x ∈ De [book(x) → ◇read(you,x)]")] }

def ex_3 : Datum :=
  { id := "alsop2024_3"
    source := ⟨"szabolcsi-2019", ""⟩
    reportedIn := some ⟨"alsop-2024", "(3)"⟩
    language := "stan1293"
    primaryText := "Any bishop may meet a bishop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")] }

def ex_5a : Datum :=
  { id := "alsop2024_5a"
    source := ⟨"alsop-2024", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane didn't buy any shirts."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("any", "npi"), ("environment", "negation")] }

def ex_5b : Datum :=
  { id := "alsop2024_5b"
    source := ⟨"alsop-2024", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom thanked every guest who brought any drinks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("any", "npi"), ("environment", "restrictorOfEvery")] }

def ex_6a : Datum :=
  { id := "alsop2024_6a"
    source := ⟨"alsop-2024", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carrie read any book."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("any", "fci"), ("environment", "episodic")] }

def ex_6b : Datum :=
  { id := "alsop2024_6b"
    source := ⟨"alsop-2024", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carrie may read any book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("any", "fci"), ("environment", "possibilityModal")] }

def ex_6c : Datum :=
  { id := "alsop2024_6c"
    source := ⟨"alsop-2024", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carrie must read any book."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("any", "fci"), ("environment", "necessityModal")] }

def ex_17 : Datum :=
  { id := "alsop2024_17"
    source := ⟨"menendez-benito-2010", ""⟩
    reportedIn := some ⟨"alsop-2024", "(17)"⟩
    language := "stan1293"
    primaryText := "In Canasta, you can take any of the cards in the discard pile when you have two cards that match its top card."
    glossedTokens := []
    context := "One of the rules of the card game Canasta is: When a player has two cards that match the top card of the discard pile, she has two options: (i) take all the cards in the discard pile and (ii) take no card from the discard pile (but take the top card of the regular pile instead). Those are her two only options."
    judgment := .acceptable
    contrasts := []
    readings := [("literal", .acceptable), ("exclusiveness", .unacceptable)]
    paperFeatures := [("state", "only2")] }

def ex_19 : Datum :=
  { id := "alsop2024_19"
    source := ⟨"alsop-2024", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Annie: Can I take any of these cats? Shelter employee: Technically yes…but they're siblings, so if you take one, you're required to take them all."
    glossedTokens := []
    context := "The local animal shelter has a strict policy of not separating animals from their siblings. Annie goes to the shelter to adopt a cat, and walks into one room with three cats inside."
    judgment := .acceptable
    contrasts := []
    readings := [("literal", .acceptable), ("exclusiveness", .unacceptable)]
    paperFeatures := [("state", "only2")] }

def ex_20a : Datum :=
  { id := "alsop2024_20a"
    source := ⟨"alsop-2024", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any bishop may gather with other bishops."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")] }

def ex_20b : Datum :=
  { id := "alsop2024_20b"
    source := ⟨"alsop-2024", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any bishop may converse with another bishop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")] }

def ex_20c : Datum :=
  { id := "alsop2024_20c"
    source := ⟨"alsop-2024", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any bishop may pair up with another bishop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")] }

def ex_21b : Datum :=
  { id := "alsop2024_21b"
    source := ⟨"alsop-2024", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may take any class."
    glossedTokens := []
    context := "You are a graduate student only required to take one class per semester. You ask: What classes are we allowed to take in our first year?"
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .acceptable)]
    paperFeatures := [] }

def ex_22b : Datum :=
  { id := "alsop2024_22b"
    source := ⟨"alsop-2024", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may take any class."
    glossedTokens := []
    context := "You are an undergraduate student required to take four classes per semester. You ask: What classes are we allowed to take in our first year?"
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("state", "only2")] }

def ex_23 : Datum :=
  { id := "alsop2024_23"
    source := ⟨"alsop-2024", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt any cat here… But if you adopt a cat, you also have to adopt its siblings."
    glossedTokens := []
    context := "Annie goes to the shelter to adopt a cat; the shelter employee speaks."
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("implicature", "cancelled"), ("state", "only2")] }

def ex_24a : Datum :=
  { id := "alsop2024_24a"
    source := ⟨"dayal-2013", "pp. 93–94"⟩
    reportedIn := some ⟨"alsop-2024", "(24a)"⟩
    language := "stan1293"
    primaryText := "Bill may read any of these books."
    glossedTokens := []
    context := "Out of the blue."
    judgment := .acceptable
    contrasts := []
    readings := [("not every", .questionable)]
    paperFeatures := [("prior", "uniform")] }

def ex_25b : Datum :=
  { id := "alsop2024_25b"
    source := ⟨"alsop-2024", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may take any class."
    glossedTokens := []
    context := "You are a part-time student who is forbidden from taking more than one class in a semester. Your university offers hundreds of classes each semester. You ask: What classes are we allowed to take in our first year?"
    judgment := .acceptable
    contrasts := []
    readings := [("not two", .acceptable), ("not three", .acceptable), ("not every", .acceptable)]
    paperFeatures := [("state", "only1")] }

def ex_26a : Datum :=
  { id := "alsop2024_26a"
    source := ⟨"alsop-2024", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anyone and everyone is welcome to come."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "anyAndEvery")] }

def ex_26b : Datum :=
  { id := "alsop2024_26b"
    source := ⟨"alsop-2024", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We welcome any and all questions."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "anyAndEvery")] }

def ex_27a : Datum :=
  { id := "alsop2024_27a"
    source := ⟨"alsop-2024", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We reserve the right to refuse to serve anyone."
    glossedTokens := []
    context := "A restaurant sign."
    judgment := .acceptable
    contrasts := [("We reserve the right to refuse to serve anyone and everyone.", .unacceptable)]
    readings := []
    paperFeatures := [] }

def ex_28 : Datum :=
  { id := "alsop2024_28"
    source := ⟨"alsop-2024", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have any of these souvenirs… In fact, you may even have all of them."
    glossedTokens := []
    context := "You are one of three siblings. Your mother returns from a business trip with three souvenirs and presents them to just you first."
    judgment := .acceptable
    contrasts := []
    readings := [("not every", .unacceptable)]
    paperFeatures := [("implicature", "cancelled")] }

def ex_31_mayS : Datum :=
  { id := "alsop2024_31_mayS"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take Semantics."
    glossedTokens := []
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("utterance", "mayS"), ("parses", "3")] }

def ex_31_mayP : Datum :=
  { id := "alsop2024_31_mayP"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take Phonology."
    glossedTokens := []
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("utterance", "mayP"), ("parses", "3")] }

def ex_31_mayAny : Datum :=
  { id := "alsop2024_31_mayAny"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take any class."
    glossedTokens := []
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    contrasts := []
    readings := [("exclusiveness", .acceptable), ("not every", .questionable)]
    paperFeatures := [("utterance", "mayAny"), ("parses", "2"), ("prior", "uniform")] }

def ex_31_mayEvery : Datum :=
  { id := "alsop2024_31_mayEvery"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take every class."
    glossedTokens := []
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("utterance", "mayEvery"), ("parses", "4")] }

def ex_44 : Datum :=
  { id := "alsop2024_44"
    source := ⟨"alsop-2024", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris: Can I choose any of those chores? Grandmother: Technically yes—in fact, you must do all of them."
    glossedTokens := []
    context := "This year, Chris decides to spend the summer at his grandmother's house. His first day there, his grandmother pulls him aside to discuss his responsibilities for the summer. She shows him a list of chores she has written down."
    judgment := .acceptable
    contrasts := []
    readings := [("literal", .acceptable), ("exclusiveness", .unacceptable), ("may but not must", .unacceptable)]
    paperFeatures := [("revisedViabilityConstraint", "cancelled")] }

def all : List Datum := [ex_1a, ex_3, ex_5a, ex_5b, ex_6a, ex_6b, ex_6c, ex_17, ex_19, ex_20a, ex_20b, ex_20c, ex_21b, ex_22b, ex_23, ex_24a, ex_25b, ex_26a, ex_26b, ex_27a, ex_28, ex_31_mayS, ex_31_mayP, ex_31_mayAny, ex_31_mayEvery, ex_44]

end Alsop2024.Examples
