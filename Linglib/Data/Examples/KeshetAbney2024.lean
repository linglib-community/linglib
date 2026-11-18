module

public import Linglib.Data.Examples.Schema

/-!
# `KeshetAbney2024` — typed example data

Auto-generated from `Linglib/Data/Examples/KeshetAbney2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KeshetAbney2024.Examples`.
-/

@[expose] public section

namespace KeshetAbney2024.Examples

def ex_2a : Datum :=
  { id := "keshetabney2024_2a"
    source := ⟨"keshet-abney-2024", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone is eating a cheeseburger. It is very large!"
    glossedTokens := []
    context := "Everyone is (atypically) sharing a huge cheeseburger."
    judgment := .acceptable
    contrasts := [("Everyone is eating a cheeseburger. They are very large!", .acceptable)]
    readings := []
    paperFeatures := [("operator", "every"), ("pronoun", "summation")] }

def ex_3a : Datum :=
  { id := "keshetabney2024_3a"
    source := ⟨"keshet-abney-2024", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Andrea might be eating a cheeseburger. It is very large!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("Andrea might be eating a cheeseburger. They are very large!", .unacceptable)]
    readings := [("the burger she might be eating is/would be large", .unacceptable)]
    paperFeatures := [("operator", "might"), ("pronoun", "summation")] }

def ex_4 : Datum :=
  { id := "keshetabney2024_4"
    source := ⟨"keshet-abney-2024", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Andrea might be eating a cheeseburger. They are on the kitchen counter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("the various cheeseburgers Andrea might be eating are all on the counter", .unacceptable)]
    paperFeatures := [("operator", "might"), ("pronoun", "summation")] }

def ex_5a : Datum :=
  { id := "keshetabney2024_5a"
    source := ⟨"keshet-abney-2024", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There might already be a winner in the mayoral election. She is a woman."
    glossedTokens := []
    context := "Exactly five well-known candidates have run, no write-ins; late on election night the speaker has not checked the news, and may even have one candidate in mind as the possible winner."
    judgment := .unacceptable
    contrasts := [("There might already be a winner in the mayoral election. They are women.", .unacceptable)]
    readings := [("the possible winner is a woman", .unacceptable)]
    paperFeatures := [("operator", "might"), ("pronoun", "summation"), ("referents_exist", "true")] }

def ex_6 : Datum :=
  { id := "keshetabney2024_6"
    source := ⟨"keshet-abney-2024", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there's a light on at 9pm, it is possible that one of the teachers is still inside the school building. She is working late."
    glossedTokens := []
    context := "The teachers of a particular school; the speaker has no particular teacher in mind."
    judgment := .unacceptable
    contrasts := [("… He is working late.", .unacceptable), ("… They are working late.", .unacceptable)]
    readings := []
    paperFeatures := [("operator", "possible"), ("pronoun", "summation"), ("referents_exist", "true")] }

def ex_10 : Datum :=
  { id := "keshetabney2024_10"
    source := ⟨"keshet-abney-2024", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There must be some sort of animal in the shed. It's making quite a racket!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "must"), ("pronoun", "summation")] }

def ex_11 : Datum :=
  { id := "keshetabney2024_11"
    source := ⟨"keshet-abney-2024", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it's cancer, there must be a test. — You just did it."
    glossedTokens := []
    context := "House, Season 5, Episode 9 (corpus attestation)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "must"), ("pronoun", "summation")] }

def ex_16a : Datum :=
  { id := "keshetabney2024_16a"
    source := ⟨"keshet-abney-2024", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jerry might own a car, but they are still a hassle."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Jerry doesn't own a car—they are too much of a hassle!", .acceptable)]
    readings := [("'they' refers to the kind cars", .acceptable)]
    paperFeatures := [("operator", "might"), ("pronoun", "kind")] }

def ex_22a : Datum :=
  { id := "keshetabney2024_22a"
    source := ⟨"keshet-abney-2024", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog appeared. It barked."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "none"), ("pronoun", "simple")] }

def ex_52 : Datum :=
  { id := "keshetabney2024_52"
    source := ⟨"keshet-abney-2024", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Between one and five bunnies live in my yard. It ate my tulips."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "none"), ("pronoun", "simple")] }

def ex_53 : Datum :=
  { id := "keshetabney2024_53"
    source := ⟨"keshet-abney-2024", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farmer that owns a donkey beats it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "every"), ("pronoun", "simple")] }

def ex_57a : Datum :=
  { id := "keshetabney2024_57a"
    source := ⟨"keshet-abney-2024", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farmer that owns a donkey beats it. Most treat it well otherwise."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("most of the donkeys that are owned and beaten are otherwise treated well", .acceptable)]
    paperFeatures := [("operator", "most"), ("pronoun", "simple"), ("subordination", "quantificational")] }

def ex_58a : Datum :=
  { id := "keshetabney2024_58a"
    source := ⟨"keshet-abney-2024", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Sal has a pet, it must be a donkey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "must"), ("pronoun", "simple"), ("subordination", "modal")] }

def ex_59 : Datum :=
  { id := "keshetabney2024_59"
    source := ⟨"keshet-abney-2024", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A wolf might enter. It would eat Tasty Tim."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "might"), ("pronoun", "simple"), ("subordination", "modal")] }

def ex_61 : Datum :=
  { id := "keshetabney2024_61"
    source := ⟨"keshet-abney-2024", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some girls were having lunch in the cafeteria. They waved to some other girls having lunch there, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "none"), ("pronoun", "simple")] }

def ex_62 : Datum :=
  { id := "keshetabney2024_62"
    source := ⟨"keshet-abney-2024", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most girls were having lunch in the cafeteria. They waved to some other girls having lunch there, too."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most"), ("pronoun", "summation")] }

def ex_66 : Datum :=
  { id := "keshetabney2024_66"
    source := ⟨"keshet-abney-2024", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Almost every girl brought in the paper she wrote. Few of them forgot it at home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("'it' refers to the papers written by the few forgetful girls", .acceptable)]
    paperFeatures := [("operator", "few"), ("pronoun", "paycheck")] }

def ex_74 : Datum :=
  { id := "keshetabney2024_74"
    source := ⟨"keshet-abney-2024", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Andrea is eating a cheeseburger. It is large."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "none"), ("pronoun", "simple")] }

def ex_79 : Datum :=
  { id := "keshetabney2024_79"
    source := ⟨"keshet-abney-2024", "(79)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Andrea might be eating a cheeseburger. It is large."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "might"), ("pronoun", "summation")] }

def ex_85 : Datum :=
  { id := "keshetabney2024_85"
    source := ⟨"keshet-abney-2024", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There may already be a winner in the mayoral race. She is a woman, you know."
    glossedTokens := []
    context := "A known set of real-life candidates, no write-ins; late on election night the tabulation might be over."
    judgment := .unacceptable
    contrasts := []
    readings := [("the likely/possible/potential winner is a woman", .unacceptable)]
    paperFeatures := [("operator", "may"), ("pronoun", "summation"), ("referents_exist", "true")] }

def ex_91 : Datum :=
  { id := "keshetabney2024_91"
    source := ⟨"geach-1967", ""⟩
    reportedIn := some ⟨"keshet-abney-2024", "(91)"⟩
    language := "stan1293"
    primaryText := "Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the same witch) killed Cob's sow."
    glossedTokens := []
    context := "A town with an outbreak of witch mania."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "think"), ("pronoun", "summation")] }

def ex_92b : Datum :=
  { id := "keshetabney2024_92b"
    source := ⟨"keshet-abney-2024", "(92b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there's no bathroom in this house or it's in a funny place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Either John doesn't own a donkey, or he keeps it very quiet.", .acceptable)]
    readings := []
    paperFeatures := [("operator", "negation"), ("pronoun", "summation")] }

def all : List Datum := [ex_2a, ex_3a, ex_4, ex_5a, ex_6, ex_10, ex_11, ex_16a, ex_22a, ex_52, ex_53, ex_57a, ex_58a, ex_59, ex_61, ex_62, ex_66, ex_74, ex_79, ex_85, ex_91, ex_92b]

end KeshetAbney2024.Examples
