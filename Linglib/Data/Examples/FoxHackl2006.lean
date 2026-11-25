module

public import Linglib.Data.Examples.Schema

/-!
# `FoxHackl2006` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxHackl2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxHackl2006.Examples`.
-/

@[expose] public section

namespace FoxHackl2006.Examples

def ex_1 : Datum :=
  { id := "foxhackl2006_1"
    source := ⟨"fox-hackl-2006", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has 3 children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John doesn't have 4 children", .acceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "none"), ("property", "upward")] }

def ex_2 : Datum :=
  { id := "foxhackl2006_2"
    source := ⟨"fox-hackl-2006", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has more than 3 children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John doesn't have more than 4 children", .unacceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "none"), ("property", "upward")] }

def ex_4 : Datum :=
  { id := "foxhackl2006_4"
    source := ⟨"fox-hackl-2006", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has very few children. He only has 3F (children)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "none"), ("property", "upward")] }

def ex_5 : Datum :=
  { id := "foxhackl2006_5"
    source := ⟨"fox-hackl-2006", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has very few children. He only has more than 3F (children)."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "none"), ("property", "upward")] }

def ex_7a : Datum :=
  { id := "foxhackl2006_7a"
    source := ⟨"fox-hackl-2006", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John weighs 120 pounds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John only weighs 120 pounds", .acceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "none"), ("property", "upward")] }

def ex_7b : Datum :=
  { id := "foxhackl2006_7b"
    source := ⟨"fox-hackl-2006", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John weighs more than 120 pounds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: for every degree d greater than 120, John does not weigh more than d pounds", .unacceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "none"), ("property", "upward")] }

def ex_7c : Datum :=
  { id := "foxhackl2006_7c"
    source := ⟨"fox-hackl-2006", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only weighs more than 120F pounds."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "none"), ("property", "upward")] }

def ex_13a : Datum :=
  { id := "foxhackl2006_13a"
    source := ⟨"fox-hackl-2006", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're required to read more than 30 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: there is no degree d greater than 30 such that you are required to read more than d books", .acceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "universal"), ("property", "upward")] }

def ex_13b : Datum :=
  { id := "foxhackl2006_13b"
    source := ⟨"fox-hackl-2006", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're only required to read more than 30F books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "universal"), ("property", "upward")] }

def ex_14a : Datum :=
  { id := "foxhackl2006_14a"
    source := ⟨"fox-hackl-2006", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're allowed to smoke more than 30 cigarettes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: there is no degree d greater than 30 such that you are allowed to smoke more than d cigarettes", .ungrammatical)]
    paperFeatures := [("operator", "exh"), ("modal", "existential"), ("property", "upward")] }

def ex_14b : Datum :=
  { id := "foxhackl2006_14b"
    source := ⟨"fox-hackl-2006", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're only allowed to smoke more than 30F cigarettes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "existential"), ("property", "upward")] }

def ex_16 : Datum :=
  { id := "foxhackl2006_16"
    source := ⟨"fox-hackl-2006", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much does John not weigh?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "downward")] }

def ex_19a : Datum :=
  { id := "foxhackl2006_19a"
    source := ⟨"fox-hackl-2006", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have the amount of water that you don't."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("I have the amount of water that you do.", .acceptable)]
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "none"), ("property", "downward")] }

def ex_19b : Datum :=
  { id := "foxhackl2006_19b"
    source := ⟨"fox-hackl-2006", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have an amount of water that you don't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "indefinite"), ("modal", "none"), ("property", "downward")] }

def ex_21 : Datum :=
  { id := "foxhackl2006_21"
    source := ⟨"fox-hackl-2006", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much flour is sufficient to bake a cake?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "downward")] }

def ex_23 : Datum :=
  { id := "foxhackl2006_23"
    source := ⟨"fox-hackl-2006", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have the amount of flour sufficient to bake a cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "none"), ("property", "downward")] }

def ex_27a : Datum :=
  { id := "foxhackl2006_27a"
    source := ⟨"fox-hackl-2006", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much are you sure that this vessel won't weigh?"
    glossedTokens := []
    context := "The addressee does not know how much the vessel will weigh but can put an upper bound on possible weights."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "downward")] }

def ex_27b : Datum :=
  { id := "foxhackl2006_27b"
    source := ⟨"fox-hackl-2006", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much radiation are we not allowed to expose our workers to?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "downward")] }

def ex_27c : Datum :=
  { id := "foxhackl2006_27c"
    source := ⟨"fox-hackl-2006", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The amount of radiation that we are not allowed to expose our workers to is greater than we had thought."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "universal"), ("property", "downward")] }

def ex_28a : Datum :=
  { id := "foxhackl2006_28a"
    source := ⟨"fox-hackl-2006", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much radiation is the company not allowed to expose its workers to?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "downward")] }

def ex_28b : Datum :=
  { id := "foxhackl2006_28b"
    source := ⟨"fox-hackl-2006", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much food is the company not required to give its workers?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "existential"), ("property", "downward")] }

def ex_29a : Datum :=
  { id := "foxhackl2006_29a"
    source := ⟨"fox-hackl-2006", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much radiation is the company required not to expose its workers to?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "downward")] }

def ex_29b : Datum :=
  { id := "foxhackl2006_29b"
    source := ⟨"fox-hackl-2006", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How much food is the company allowed not to give its workers?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "existential"), ("property", "downward")] }

def ex_30b : Datum :=
  { id := "foxhackl2006_30b"
    source := ⟨"fox-hackl-2006", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The amount of food that the company is not required to give its workers is quite high."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "existential"), ("property", "downward")] }

def ex_32 : Datum :=
  { id := "foxhackl2006_32"
    source := ⟨"fox-hackl-2006", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Before when did John arrive?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "downward")] }

def ex_33 : Datum :=
  { id := "foxhackl2006_33"
    source := ⟨"fox-hackl-2006", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Before when do you have to arrive?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "downward")] }

def ex_34 : Datum :=
  { id := "foxhackl2006_34"
    source := ⟨"fox-hackl-2006", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Before when are you allowed to arrive?"
    glossedTokens := []
    context := "Addressed to a guest of a youth hostel whose doors are locked at 10 pm."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "existential"), ("property", "downward")] }

def ex_50a : Datum :=
  { id := "foxhackl2006_50a"
    source := ⟨"fox-hackl-2006", "(50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't smoke 30 cigarettes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John smoked 29 cigarettes", .ungrammatical)]
    paperFeatures := [("operator", "exh"), ("modal", "none"), ("property", "downward")] }

def ex_50b : Datum :=
  { id := "foxhackl2006_50b"
    source := ⟨"fox-hackl-2006", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't read 30 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John read 29 books", .ungrammatical)]
    paperFeatures := [("operator", "exh"), ("modal", "none"), ("property", "downward")] }

def ex_52 : Datum :=
  { id := "foxhackl2006_52"
    source := ⟨"fox-hackl-2006", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not allowed to smoke 30 cigarettes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John is allowed to smoke 29 cigarettes", .acceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "universal"), ("property", "downward")] }

def ex_53 : Datum :=
  { id := "foxhackl2006_53"
    source := ⟨"fox-hackl-2006", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required not to smoke 30 cigarettes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John is allowed to smoke 29 cigarettes", .acceptable)]
    paperFeatures := [("operator", "exh"), ("modal", "universal"), ("property", "downward")] }

def ex_54 : Datum :=
  { id := "foxhackl2006_54"
    source := ⟨"fox-hackl-2006", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not required to read 30 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John is required to read 29 books", .ungrammatical)]
    paperFeatures := [("operator", "exh"), ("modal", "existential"), ("property", "downward")] }

def ex_55 : Datum :=
  { id := "foxhackl2006_55"
    source := ⟨"fox-hackl-2006", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is allowed not to read 30 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("implicature: John is required to read 29 books", .ungrammatical)]
    paperFeatures := [("operator", "exh"), ("modal", "existential"), ("property", "downward")] }

def ex_57a : Datum :=
  { id := "foxhackl2006_57a"
    source := ⟨"fox-hackl-2006", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has only not smoked 30F cigarettes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "none"), ("property", "downward")] }

def ex_57c : Datum :=
  { id := "foxhackl2006_57c"
    source := ⟨"fox-hackl-2006", "(57c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only does not weigh 190F pounds."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "none"), ("property", "downward")] }

def ex_58a : Datum :=
  { id := "foxhackl2006_58a"
    source := ⟨"fox-hackl-2006", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is only required not to smoke 30F cigarettes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "universal"), ("property", "downward")] }

def ex_60 : Datum :=
  { id := "foxhackl2006_60"
    source := ⟨"fox-hackl-2006", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is only allowed not to read 30F books."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "existential"), ("property", "downward")] }

def ex_61 : Datum :=
  { id := "foxhackl2006_61"
    source := ⟨"fox-hackl-2006", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is only not required to read 30F books."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "only"), ("modal", "existential"), ("property", "downward")] }

def ex_62a : Datum :=
  { id := "foxhackl2006_62a"
    source := ⟨"fox-hackl-2006", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than how many books did John read?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "upward")] }

def ex_62b : Datum :=
  { id := "foxhackl2006_62b"
    source := ⟨"fox-hackl-2006", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than how many books does John have to read?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "upward")] }

def ex_62c : Datum :=
  { id := "foxhackl2006_62c"
    source := ⟨"fox-hackl-2006", "(62c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than how many cigarettes is John allowed to smoke?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alsoJudged := [.ungrammatical]
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "existential"), ("property", "upward")] }

def ex_63a : Datum :=
  { id := "foxhackl2006_63a"
    source := ⟨"fox-hackl-2006", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many feet is John under?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "upward")] }

def ex_63b : Datum :=
  { id := "foxhackl2006_63b"
    source := ⟨"fox-hackl-2006", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many feet do you have to be under to take this ride?"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "universal"), ("property", "upward")] }

def ex_64a : Datum :=
  { id := "foxhackl2006_64a"
    source := ⟨"fox-hackl-2006", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The amount of food such that you ate more than that (is greater than I had thought)."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "none"), ("property", "upward")] }

def ex_64b : Datum :=
  { id := "foxhackl2006_64b"
    source := ⟨"fox-hackl-2006", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The amount of food such that we are required to eat more than that (is greater than we had thought)."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "universal"), ("property", "upward")] }

def ex_64c : Datum :=
  { id := "foxhackl2006_64c"
    source := ⟨"fox-hackl-2006", "(64c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The amount of candy such that we are allowed to eat more than that (is greater than we had thought)."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "definite"), ("modal", "existential"), ("property", "upward")] }

def ex_100a : Datum :=
  { id := "foxhackl2006_100a"
    source := ⟨"fox-hackl-2006", "(100a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tell me how many points Iverson didn't score?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "downward")] }

def ex_100b : Datum :=
  { id := "foxhackl2006_100b"
    source := ⟨"fox-hackl-2006", "(100b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Among the following, please tell me how many points Iverson didn't score? A. 20 B. 30 C. 40 D. 50"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "question"), ("modal", "none"), ("property", "downward")] }

def all : List Datum := [ex_1, ex_2, ex_4, ex_5, ex_7a, ex_7b, ex_7c, ex_13a, ex_13b, ex_14a, ex_14b, ex_16, ex_19a, ex_19b, ex_21, ex_23, ex_27a, ex_27b, ex_27c, ex_28a, ex_28b, ex_29a, ex_29b, ex_30b, ex_32, ex_33, ex_34, ex_50a, ex_50b, ex_52, ex_53, ex_54, ex_55, ex_57a, ex_57c, ex_58a, ex_60, ex_61, ex_62a, ex_62b, ex_62c, ex_63a, ex_63b, ex_64a, ex_64b, ex_64c, ex_100a, ex_100b]

end FoxHackl2006.Examples
