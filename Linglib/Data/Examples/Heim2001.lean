module

public import Linglib.Data.Examples.Schema

/-!
# `Heim2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim2001.Examples`.
-/

@[expose] public section

namespace Heim2001.Examples

def ex_7 : Datum :=
  { id := "heim2001_7"
    source := ⟨"heim-2001", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is taller than 4 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "max{d : tall(j, d)} > 4 feet")] }

def ex_8 : Datum :=
  { id := "heim2001_8"
    source := ⟨"heim-2001", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is taller than 4 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "universal"), ("claim", "the two LFs (9) are equivalent, (10)")] }

def ex_11 : Datum :=
  { id := "heim2001_11"
    source := ⟨"heim-2001", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some girl is taller than 4 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "existential"), ("claim", "the two LFs are equivalent, (12)")] }

def ex_13a : Datum :=
  { id := "heim2001_13a"
    source := ⟨"heim-2001", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is as tall as John is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "universal"), ("claim", "the equivalence extends to equatives")] }

def ex_13b : Datum :=
  { id := "heim2001_13b"
    source := ⟨"heim-2001", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some girl is as tall as John is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "existential")] }

def ex_14a : Datum :=
  { id := "heim2001_14a"
    source := ⟨"heim-2001", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than 20 girls are taller than 4 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "monotone increasing")] }

def ex_14b : Datum :=
  { id := "heim2001_14b"
    source := ⟨"heim-2001", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most of the papers are longer than 5 pages."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "monotone increasing")] }

def ex_15a : Datum :=
  { id := "heim2001_15a"
    source := ⟨"heim-2001", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is required to be longer than 10 pages."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "necessity"), ("claim", "the two LFs (16) are equivalent")] }

def ex_15b : Datum :=
  { id := "heim2001_15b"
    source := ⟨"heim-2001", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is allowed to be longer than 10 pages."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "possibility")] }

def ex_17a : Datum :=
  { id := "heim2001_17a"
    source := ⟨"heim-2001", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary isn't taller than 4 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "negation"), ("claim", "the high-DegP LF (17c) refers to an undefined maximum")] }

def ex_18a : Datum :=
  { id := "heim2001_18a"
    source := ⟨"heim-2001", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most two girls are taller than 5 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "monotone decreasing")] }

def ex_19a : Datum :=
  { id := "heim2001_19a"
    source := ⟨"heim-2001", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Mary works 60 hrs a week, and) she refuses to work harder than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "implicitly negative")] }

def ex_20a : Datum :=
  { id := "heim2001_20a"
    source := ⟨"heim-2001", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly two girls are taller than 5 feet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.1"), ("operator", "non-monotone"), ("claim", "the high-DegP LF (20c) has a defined maximum and means at least two girls are taller")] }

def ex_21a : Datum :=
  { id := "heim2001_21a"
    source := ⟨"heim-2001", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some girl is exactly 1'' taller than that."
    glossedTokens := []
    context := "John is 4' tall."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.2"), ("operator", "existential"), ("differential", "exactly")] }

def ex_22a : Datum :=
  { id := "heim2001_22a"
    source := ⟨"heim-2001", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is exactly 1'' taller than that."
    glossedTokens := []
    context := "John is 4' tall."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.2"), ("operator", "universal"), ("differential", "exactly"), ("claim", "(22c) is true and the sentence false when the shortest girl is exactly 4'1'' and others are taller")] }

def ex_24a : Datum :=
  { id := "heim2001_24a"
    source := ⟨"heim-2001", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is less tall than that."
    glossedTokens := []
    context := "John is 4' tall."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.2"), ("operator", "universal"), ("comparative", "less"), ("claim", "(24c) says the shortest girl is less than 4' tall, not an available reading")] }

def ex_25 : Datum :=
  { id := "heim2001_25"
    source := ⟨"heim-2001", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary set every post exactly 2 feet deeper than that."
    glossedTokens := []
    context := "The frostline is 3 and a half feet deep."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.2"), ("operator", "universal object"), ("differential", "exactly")] }

def ex_26 : Datum :=
  { id := "heim2001_26"
    source := ⟨"heim-2001", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was less impressed with every candidate than that."
    glossedTokens := []
    context := "John gave every candidate an A."
    judgment := .marginal
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .unacceptable)]
    paperFeatures := [("section", "2.2"), ("operator", "universal internal argument"), ("comparative", "less")] }

def ex_28a : Datum :=
  { id := "heim2001_28a"
    source := ⟨"heim-2001", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is required to be exactly 5 pages longer than that."
    glossedTokens := []
    context := "This draft is 10 pages."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.3"), ("verb", "require"), ("class", "deontic"), ("highDegP", "yes")] }

def ex_29a : Datum :=
  { id := "heim2001_29a"
    source := ⟨"heim-2001", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is allowed to be exactly 5 pages longer than that."
    glossedTokens := []
    context := "This draft is 10 pages."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.3"), ("verb", "allow"), ("class", "possibility"), ("highDegP", "yes")] }

def ex_30a : Datum :=
  { id := "heim2001_30a"
    source := ⟨"heim-2001", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is required to be less long than that."
    glossedTokens := []
    context := "This draft is 10 pages."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.3"), ("verb", "require"), ("class", "deontic"), ("highDegP", "yes")] }

def ex_31a : Datum :=
  { id := "heim2001_31a"
    source := ⟨"heim-2001", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is allowed to be less long than that."
    glossedTokens := []
    context := "This draft is 10 pages."
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.3"), ("verb", "allow"), ("class", "possibility"), ("highDegP", "yes")] }

def ex_32a : Datum :=
  { id := "heim2001_32a"
    source := ⟨"heim-2001", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is able to run less fast than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.3"), ("verb", "be able"), ("class", "possibility"), ("highDegP", "yes")] }

def ex_32b : Datum :=
  { id := "heim2001_32b"
    source := ⟨"heim-2001", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper needs to be exactly 5 pp longer than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "2.3"), ("verb", "need"), ("class", "deontic"), ("highDegP", "yes")] }

def ex_33 : Datum :=
  { id := "heim2001_33"
    source := ⟨"heim-2001", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper might be less long than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .ungrammatical)]
    paperFeatures := [("section", "2.3"), ("verb", "might"), ("class", "epistemic"), ("highDegP", "no")] }

def ex_34a : Datum :=
  { id := "heim2001_34a"
    source := ⟨"heim-2001", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper should be less long than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .ungrammatical)]
    paperFeatures := [("section", "2.3"), ("verb", "should"), ("class", "negRaising"), ("highDegP", "no")] }

def ex_34b : Datum :=
  { id := "heim2001_34b"
    source := ⟨"heim-2001", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is supposed to be less long than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .ungrammatical)]
    paperFeatures := [("section", "2.3"), ("verb", "be supposed to"), ("class", "negRaising"), ("highDegP", "no")] }

def ex_34c : Datum :=
  { id := "heim2001_34c"
    source := ⟨"heim-2001", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want the paper to be less long than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .ungrammatical)]
    paperFeatures := [("section", "2.3"), ("verb", "want"), ("class", "negRaising"), ("highDegP", "no")] }

def ex_37 : Datum :=
  { id := "heim2001_37"
    source := ⟨"heim-2001", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks the yacht is longer than it is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("de dicto", .acceptable), ("de re", .acceptable)]
    paperFeatures := [("section", "2.4"), ("claim", "the Russell ambiguity is de re versus de dicto, not DegP scope, (40)")] }

def ex_38 : Datum :=
  { id := "heim2001_38"
    source := ⟨"heim-2001", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary smoked less than she does, she would be healthier."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("claim", "a high-DegP LF would misrepresent the truth conditions")] }

def ex_41 : Datum :=
  { id := "heim2001_41"
    source := ⟨"heim-2001", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The box is required to be less wide than it is tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("claim", "three readings: low DegP de dicto, low DegP de re, high DegP de re")] }

def ex_42 : Datum :=
  { id := "heim2001_42"
    source := ⟨"heim-2001", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The box is not required to be as wide as it is tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("claim", "adds a de dicto reading (41) lacks")] }

def ex_58 : Datum :=
  { id := "heim2001_58"
    source := ⟨"heim-2001", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John screamed (the) loudest."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("claim", "the complement of -est is used twice, (59)")] }

def ex_60a : Datum :=
  { id := "heim2001_60a"
    source := ⟨"heim-2001", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs to drive faster than Mary does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "3.2"), ("claim", "two readings by the size of the ellipsis antecedent")] }

def ex_60b : Datum :=
  { id := "heim2001_60b"
    source := ⟨"heim-2001", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs to drive fastest."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "3.2"), ("claim", "the same two readings by scoping -est, (61)")] }

def ex_63 : Datum :=
  { id := "heim2001_63"
    source := ⟨"heim-2001", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John needs (to have) too much money."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("low DegP", .acceptable), ("high DegP", .acceptable)]
    paperFeatures := [("section", "3.2"), ("claim", "two readings by scoping too, (62)")] }

def all : List Datum := [ex_7, ex_8, ex_11, ex_13a, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_17a, ex_18a, ex_19a, ex_20a, ex_21a, ex_22a, ex_24a, ex_25, ex_26, ex_28a, ex_29a, ex_30a, ex_31a, ex_32a, ex_32b, ex_33, ex_34a, ex_34b, ex_34c, ex_37, ex_38, ex_41, ex_42, ex_58, ex_60a, ex_60b, ex_63]

end Heim2001.Examples
