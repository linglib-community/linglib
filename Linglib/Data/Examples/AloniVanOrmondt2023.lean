module

public import Linglib.Data.Examples.Schema

/-!
# `AloniVanOrmondt2023` — typed example data

Auto-generated from `Linglib/Data/Examples/AloniVanOrmondt2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AloniVanOrmondt2023.Examples`.
-/

@[expose] public section

namespace AloniVanOrmondt2023.Examples

def ex_3a : Datum :=
  { id := "alonivanormondt2023_3a"
    source := ⟨"aloni-vanormondt-2023", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have at least three children."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("inference", "ignorance")] }

def ex_3b : Datum :=
  { id := "alonivanormondt2023_3b"
    source := ⟨"aloni-vanormondt-2023", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have more than two children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "comparative"), ("numeral", "2"), ("inference", "none")] }

def ex_4a : Datum :=
  { id := "alonivanormondt2023_4a"
    source := ⟨"aloni-vanormondt-2023", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A hexagon has at most 10 sides."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "10"), ("inference", "ignorance")] }

def ex_4b : Datum :=
  { id := "alonivanormondt2023_4b"
    source := ⟨"aloni-vanormondt-2023", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A hexagon has fewer than 11 sides."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "comparative"), ("numeral", "11"), ("inference", "none")] }

def ex_5 : Datum :=
  { id := "alonivanormondt2023_5"
    source := ⟨"aloni-vanormondt-2023", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has three players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("numeral", "3"), ("inference", "exact")] }

def ex_6 : Datum :=
  { id := "alonivanormondt2023_6"
    source := ⟨"aloni-vanormondt-2023", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has at least three players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("inference", "ignorance")] }

def ex_7 : Datum :=
  { id := "alonivanormondt2023_7"
    source := ⟨"aloni-vanormondt-2023", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has more than two players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "comparative"), ("numeral", "2"), ("inference", "none")] }

def ex_10 : Datum :=
  { id := "alonivanormondt2023_10"
    source := ⟨"aloni-vanormondt-2023", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Klaus married Paul or John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The speaker does not know who", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("inference", "ignorance")] }

def ex_11 : Datum :=
  { id := "alonivanormondt2023_11"
    source := ⟨"aloni-vanormondt-2023", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Klaus has three or four children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("The speaker does not know how many", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("inference", "ignorance")] }

def ex_12 : Datum :=
  { id := "alonivanormondt2023_12"
    source := ⟨"aloni-vanormondt-2023", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I married Paul or John."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("construction", "disjunction"), ("inference", "ignorance")] }

def ex_13 : Datum :=
  { id := "alonivanormondt2023_13"
    source := ⟨"aloni-vanormondt-2023", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have three or four children."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("construction", "disjunction"), ("inference", "ignorance")] }

def ex_18 : Datum :=
  { id := "alonivanormondt2023_18"
    source := ⟨"aloni-vanormondt-2023", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Klaus married with Paul or John"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("It is possible that Klaus married with Paul and it is possible that Klaus married with John", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("inference", "ignorance")] }

def ex_19 : Datum :=
  { id := "alonivanormondt2023_19"
    source := ⟨"aloni-vanormondt-2023", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has at least three players"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("It is possible that the band has exactly three players and it is possible that the band has more than three players", .acceptable)]
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("inference", "ignorance")] }

def ex_20 : Datum :=
  { id := "alonivanormondt2023_20"
    source := ⟨"aloni-vanormondt-2023", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone read at least three books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("embedding", "universal"), ("inference", "obviation")] }

def ex_21 : Datum :=
  { id := "alonivanormondt2023_21"
    source := ⟨"aloni-vanormondt-2023", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paprika is required to read at least three books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Authoritative: it has to be the case that Paprika reads three or more books", .acceptable), ("Epistemic: three or more is such that Paprika has to read that many books", .acceptable)]
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("embedding", "necessity"), ("inference", "obviation")] }

def ex_22 : Datum :=
  { id := "alonivanormondt2023_22"
    source := ⟨"aloni-vanormondt-2023", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The password must be at least five characters long."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "5"), ("embedding", "necessity"), ("inference", "obviation"), ("reading", "authoritative")] }

def ex_23 : Datum :=
  { id := "alonivanormondt2023_23"
    source := ⟨"aloni-vanormondt-2023", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To become a member of this club, you have to pay at least $200,000."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "200000"), ("embedding", "necessity"), ("inference", "ignorance"), ("reading", "epistemic")] }

def ex_24a : Datum :=
  { id := "alonivanormondt2023_24a"
    source := ⟨"aloni-vanormondt-2023", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paprika read two or three books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "disjunction"), ("inference", "ignorance")] }

def ex_25a : Datum :=
  { id := "alonivanormondt2023_25a"
    source := ⟨"aloni-vanormondt-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone read two or three books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "disjunction"), ("embedding", "universal"), ("inference", "obviation")] }

def ex_26 : Datum :=
  { id := "alonivanormondt2023_26"
    source := ⟨"aloni-vanormondt-2023", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paprika is required to read two or three books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Authoritative", .acceptable), ("Epistemic", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "necessity"), ("inference", "obviation")] }

def ex_27 : Datum :=
  { id := "alonivanormondt2023_27"
    source := ⟨"aloni-vanormondt-2023", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman in my family has two or three children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Some woman has two and some woman has three children", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "universal"), ("inference", "distribution"), ("knowledge", "full")] }

def ex_28 : Datum :=
  { id := "alonivanormondt2023_28"
    source := ⟨"aloni-vanormondt-2023", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman in my family has two or three children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Some woman might have two and some woman might have three children", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "universal"), ("inference", "distributionEpi"), ("knowledge", "partial")] }

def ex_29 : Datum :=
  { id := "alonivanormondt2023_29"
    source := ⟨"aloni-vanormondt-2023", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman in my family has at least three children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Full knowledge: some woman has three and some woman has more than three children", .acceptable), ("Partial information: some woman might have three and some woman might have more than three children", .acceptable)]
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("embedding", "universal"), ("inference", "distribution")] }

def ex_30a : Datum :=
  { id := "alonivanormondt2023_30a"
    source := ⟨"aloni-vanormondt-2023", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To pass this course you are required to give a presentation or write a short paper"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("You are allowed to give a presentation and you are allowed to write a short paper", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "necessity"), ("inference", "boxFreeChoice")] }

def ex_31a : Datum :=
  { id := "alonivanormondt2023_31a"
    source := ⟨"aloni-vanormondt-2023", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To pass the course, you're required to read at least three books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("You are allowed to read three books and you are allowed to read more", .acceptable)]
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("embedding", "necessity"), ("inference", "boxFreeChoice"), ("reading", "authoritative")] }

def ex_34 : Datum :=
  { id := "alonivanormondt2023_34"
    source := ⟨"aloni-vanormondt-2023", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every brother of mine has been married to a woman or a man."
    glossedTokens := []
    context := "All brothers have been married to a woman, and one of them married first a woman and then a man."
    judgment := .acceptable
    contrasts := []
    readings := [("Some brother has been married to a woman and some brother has been married to a man", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "universal"), ("inference", "distribution")] }

def ex_35a : Datum :=
  { id := "alonivanormondt2023_35a"
    source := ⟨"aloni-vanormondt-2023", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have coffee or tea"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("You may have coffee and you may have tea", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "possibility"), ("inference", "diamondFreeChoice")] }

def ex_39a : Datum :=
  { id := "alonivanormondt2023_39a"
    source := ⟨"aloni-vanormondt-2023", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some woman in my family has two or three children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Some woman has two and some woman has three", .unacceptable), ("Some woman in my family might have two children and might have three children", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "existential"), ("inference", "ignorance")] }

def ex_40a : Datum :=
  { id := "alonivanormondt2023_40a"
    source := ⟨"aloni-vanormondt-2023", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Klaus didn't marry John or Bill"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Klaus did not marry either of the two", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "negation"), ("inference", "negation")] }

def ex_41 : Datum :=
  { id := "alonivanormondt2023_41"
    source := ⟨"aloni-vanormondt-2023", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Klaus doesn't have at least 3 children."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("embedding", "negation"), ("inference", "negation")] }

def ex_42 : Datum :=
  { id := "alonivanormondt2023_42"
    source := ⟨"aloni-vanormondt-2023", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Klaus has less than 3 children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "comparative"), ("numeral", "3"), ("inference", "none")] }

def ex_45a : Datum :=
  { id := "alonivanormondt2023_45a"
    source := ⟨"aloni-vanormondt-2023", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has at least three players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("translation", "three ∨ more")] }

def ex_46a : Datum :=
  { id := "alonivanormondt2023_46a"
    source := ⟨"aloni-vanormondt-2023", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has at most three players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("translation", "three ∨ less")] }

def ex_47a : Datum :=
  { id := "alonivanormondt2023_47a"
    source := ⟨"aloni-vanormondt-2023", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has more than two players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "comparative"), ("numeral", "2"), ("translation", "more-than-two")] }

def ex_48a : Datum :=
  { id := "alonivanormondt2023_48a"
    source := ⟨"aloni-vanormondt-2023", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The band has less than two players."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "comparative"), ("numeral", "2"), ("translation", "less-than-two")] }

def ex_63a : Datum :=
  { id := "alonivanormondt2023_63a"
    source := ⟨"aloni-vanormondt-2023", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the boys may go to the beach or to the cinema."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("All of the boys may go to the beach and all of the boys may go to the cinema", .acceptable)]
    paperFeatures := [("construction", "disjunction"), ("embedding", "universalPossibility"), ("inference", "universalFreeChoice")] }

def ex_64 : Datum :=
  { id := "alonivanormondt2023_64"
    source := ⟨"aloni-vanormondt-2023", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John does not have at least three children."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "3"), ("embedding", "negation"), ("inference", "negation")] }

def ex_65 : Datum :=
  { id := "alonivanormondt2023_65"
    source := ⟨"aloni-vanormondt-2023", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every candidate who has at least 2 degrees will be invited for the interview."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "superlative"), ("numeral", "2"), ("embedding", "restrictor")] }

def all : List Datum := [ex_3a, ex_3b, ex_4a, ex_4b, ex_5, ex_6, ex_7, ex_10, ex_11, ex_12, ex_13, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24a, ex_25a, ex_26, ex_27, ex_28, ex_29, ex_30a, ex_31a, ex_34, ex_35a, ex_39a, ex_40a, ex_41, ex_42, ex_45a, ex_46a, ex_47a, ex_48a, ex_63a, ex_64, ex_65]

end AloniVanOrmondt2023.Examples
