module

public import Linglib.Data.Examples.Schema

/-!
# `Yan2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Yan2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yan2023.Examples`.
-/

@[expose] public section

namespace Yan2023.Examples

def ex_1 : Datum :=
  { id := "yan2023_1"
    source := ⟨"yan-2023", "Ch. 4 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas wants a free trip on the Concorde."
    glossedTokens := []
    context := "Nicholas is not willing to pay the 3,000 dollars he believes a trip would cost."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("role", "premise")] }

def ex_2 : Datum :=
  { id := "yan2023_2"
    source := ⟨"yan-2023", "Ch. 4 (1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas wants a trip on the Concorde."
    glossedTokens := []
    context := "As in (1b)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("role", "monotonic conclusion"), ("holds", "no")] }

def ex_3 : Datum :=
  { id := "yan2023_3"
    source := ⟨"yan-2023", "Ch. 4 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want to teach on Tuesdays next semester."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Heim"), ("role", "premise")] }

def ex_4 : Datum :=
  { id := "yan2023_4"
    source := ⟨"yan-2023", "Ch. 4 (2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want to teach next semester."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Heim"), ("role", "monotonic conclusion")] }

def ex_5 : Datum :=
  { id := "yan2023_5"
    source := ⟨"yan-2023", "Ch. 4 (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to send the letter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("role", "premise")] }

def ex_6 : Datum :=
  { id := "yan2023_6"
    source := ⟨"yan-2023", "Ch. 4 (3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to send the letter or burn it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("role", "monotonic conclusion")] }

def ex_7 : Datum :=
  { id := "yan2023_7"
    source := ⟨"yan-2023", "Ch. 4 (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to buy a Ferrari or a Porsche."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("John is ok with a Ferrari and he is ok with a Porsche", .acceptable)]
    paperFeatures := [("inference", "box free choice")] }

def ex_8 : Datum :=
  { id := "yan2023_8"
    source := ⟨"yan-2023", "Ch. 4 (26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for John to send the letter."
    glossedTokens := []
    context := "John wants to send the letter."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("formula", "◇SEND a")] }

def ex_9 : Datum :=
  { id := "yan2023_9"
    source := ⟨"yan-2023", "Ch. 4 (26d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for John to burn the letter."
    glossedTokens := []
    context := "John wants to send the letter."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("formula", "◇BURN a")] }

def ex_10 : Datum :=
  { id := "yan2023_10"
    source := ⟨"yan-2023", "Ch. 4 (27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for Nicholas to have a free trip."
    glossedTokens := []
    context := "Nicholas wants a free trip on the Concorde."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("formula", "◇∃x FREE x")] }

def ex_11 : Datum :=
  { id := "yan2023_11"
    source := ⟨"yan-2023", "Ch. 4 (27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for Nicholas to have a non-free trip."
    glossedTokens := []
    context := "Nicholas wants a free trip on the Concorde."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Asher"), ("formula", "◇∃x ¬FREE x")] }

def ex_12 : Datum :=
  { id := "yan2023_12"
    source := ⟨"yan-2023", "Ch. 4 (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't want to eat any fast food."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidence", "monotonicity"), ("item", "NPI any")] }

def ex_13 : Datum :=
  { id := "yan2023_13"
    source := ⟨"yan-2023", "Ch. 4 (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jones wants to buy a green sweater, but she doesn't want to buy a sweater."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("evidence", "monotonicity"), ("role", "contradiction"), ("felicity", "infelicitous")] }

def ex_14 : Datum :=
  { id := "yan2023_14"
    source := ⟨"yan-2023", "Ch. 4 (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ok for John to send the letter, and it is ok for him to burn it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Ross"), ("role", "free-choice inference")] }

def ex_15 : Datum :=
  { id := "yan2023_15"
    source := ⟨"yan-2023", "Ch. 4 (16c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm ok to teach on the days that are not Tuesday next semester."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Heim"), ("role", "unwarranted inference")] }

def ex_16 : Datum :=
  { id := "yan2023_16"
    source := ⟨"yan-2023", "Ch. 4 (19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The school wants that students who struggle with math attend tutoring."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Good Samaritan under desire"), ("role", "premise")] }

def ex_17 : Datum :=
  { id := "yan2023_17"
    source := ⟨"yan-2023", "Ch. 4 (19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The school wants that students struggle with math."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("puzzle", "Good Samaritan under desire"), ("role", "monotonic conclusion")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17]

end Yan2023.Examples
