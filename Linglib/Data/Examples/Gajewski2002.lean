module

public import Linglib.Data.Examples.Schema

/-!
# `Gajewski2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Gajewski2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gajewski2002.Examples`.
-/

@[expose] public section

namespace Gajewski2002.Examples

def ex4a : Datum :=
  { id := "gajewski2002_ex4a"
    source := ⟨"gajewski-2002", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is the wolf at the door."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "the"), ("strength", "strong"), ("grammatical", "no")] }

def ex4b : Datum :=
  { id := "gajewski2002_ex4b"
    source := ⟨"gajewski-2002", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There were John and Mary cycling along the creek."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "none"), ("strength", "strong"), ("grammatical", "no")] }

def ex4c : Datum :=
  { id := "gajewski2002_ex4c"
    source := ⟨"gajewski-2002", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There was everyone in the room."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "every"), ("strength", "strong"), ("grammatical", "no")] }

def ex5a : Datum :=
  { id := "gajewski2002_ex5a"
    source := ⟨"gajewski-2002", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a wolf at the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "some"), ("strength", "weak"), ("grammatical", "yes")] }

def ex5b : Datum :=
  { id := "gajewski2002_ex5b"
    source := ⟨"gajewski-2002", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There were two people cycling along the creek."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "two"), ("strength", "weak"), ("grammatical", "yes")] }

def ex5c : Datum :=
  { id := "gajewski2002_ex5c"
    source := ⟨"gajewski-2002", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There was someone in the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "some"), ("strength", "weak"), ("grammatical", "yes")] }

def ex11a_every : Datum :=
  { id := "gajewski2002_ex11a_every"
    source := ⟨"gajewski-2002", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "every"), ("grammatical", "yes")] }

def ex11a_no : Datum :=
  { id := "gajewski2002_ex11a_no"
    source := ⟨"gajewski-2002", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "no"), ("grammatical", "yes")] }

def ex11b_some : Datum :=
  { id := "gajewski2002_ex11b_some"
    source := ⟨"gajewski-2002", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "some"), ("grammatical", "no")] }

def ex11b_three : Datum :=
  { id := "gajewski2002_ex11b_three"
    source := ⟨"gajewski-2002", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "three"), ("grammatical", "no")] }

def ex11b_many : Datum :=
  { id := "gajewski2002_ex11b_many"
    source := ⟨"gajewski-2002", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Many students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "many"), ("grammatical", "no")] }

def ex11c_most : Datum :=
  { id := "gajewski2002_ex11c_most"
    source := ⟨"gajewski-2002", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "most"), ("grammatical", "no")] }

def ex11c_exactly_two : Datum :=
  { id := "gajewski2002_ex11c_exactly_two"
    source := ⟨"gajewski-2002", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly two students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "exactly two"), ("grammatical", "no")] }

def ex11c_fewer_than_three : Datum :=
  { id := "gajewski2002_ex11c_fewer_than_three"
    source := ⟨"gajewski-2002", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fewer than three students but Bill passed the exam."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "fewer than three"), ("grammatical", "no")] }

def ex30a : Datum :=
  { id := "gajewski2002_ex30a"
    source := ⟨"gajewski-2002", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is every new student."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "every"), ("grammatical", "no")] }

def ex34a : Datum :=
  { id := "gajewski2002_ex34a"
    source := ⟨"gajewski-2002", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman is a woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "everyIs"), ("determiner", "every"), ("grammatical", "yes")] }

def ex34b : Datum :=
  { id := "gajewski2002_ex34b"
    source := ⟨"gajewski-2002", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is smoking and John is not smoking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "andNot"), ("determiner", "none"), ("grammatical", "yes")] }

def all : List Datum := [ex4a, ex4b, ex4c, ex5a, ex5b, ex5c, ex11a_every, ex11a_no, ex11b_some, ex11b_three, ex11b_many, ex11c_most, ex11c_exactly_two, ex11c_fewer_than_three, ex30a, ex34a, ex34b]

end Gajewski2002.Examples
