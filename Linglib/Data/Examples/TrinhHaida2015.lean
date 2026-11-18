module

public import Linglib.Data.Examples.Schema

/-!
# `TrinhHaida2015` — typed example data

Auto-generated from `Linglib/Data/Examples/TrinhHaida2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TrinhHaida2015.Examples`.
-/

@[expose] public section

namespace TrinhHaida2015.Examples

def ex_5 : Datum :=
  { id := "trinhhaida2015_5"
    source := ⟨"trinh-haida-2015", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill went for a run and didn't smoke. John (only) went for a run."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John went for a run and didn't smoke], so John smoked", .acceptable)]
    paperFeatures := [("case", "symmetry breaking"), ("prejacent", "run"), ("contextual alternative", "run and not smoke")] }

def ex_6 : Datum :=
  { id := "trinhhaida2015_6"
    source := ⟨"trinh-haida-2015", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill passed some of the tests and failed some. John (only) passed some of the tests."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John passed some and failed some], so John passed all", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "pass some"), ("contextual alternative", "pass some and fail some"), ("felicity", "infelicitous")] }

def ex_9 : Datum :=
  { id := "trinhhaida2015_9"
    source := ⟨"trinh-haida-2015", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John (only) has three chairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: John does not have four chairs", .acceptable)]
    paperFeatures := [("case", "symmetry problem"), ("symmetric alternatives", "four; exactly three")] }

def ex_10 : Datum :=
  { id := "trinhhaida2015_10"
    source := ⟨"trinh-haida-2015", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John (only) did some of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: John did not do all of the homework", .acceptable)]
    paperFeatures := [("case", "symmetry problem"), ("symmetric alternatives", "all; some but not all")] }

def ex_20b : Datum :=
  { id := "trinhhaida2015_20b"
    source := ⟨"trinh-haida-2015", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill works hard and doesn't watch TV. John (only) works hard."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John works hard and doesn't watch TV]", .acceptable)]
    paperFeatures := [("case", "symmetry breaking"), ("prejacent", "work hard"), ("contextual alternative", "work hard and not watch TV")] }

def ex_20c : Datum :=
  { id := "trinhhaida2015_20c"
    source := ⟨"trinh-haida-2015", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill is tall and not bald. John is (only) tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John is tall and not bald]", .acceptable)]
    paperFeatures := [("case", "symmetry breaking"), ("prejacent", "tall"), ("contextual alternative", "tall and not bald")] }

def ex_21a : Datum :=
  { id := "trinhhaida2015_21a"
    source := ⟨"trinh-haida-2015", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill ate exactly three cookies. John (only) ate three cookies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John ate exactly three cookies]", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "three"), ("contextual alternative", "exactly three"), ("lexical alternative", "four")] }

def ex_21b : Datum :=
  { id := "trinhhaida2015_21b"
    source := ⟨"trinh-haida-2015", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill fathered children and no twins. John (only) fathered children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John fathered children and no twins]", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "children"), ("contextual alternative", "children and no twins"), ("lexical alternative", "twins")] }

def ex_21c : Datum :=
  { id := "trinhhaida2015_21c"
    source := ⟨"trinh-haida-2015", "(21c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill passed some of the fitness tests and failed some. John (only) passed some of the fitness tests."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [John passed some of the fitness tests and failed some]", .unacceptable)]
    paperFeatures := [("case", "symmetry preserving"), ("prejacent", "pass some"), ("contextual alternative", "pass some and fail some"), ("lexical alternative", "pass all")] }

def ex_50 : Datum :=
  { id := "trinhhaida2015_50"
    source := ⟨"trinh-haida-2015", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Detective A concluded that the robbers stole the book and not the jewelry. Detective B (only) concluded that they stole the book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: Detective B did not conclude that they stole the book and not the jewelry", .acceptable), ("inference: Detective B did not conclude that they stole the book and the jewelry", .acceptable)]
    paperFeatures := [("case", "apparent problem"), ("prejacent", "concluded book")] }

def ex_54 : Datum :=
  { id := "trinhhaida2015_54"
    source := ⟨"trinh-haida-2015", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The committee didn't pass all of my students."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: the committee passed some of my students", .acceptable)]
    paperFeatures := [("case", "indirect implicature"), ("prejacent", "not all")] }

def ex_56 : Datum :=
  { id := "trinhhaida2015_56"
    source := ⟨"trinh-haida-2015", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of my students did all of the readings."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: not [all of my students did some of the readings]", .unacceptable)]
    paperFeatures := [("case", "switching problem"), ("prejacent", "some all")] }

def ex_58 : Datum :=
  { id := "trinhhaida2015_58"
    source := ⟨"trinh-haida-2015", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of my students did all of the readings."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inference: all of my students did some of the readings", .acceptable)]
    paperFeatures := [("case", "switching problem"), ("prejacent", "not some all")] }

def all : List Datum := [ex_5, ex_6, ex_9, ex_10, ex_20b, ex_20c, ex_21a, ex_21b, ex_21c, ex_50, ex_54, ex_56, ex_58]

end TrinhHaida2015.Examples
