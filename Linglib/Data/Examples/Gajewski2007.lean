module

public import Linglib.Data.Examples.Schema

/-!
# `Gajewski2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Gajewski2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gajewski2007.Examples`.
-/

@[expose] public section

namespace Gajewski2007.Examples

def ex_12a : Datum :=
  { id := "gajewski2007_12a"
    source := ⟨"gajewski-2007", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary left until yesterday"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "gajewski2007_12b"
    source := ⟨"gajewski-2007", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't leave until yesterday"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13a : Datum :=
  { id := "gajewski2007_13a"
    source := ⟨"gajewski-2007", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill has left the country in (at least two) years"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13b : Datum :=
  { id := "gajewski2007_13b"
    source := ⟨"gajewski-2007", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill hasn't left the country in (at least two) years"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "gajewski2007_14a"
    source := ⟨"gajewski-2007", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill didn't claim that Mary would arrive until tomorrow"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "gajewski2007_14b"
    source := ⟨"gajewski-2007", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't claim that Bill had left the country in years"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_15a : Datum :=
  { id := "gajewski2007_15a"
    source := ⟨"gajewski-2007", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill doesn't think Mary will leave until tomorrow"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_15b : Datum :=
  { id := "gajewski2007_15b"
    source := ⟨"gajewski-2007", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't believe Bill has left the country in years"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_54a : Datum :=
  { id := "gajewski2007_54a"
    source := ⟨"gajewski-2007", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not a single student has visited in years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_54b : Datum :=
  { id := "gajewski2007_54b"
    source := ⟨"gajewski-2007", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every student has visited in years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_57 : Datum :=
  { id := "gajewski2007_57"
    source := ⟨"gajewski-2007", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't think Mary left until five."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_58a : Datum :=
  { id := "gajewski2007_58a"
    source := ⟨"gajewski-2007", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill doesn't think Sue has visited in years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_58b : Datum :=
  { id := "gajewski2007_58b"
    source := ⟨"gajewski-2007", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill doesn't know that Sue has visited in years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_68a : Datum :=
  { id := "gajewski2007_68a"
    source := ⟨"gajewski-2007", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every student arrived until 5 o'clock."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_68b : Datum :=
  { id := "gajewski2007_68b"
    source := ⟨"gajewski-2007", "(68b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not a single student arrived until 5 o'clock."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_69a : Datum :=
  { id := "gajewski2007_69a"
    source := ⟨"gajewski-2007", "(69a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every student has visited Bill in (at least two) years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_69b : Datum :=
  { id := "gajewski2007_69b"
    source := ⟨"gajewski-2007", "(69b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not a single student has visited Bill in (at least two) years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_71a : Datum :=
  { id := "gajewski2007_71a"
    source := ⟨"gajewski-2007", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An applicant is not allowed to have left the country in at least 2 years"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_71b : Datum :=
  { id := "gajewski2007_71b"
    source := ⟨"gajewski-2007", "(71b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An applicant can't have left the country in at least 2 years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_72a : Datum :=
  { id := "gajewski2007_72a"
    source := ⟨"gajewski-2007", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An applicant is not required to have left the country in at least 2 years"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_72b : Datum :=
  { id := "gajewski2007_72b"
    source := ⟨"gajewski-2007", "(72b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An applicant doesn't have to have left the country in at least 2 years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_73 : Datum :=
  { id := "gajewski2007_73"
    source := ⟨"gajewski-2007", "(73)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not certain that Bill has left the country in at least 2 years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_74 : Datum :=
  { id := "gajewski2007_74"
    source := ⟨"gajewski-2007", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not possible that Bill has left the country in at least 2 years."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_83 : Datum :=
  { id := "gajewski2007_83"
    source := ⟨"gajewski-2007", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No one thought Bill would leave until tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_97a : Datum :=
  { id := "gajewski2007_97a"
    source := ⟨"gajewski-2007", "(97a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't believe John wanted Harry to die until tomorrow"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_97b : Datum :=
  { id := "gajewski2007_97b"
    source := ⟨"gajewski-2007", "(97b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't want John to believe Harry died until yesterday"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_98a : Datum :=
  { id := "gajewski2007_98a"
    source := ⟨"gajewski-2007", "(98a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't think Bill should have left until yesterday"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_98b : Datum :=
  { id := "gajewski2007_98b"
    source := ⟨"gajewski-2007", "(98b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary shouldn't think Bill left until yesterday"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_99a : Datum :=
  { id := "gajewski2007_99a"
    source := ⟨"gajewski-2007", "(99a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill doesn't imagine Sue ought to have left until yesterday"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_99b : Datum :=
  { id := "gajewski2007_99b"
    source := ⟨"gajewski-2007", "(99b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill ought not imagine Sue left until yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_123a : Datum :=
  { id := "gajewski2007_123a"
    source := ⟨"gajewski-2007", "(123a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John arrived until 5 o'clock."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_123b : Datum :=
  { id := "gajewski2007_123b"
    source := ⟨"gajewski-2007", "(123b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John has visited Mary in years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_123c : Datum :=
  { id := "gajewski2007_123c"
    source := ⟨"gajewski-2007", "(123c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John likes waffles either."
    glossedTokens := []
    context := "Only John likes pancakes."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_126a : Datum :=
  { id := "gajewski2007_126a"
    source := ⟨"gajewski-2007", "(126)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is sorry that Bill arrived until five"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_126b : Datum :=
  { id := "gajewski2007_126b"
    source := ⟨"gajewski-2007", "(126)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is sorry that Bill has visited John in years"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_127a : Datum :=
  { id := "gajewski2007_127a"
    source := ⟨"gajewski-2007", "(127)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill arrived until five, Mary was upset."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_127b : Datum :=
  { id := "gajewski2007_127b"
    source := ⟨"gajewski-2007", "(127)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Sue has visited Bill in years, then Mary is upset."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_132a : Datum :=
  { id := "gajewski2007_132a"
    source := ⟨"gajewski-2007", "(132a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Erin is the tallest girl John has seen in years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_132b : Datum :=
  { id := "gajewski2007_132b"
    source := ⟨"gajewski-2007", "(132b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tallest girl John had seen until Friday walked in the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def fn7ii : Datum :=
  { id := "gajewski2007_fn7ii"
    source := ⟨"gajewski-2007", "fn. 7 (ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I DON'T think Bill has visited in years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_12a, ex_12b, ex_13a, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_54a, ex_54b, ex_57, ex_58a, ex_58b, ex_68a, ex_68b, ex_69a, ex_69b, ex_71a, ex_71b, ex_72a, ex_72b, ex_73, ex_74, ex_83, ex_97a, ex_97b, ex_98a, ex_98b, ex_99a, ex_99b, ex_123a, ex_123b, ex_123c, ex_126a, ex_126b, ex_127a, ex_127b, ex_132a, ex_132b, fn7ii]

end Gajewski2007.Examples
