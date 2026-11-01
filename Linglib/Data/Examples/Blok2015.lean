module

public import Linglib.Data.Examples.Schema

/-!
# `Blok2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Blok2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Blok2015.Examples`.
-/

@[expose] public section

namespace Blok2015.Examples

def ex_3a : Datum :=
  { id := "blok2015_3a"
    source := ⟨"blok-2015", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most three students will show up to the lecture, if any."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "ifAny"), ("numeral", "3"), ("scaleBottom", "1")] }

def ex_3b : Datum :=
  { id := "blok2015_3b"
    source := ⟨"blok-2015", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Up to three students will show up to the lecture, if any."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "ifAny"), ("numeral", "3"), ("scaleBottom", "1")] }

def ex_4a : Datum :=
  { id := "blok2015_4a"
    source := ⟨"blok-2015", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I expect to see at most ten people, but maybe no-one will show up."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "butNone"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_4b : Datum :=
  { id := "blok2015_4b"
    source := ⟨"blok-2015", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I expect to see up to ten people, but maybe no-one will show up."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "butNone"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_7a : Datum :=
  { id := "blok2015_7a"
    source := ⟨"blok-2015", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most ten people died in the crash, perhaps even more."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "evenMore"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_7b : Datum :=
  { id := "blok2015_7b"
    source := ⟨"blok-2015", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Up to ten people died in the crash, perhaps even more."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "evenMore"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_11a : Datum :=
  { id := "blok2015_11a"
    source := ⟨"blok-2015", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're allowed to choose at most ten presents, but no more than that."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "noMore"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_11b : Datum :=
  { id := "blok2015_11b"
    source := ⟨"blok-2015", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're allowed to choose up to ten presents, but no more than that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "noMore"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_18b : Datum :=
  { id := "blok2015_18b"
    source := ⟨"blok-2015", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Stuart was absent for at most two weeks; ten days to be precise."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "precise"), ("numeral", "14"), ("precise", "10"), ("scaleBottom", "1")] }

def ex_19 : Datum :=
  { id := "blok2015_19"
    source := ⟨"blok-2015", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There will be up to 100 people at the party, 90 to be precise."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "precise"), ("numeral", "100"), ("precise", "90"), ("scaleBottom", "1")] }

def ex_22a : Datum :=
  { id := "blok2015_22a"
    source := ⟨"schwarz-buccola-hamilton-2012", "(21a)"⟩
    reportedIn := some ⟨"blok-2015", "(22a)"⟩
    language := "stan1293"
    primaryText := "At most ten people died in the crash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_22b : Datum :=
  { id := "blok2015_22b"
    source := ⟨"schwarz-buccola-hamilton-2012", "(22a)"⟩
    reportedIn := some ⟨"blok-2015", "(22b)"⟩
    language := "stan1293"
    primaryText := "At most one person died in the crash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "1"), ("scaleBottom", "1")] }

def ex_23a : Datum :=
  { id := "blok2015_23a"
    source := ⟨"schwarz-buccola-hamilton-2012", "(21b)"⟩
    reportedIn := some ⟨"blok-2015", "(23a)"⟩
    language := "stan1293"
    primaryText := "Up to ten people died in the crash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "range"), ("numeral", "10"), ("scaleBottom", "1")] }

def ex_23b : Datum :=
  { id := "blok2015_23b"
    source := ⟨"schwarz-buccola-hamilton-2012", "(22b)"⟩
    reportedIn := some ⟨"blok-2015", "(23b)"⟩
    language := "stan1293"
    primaryText := "Up to one person died in the crash."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "range"), ("numeral", "1"), ("scaleBottom", "1")] }

def ex_24a : Datum :=
  { id := "blok2015_24a"
    source := ⟨"schwarz-buccola-hamilton-2012", "(26a)"⟩
    reportedIn := some ⟨"blok-2015", "(24a)"⟩
    language := "stan1293"
    primaryText := "He bought at most a dozen eggs."
    glossedTokens := []
    context := "Eggs can be bought in half-dozen cartons only."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "12"), ("scaleBottom", "6")] }

def ex_24b : Datum :=
  { id := "blok2015_24b"
    source := ⟨"schwarz-buccola-hamilton-2012", "(27a)"⟩
    reportedIn := some ⟨"blok-2015", "(24b)"⟩
    language := "stan1293"
    primaryText := "He bought at most half a dozen eggs."
    glossedTokens := []
    context := "Eggs can be bought in half-dozen cartons only."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "6"), ("scaleBottom", "6")] }

def ex_25a : Datum :=
  { id := "blok2015_25a"
    source := ⟨"schwarz-buccola-hamilton-2012", "(26b)"⟩
    reportedIn := some ⟨"blok-2015", "(25a)"⟩
    language := "stan1293"
    primaryText := "He bought up to a dozen eggs."
    glossedTokens := []
    context := "Eggs can be bought in half-dozen cartons only."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "range"), ("numeral", "12"), ("scaleBottom", "6")] }

def ex_25b : Datum :=
  { id := "blok2015_25b"
    source := ⟨"schwarz-buccola-hamilton-2012", "(27b)"⟩
    reportedIn := some ⟨"blok-2015", "(25b)"⟩
    language := "stan1293"
    primaryText := "He bought up to half a dozen eggs."
    glossedTokens := []
    context := "Eggs can be bought in half-dozen cartons only."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "range"), ("numeral", "6"), ("scaleBottom", "6")] }

def ex_26a : Datum :=
  { id := "blok2015_26a"
    source := ⟨"blok-2015", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She bought at most one cake."
    glossedTokens := []
    context := "Cakes are sold per slice, with 12 slices in a cake."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "12"), ("scaleBottom", "1")] }

def ex_26b : Datum :=
  { id := "blok2015_26b"
    source := ⟨"blok-2015", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She bought at most one slice of cake."
    glossedTokens := []
    context := "Cakes are sold per slice, with 12 slices in a cake."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "1"), ("scaleBottom", "1")] }

def ex_27a : Datum :=
  { id := "blok2015_27a"
    source := ⟨"blok-2015", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She bought up to one cake."
    glossedTokens := []
    context := "Cakes are sold per slice, with 12 slices in a cake."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "range"), ("numeral", "12"), ("scaleBottom", "1")] }

def ex_27b : Datum :=
  { id := "blok2015_27b"
    source := ⟨"blok-2015", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She bought up to one slice of cake."
    glossedTokens := []
    context := "Cakes are sold per slice, with 12 slices in a cake."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "up to"), ("test", "range"), ("numeral", "1"), ("scaleBottom", "1")] }

def ex_29 : Datum :=
  { id := "blok2015_29"
    source := ⟨"blok-2015", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most 0 people died in the crash."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "at most"), ("test", "range"), ("numeral", "0"), ("scaleBottom", "1")] }

def ex_34a : Datum :=
  { id := "blok2015_34a"
    source := ⟨"blok-2015", "(34a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Er hoeven maximaal vijf studenten te komen."
    glossedTokens := [("Er", "there"), ("hoeven", "must-NPI"), ("maximaal", "maximally"), ("vijf", "five"), ("studenten", "students"), ("te", "to"), ("komen", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "maximaal"), ("test", "npi"), ("npi", "hoeven"), ("numeral", "5"), ("scaleBottom", "1")] }

def ex_34b : Datum :=
  { id := "blok2015_34b"
    source := ⟨"blok-2015", "(34b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Er hoeven tot vijf studenten te komen."
    glossedTokens := [("Er", "there"), ("hoeven", "must-NPI"), ("tot", "TOT"), ("vijf", "five"), ("studenten", "students"), ("te", "to"), ("komen", "come")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "tot"), ("test", "npi"), ("npi", "hoeven"), ("numeral", "5"), ("scaleBottom", "1")] }

def all : List Datum := [ex_3a, ex_3b, ex_4a, ex_4b, ex_7a, ex_7b, ex_11a, ex_11b, ex_18b, ex_19, ex_22a, ex_22b, ex_23a, ex_23b, ex_24a, ex_24b, ex_25a, ex_25b, ex_26a, ex_26b, ex_27a, ex_27b, ex_29, ex_34a, ex_34b]

end Blok2015.Examples
