module

public import Linglib.Data.Examples.Schema

/-!
# `Rett2015a` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2015a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2015a.Examples`.
-/

@[expose] public section

namespace Rett2015a.Examples

def ex_3a : Datum :=
  { id := "rett2015a_3a"
    source := ⟨"rett-2015a", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids dove as deep as their parents did. Each parent dove 10m deep and their children dove 15m deep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_3b : Datum :=
  { id := "rett2015a_3b"
    source := ⟨"rett-2015a", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids dove as deep as their parents did. Each child dove 10m deep and their parents dove 15m deep."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_5a : Datum :=
  { id := "rett2015a_5a"
    source := ⟨"rett-2015a", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The divers dove as deep as 20m. For instance, Michael dove 25m."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_5b : Datum :=
  { id := "rett2015a_5b"
    source := ⟨"rett-2015a", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The divers dove as deep as 20m. For instance, Michael dove 15m."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11 : Datum :=
  { id := "rett2015a_11"
    source := ⟨"rett-2015a", "(11)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I'm 5′1″ and my husband is 6′2″. I've dated guys as short as 5′4″. Most of the guys I've dated have been relatively tall, though (5′10″ and up)."
    glossedTokens := []
    context := "The shortest man the speaker has dated was 5′4″."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11_odd : Datum :=
  { id := "rett2015a_11_odd"
    source := ⟨"rett-2015a", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm 5′1″ and my husband is 6′2″. I've dated guys as short as 5′4″. Most of the guys I've dated have been relatively tall, though (5′10″ and up)."
    glossedTokens := []
    context := "The shortest man the speaker has dated was 5′6″."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13a : Datum :=
  { id := "rett2015a_13a"
    source := ⟨"rett-2015a", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This camera is as heavy as the lens itself. In fact, it is heavier."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13b : Datum :=
  { id := "rett2015a_13b"
    source := ⟨"rett-2015a", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This camera is as heavy as the lens itself. In fact, it is lighter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20a : Datum :=
  { id := "rett2015a_20a"
    source := ⟨"rett-2015a", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is as tall as 5ft."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20b : Datum :=
  { id := "rett2015a_20b"
    source := ⟨"rett-2015a", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A hexagon has as many sides as 6."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20c : Datum :=
  { id := "rett2015a_20c"
    source := ⟨"rett-2015a", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This hamburger is as cheap as $40."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_20d : Datum :=
  { id := "rett2015a_20d"
    source := ⟨"rett-2015a", "(20d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue leaves her house as often as once a year."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21 : Datum :=
  { id := "rett2015a_21"
    source := ⟨"rett-2015a", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Watts Towers are as tall as 30m. They are in fact all 30m tall, which makes them very short towers indeed."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22a : Datum :=
  { id := "rett2015a_22a"
    source := ⟨"rett-2015a", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every linguist is as tall as 5ft."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22b : Datum :=
  { id := "rett2015a_22b"
    source := ⟨"rett-2015a", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All mature labradors are as heavy as 30lbs."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22c : Datum :=
  { id := "rett2015a_22c"
    source := ⟨"rett-2015a", "(22c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "All other classes can be as big as 40."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_23a : Datum :=
  { id := "rett2015a_23a"
    source := ⟨"rett-2015a", "(23a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Over 9000 holes must be drilled as deep as 30 feet for the anchors for the cabling."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_23b : Datum :=
  { id := "rett2015a_23b"
    source := ⟨"rett-2015a", "(23b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Mineral loss in bone must be as high as 30%–40% before any change is visible."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_81a : Datum :=
  { id := "rett2015a_81a"
    source := ⟨"rett-2015a", "(81a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Danny Gibbons is as tall as 6′3″. He is, in fact, 6′4″."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_81b : Datum :=
  { id := "rett2015a_81b"
    source := ⟨"rett-2015a", "(81b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Danny Gibbons is as tall as 6′3″. He is, in fact, 6′2″."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_86 : Datum :=
  { id := "rett2015a_86"
    source := ⟨"rett-2015a", "(86)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every linguist is as tall as 5ft."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_87 : Datum :=
  { id := "rett2015a_87"
    source := ⟨"rett-2015a", "(87)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John must be as tall as 5ft."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def T1S1 : Datum :=
  { id := "rett2015a_T1S1"
    source := ⟨"rett-2015a", "Table 1, S1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The linguists are as tall as 5ft."
    glossedTokens := []
    context := "Linguist 1 is 4ft tall, linguist 2 is 4ft tall, and linguist 3 is 4ft tall."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def T1S2 : Datum :=
  { id := "rett2015a_T1S2"
    source := ⟨"rett-2015a", "Table 1, S2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The linguists are as tall as 5ft."
    glossedTokens := []
    context := "Linguist 1 is 6ft tall, linguist 2 is 6ft tall, and linguist 3 is 6ft tall."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def T1S3 : Datum :=
  { id := "rett2015a_T1S3"
    source := ⟨"rett-2015a", "Table 1, S3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The linguists are as tall as 5ft."
    glossedTokens := []
    context := "Linguist 1 is 4ft tall, linguist 2 is 4½ft tall, and linguist 3 is 5ft tall."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def T1S4 : Datum :=
  { id := "rett2015a_T1S4"
    source := ⟨"rett-2015a", "Table 1, S4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The linguists are as tall as 5ft."
    glossedTokens := []
    context := "Linguist 1 is 5ft tall, linguist 2 is 5ft tall, and linguist 3 is 5ft tall."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def T1S5 : Datum :=
  { id := "rett2015a_T1S5"
    source := ⟨"rett-2015a", "Table 1, S5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The linguists are as tall as 5ft."
    glossedTokens := []
    context := "Linguist 1 is 4ft tall, linguist 2 is 5ft tall, and linguist 3 is 6ft tall."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_3a, ex_3b, ex_5a, ex_5b, ex_11, ex_11_odd, ex_13a, ex_13b, ex_20a, ex_20b, ex_20c, ex_20d, ex_21, ex_22a, ex_22b, ex_22c, ex_23a, ex_23b, ex_81a, ex_81b, ex_86, ex_87, T1S1, T1S2, T1S3, T1S4, T1S5]

end Rett2015a.Examples
