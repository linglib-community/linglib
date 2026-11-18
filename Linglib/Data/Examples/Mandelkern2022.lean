module

public import Linglib.Data.Examples.Schema

/-!
# `Mandelkern2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Mandelkern2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Mandelkern2022.Examples`.
-/

@[expose] public section

namespace Mandelkern2022.Examples

def ex_1a : Datum :=
  { id := "mandelkern2022_1a"
    source := ⟨"mandelkern-2022", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has a child loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("them covaries with a child", .acceptable)]
    paperFeatures := [("section", "1")] }

def ex_1b : Datum :=
  { id := "mandelkern2022_1b"
    source := ⟨"mandelkern-2022", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who is a parent loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("them covaries with the parents' children", .marginal), ("them is some salient person", .acceptable)]
    paperFeatures := [("section", "1")] }

def ex_2a : Datum :=
  { id := "mandelkern2022_2a"
    source := ⟨"mandelkern-2022", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue has a child. She is at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .acceptable)]
    paperFeatures := [("section", "2")] }

def ex_2b : Datum :=
  { id := "mandelkern2022_2b"
    source := ⟨"mandelkern-2022", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is a parent. She is at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .marginal), ("she is Sue", .acceptable)]
    paperFeatures := [("section", "2")] }

def ex_3a : Datum :=
  { id := "mandelkern2022_3a"
    source := ⟨"mandelkern-2022", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue has a twin. She lives in Dubuque."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's twin", .acceptable)]
    paperFeatures := [("section", "2")] }

def ex_3b : Datum :=
  { id := "mandelkern2022_3b"
    source := ⟨"mandelkern-2022", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is a twin. She lives in Dubuque."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue", .acceptable)]
    paperFeatures := [("section", "2")] }

def ex_4a : Datum :=
  { id := "mandelkern2022_4a"
    source := ⟨"mandelkern-2022", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has a child loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Everyone who has a child loves the child.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2")] }

def ex_4b : Datum :=
  { id := "mandelkern2022_4b"
    source := ⟨"mandelkern-2022", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who is a parent loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Everyone who is a parent loves the child.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2")] }

def ex_5a : Datum :=
  { id := "mandelkern2022_5a"
    source := ⟨"mandelkern-2022", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has a twin loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Everyone who has a twin loves the twin.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2")] }

def ex_5b : Datum :=
  { id := "mandelkern2022_5b"
    source := ⟨"mandelkern-2022", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who is a twin loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Everyone who is a twin loves the twin.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2")] }

def ex_7 : Datum :=
  { id := "mandelkern2022_7"
    source := ⟨"mandelkern-2022", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has a child loves the child."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex_8 : Datum :=
  { id := "mandelkern2022_8"
    source := ⟨"mandelkern-2022", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who bought a sage plant bought seven others along with the sage plant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex_9a : Datum :=
  { id := "mandelkern2022_9a"
    source := ⟨"mandelkern-2022", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue has a child and she is at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3")] }

def ex_9b : Datum :=
  { id := "mandelkern2022_9b"
    source := ⟨"mandelkern-2022", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is a parent and she is at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3")] }

def ex_12a : Datum :=
  { id := "mandelkern2022_12a"
    source := ⟨"mandelkern-2022", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that Sue doesn't have a child. She's at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .acceptable)]
    paperFeatures := [("section", "4")] }

def ex_12b : Datum :=
  { id := "mandelkern2022_12b"
    source := ⟨"mandelkern-2022", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that Sue isn't a parent. She's at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .marginal), ("she is Sue", .acceptable)]
    paperFeatures := [("section", "4")] }

def ex_13a : Datum :=
  { id := "mandelkern2022_13a"
    source := ⟨"mandelkern-2022", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue doesn't have a child. That's not true! She's at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .acceptable)]
    paperFeatures := [("section", "4")] }

def ex_13b : Datum :=
  { id := "mandelkern2022_13b"
    source := ⟨"mandelkern-2022", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue isn't a parent. That's not true! She's at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .marginal), ("she is Sue", .acceptable)]
    paperFeatures := [("section", "4")] }

def ex_14a : Datum :=
  { id := "mandelkern2022_14a"
    source := ⟨"mandelkern-2022", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Sue doesn't have a child, or she's at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .acceptable)]
    paperFeatures := [("section", "4")] }

def ex_14b : Datum :=
  { id := "mandelkern2022_14b"
    source := ⟨"mandelkern-2022", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Sue isn't a parent, or she's at boarding school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("she is Sue's child", .marginal)]
    paperFeatures := [("section", "4")] }

def ex_15a : Datum :=
  { id := "mandelkern2022_15a"
    source := ⟨"mandelkern-2022", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man came in and he sat down."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he is the man", .acceptable)]
    paperFeatures := [("section", "5.5")] }

def ex_15b : Datum :=
  { id := "mandelkern2022_15b"
    source := ⟨"mandelkern-2022", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He sat down and a man came in."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he is the man", .questionable)]
    paperFeatures := [("section", "5.5")] }

def ex_16a : Datum :=
  { id := "mandelkern2022_16a"
    source := ⟨"mandelkern-2022", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either there isn't a bathroom, or it is upstairs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Either there isn't a bathroom, or the bathroom is upstairs.", .acceptable)]
    readings := [("it is the bathroom", .acceptable)]
    paperFeatures := [("section", "5.5")] }

def ex_16b : Datum :=
  { id := "mandelkern2022_16b"
    source := ⟨"mandelkern-2022", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either it is upstairs, or there isn't a bathroom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Either the bathroom is upstairs, or there isn't a bathroom.", .acceptable)]
    readings := [("it is the bathroom", .acceptable)]
    paperFeatures := [("section", "5.5")] }

def ex_17a : Datum :=
  { id := "mandelkern2022_17a"
    source := ⟨"mandelkern-2022", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either she is at boarding school, or Susie doesn't have a child."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Either the child is at boarding school, or Susie doesn't have a child.", .acceptable)]
    readings := [("she is Susie's child", .acceptable)]
    paperFeatures := [("section", "5.5")] }

def ex_17b : Datum :=
  { id := "mandelkern2022_17b"
    source := ⟨"mandelkern-2022", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either she is at boarding school, or Susie isn't a parent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Either the child is at boarding school, or Susie isn't a parent.", .acceptable)]
    readings := [("she is Susie's child", .marginal)]
    paperFeatures := [("section", "5.5")] }

def ex_18a : Datum :=
  { id := "mandelkern2022_18a"
    source := ⟨"mandelkern-2022", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It took him a long time, but a student of mine wrote a really good paper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("him is the student", .acceptable)]
    paperFeatures := [("section", "5.5")] }

def ex_18b : Datum :=
  { id := "mandelkern2022_18b"
    source := ⟨"mandelkern-2022", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He complained all the way to the fair, and then one of my kids just disappeared."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("he is the kid", .acceptable)]
    paperFeatures := [("section", "5.5")] }

def ex_19 : Datum :=
  { id := "mandelkern2022_19"
    source := ⟨"mandelkern-2022", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We don't have a cat. She is a tabby."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.5")] }

def ex_21a : Datum :=
  { id := "mandelkern2022_21a"
    source := ⟨"mandelkern-2022", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has a child loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Everyone who has a child loves the child.", .acceptable)]
    readings := [("them covaries with a child", .acceptable)]
    paperFeatures := [("section", "5.8")] }

def ex_21b : Datum :=
  { id := "mandelkern2022_21b"
    source := ⟨"mandelkern-2022", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every parent loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Every parent loves the child.", .acceptable)]
    readings := [("them covaries with the parents' children", .unacceptable)]
    paperFeatures := [("section", "5.8")] }

def ex_22a : Datum :=
  { id := "mandelkern2022_22a"
    source := ⟨"mandelkern-2022", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who has a child loves them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.8")] }

def ex_23 : Datum :=
  { id := "mandelkern2022_23"
    source := ⟨"mandelkern-2022", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue doesn't have a child. You would know them by now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex_24 : Datum :=
  { id := "mandelkern2022_24"
    source := ⟨"mandelkern-2022", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't have a car so he doesn't wash it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("John doesn't have a car so he doesn't wash the car.", .acceptable)]
    readings := []
    paperFeatures := [("section", "6"), ("footnote", "26")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b, ex_5a, ex_5b, ex_7, ex_8, ex_9a, ex_9b, ex_12a, ex_12b, ex_13a, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17a, ex_17b, ex_18a, ex_18b, ex_19, ex_21a, ex_21b, ex_22a, ex_23, ex_24]

end Mandelkern2022.Examples
