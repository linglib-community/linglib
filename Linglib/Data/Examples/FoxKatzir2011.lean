module

public import Linglib.Data.Examples.Schema

/-!
# `FoxKatzir2011` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxKatzir2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxKatzir2011.Examples`.
-/

@[expose] public section

namespace FoxKatzir2011.Examples

def ex1 : Datum :=
  { id := "foxkatzir2011_ex1"
    source := ⟨"fox-katzir-2011", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John did all of the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")] }

def ex2 : Datum :=
  { id := "foxkatzir2011_ex2"
    source := ⟨"fox-katzir-2011", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did the reading or the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John did the reading and the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")] }

def ex3 : Datum :=
  { id := "foxkatzir2011_ex3"
    source := ⟨"fox-katzir-2011", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has three children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John has four children", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")] }

def ex29 : Datum :=
  { id := "foxkatzir2011_ex29"
    source := ⟨"fox-katzir-2011", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only [read three books]F."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John read four books", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "no"), ("universal", "no"), ("compatible", "no")] }

def ex33 : Datum :=
  { id := "foxkatzir2011_ex33"
    source := ⟨"fox-katzir-2011", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only [read three books]F."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John read exactly three books", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")] }

def ex38 : Datum :=
  { id := "foxkatzir2011_ex38"
    source := ⟨"fox-katzir-2011", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did all of the homework or none of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John did all of the homework", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")] }

def ex40 : Datum :=
  { id := "foxkatzir2011_ex40"
    source := ⟨"fox-katzir-2011", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is determined to do all of the homework or none of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John is determined to do all of the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")] }

def ex41 : Datum :=
  { id := "foxkatzir2011_ex41"
    source := ⟨"fox-katzir-2011", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each of my students did all of the homework or none of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: Each of my students did all of the homework", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")] }

def ex42a : Datum :=
  { id := "foxkatzir2011_ex42a"
    source := ⟨"fox-katzir-2011", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some of the homework yesterday, and he did just some of the homework today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John did just some of the homework yesterday", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")] }

def ex44 : Datum :=
  { id := "foxkatzir2011_ex44"
    source := ⟨"fox-katzir-2011", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was required to do some of the homework yesterday, and he was required to do just some of the homework today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: John was required to do just some of the homework yesterday", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")] }

def ex46 : Datum :=
  { id := "foxkatzir2011_ex46"
    source := ⟨"fox-katzir-2011", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last week I gave an exam to the third graders, who are a highly motivated bunch, and I was very happy to learn that every single student (even the weakest of them all) got some of the questions right. Today I gave an exam to the fifth graders, who are all very talented. I was disappointed to learn that this time every single student got just some of the questions right."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: Last week, every student got just some of the questions right", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")] }

def ex47a : Datum :=
  { id := "foxkatzir2011_ex47a"
    source := ⟨"fox-katzir-2011", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In last week's robbery they only [stole the books]F. In today's robbery they [stole the books but not the jewelry]F."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: In last week's robbery they stole the books but not the jewelry", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "yes"), ("universal", "no"), ("compatible", "no")] }

def ex49a : Datum :=
  { id := "foxkatzir2011_ex49a"
    source := ⟨"fox-katzir-2011", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Detective A only concluded that the robbers [stole the books]F. Detective B concluded that the robbers [stole the books but not the jewelry]F."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: Detective A concluded that the robbers stole the books but not the jewelry", .acceptable)]
    paperFeatures := [("inference", "yes"), ("symmetric", "yes"), ("universal", "yes"), ("compatible", "no")] }

def ex53 : Datum :=
  { id := "foxkatzir2011_ex53"
    source := ⟨"fox-katzir-2011", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John talked to Mary or Sue, and today, John talked to Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not: Yesterday, John talked to Mary", .unacceptable)]
    paperFeatures := [("inference", "no"), ("symmetric", "no"), ("universal", "no"), ("compatible", "yes")] }

def all : List Datum := [ex1, ex2, ex3, ex29, ex33, ex38, ex40, ex41, ex42a, ex44, ex46, ex47a, ex49a, ex53]

end FoxKatzir2011.Examples
