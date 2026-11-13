module

public import Linglib.Data.Examples.Schema

/-!
# `Romoli2013b` — typed example data

Auto-generated from `Linglib/Data/Examples/Romoli2013b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Romoli2013b.Examples`.
-/

@[expose] public section

namespace Romoli2013b.Examples

def ex_112a : Datum :=
  { id := "romoli2013b_112a"
    source := ⟨"romoli-2013b", "(112a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't think that Mary will arrive until tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_112b : Datum :=
  { id := "romoli2013b_112b"
    source := ⟨"romoli-2013b", "(112b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John isn't certain that Mary will arrive until tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_115 : Datum :=
  { id := "romoli2013b_115"
    source := ⟨"romoli-2013b", "(115)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't think that Bill would leave until tomorrow"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_117a : Datum :=
  { id := "romoli2013b_117a"
    source := ⟨"romoli-2013b", "(117a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student who left until his birthday missed many classes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_117b : Datum :=
  { id := "romoli2013b_117b"
    source := ⟨"romoli-2013b", "(117b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student who has seen Mary in weeks is upset with her."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_118 : Datum :=
  { id := "romoli2013b_118"
    source := ⟨"romoli-2013b", "(118)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't leave until Thursday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_119 : Datum :=
  { id := "romoli2013b_119"
    source := ⟨"romoli-2013b", "(119)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student who left until Thursday, missed the class on presuppositions."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_128 : Datum :=
  { id := "romoli2013b_128"
    source := ⟨"romoli-2013b", "(128)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Robin won't be here until six o' clock."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_129 : Datum :=
  { id := "romoli2013b_129"
    source := ⟨"romoli-2013b", "(129)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that Robin will be here until six o' clock."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_130 : Datum :=
  { id := "romoli2013b_130"
    source := ⟨"romoli-2013b", "(130)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leslie doesn't believe that Robin will be here until six o' clock."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_131 : Datum :=
  { id := "romoli2013b_131"
    source := ⟨"romoli-2013b", "(131)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leslie doesn't believe that it's true that Robin will be here until six o' clock."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_160 : Datum :=
  { id := "romoli2013b_160"
    source := ⟨"romoli-2013b", "(160)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student thought that Mary would leave until tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_112a, ex_112b, ex_115, ex_117a, ex_117b, ex_118, ex_119, ex_128, ex_129, ex_130, ex_131, ex_160]

end Romoli2013b.Examples
