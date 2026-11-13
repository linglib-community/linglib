module

public import Linglib.Data.Examples.Schema

/-!
# `Heim1994b` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1994b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1994b.Examples`.
-/

@[expose] public section

namespace Heim1994b.Examples

def ex1_exhaustive : Datum :=
  { id := "heim1994b_ex1_exhaustive"
    source := ⟨"heim-1994", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students called."
    glossedTokens := []
    context := "Student Mary did not call, and John is agnostic as to whether she called; of every student who called he believes that they called."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex1_dedicto : Datum :=
  { id := "heim1994b_ex1_dedicto"
    source := ⟨"heim-1994", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students called."
    glossedTokens := []
    context := "Mary is a student who called; John knows exactly who called but does not know that Mary is a student."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("reading", "de dicto")] }

def ex6 : Datum :=
  { id := "heim1994b_ex6"
    source := ⟨"heim-1994", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who called."
    glossedTokens := []
    context := "Mary is a student who called; John knows exactly who called but does not know that Mary is a student."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("section", "3")] }

def ex17 : Datum :=
  { id := "heim1994b_ex17"
    source := ⟨"heim-1994", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows the answer to the question which students called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex18 : Datum :=
  { id := "heim1994b_ex18"
    source := ⟨"heim-1994", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows that Bill and Sue called. That Bill and Sue called happens to be the answer to the question which students called. So John knows the answer to the question which students called."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex19 : Datum :=
  { id := "heim1994b_ex19"
    source := ⟨"heim-1994", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't find your house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex20a : Datum :=
  { id := "heim1994b_ex20a"
    source := ⟨"heim-1994", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I identified the culprit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex20b : Datum :=
  { id := "heim1994b_ex20b"
    source := ⟨"heim-1994", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I identified the striped animal in your drawing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")] }

def ex21 : Datum :=
  { id := "heim1994b_ex21"
    source := ⟨"heim-1994", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students are identical with themselves."
    glossedTokens := []
    context := "Any, even one where John has no idea who, if anyone, is a student."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("section", "7")] }

def ex24 : Datum :=
  { id := "heim1994b_ex24"
    source := ⟨"heim-1994", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students live with their actual spouses."
    glossedTokens := []
    context := "Bill is married to Sue; both are students and live with each other, and no other students live with their spouses. John is well informed about these facts, except that he falsely believes Sue not to be a student."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("section", "7")] }

def fn8ii : Datum :=
  { id := "heim1994b_fn8ii"
    source := ⟨"heim-1994", "fn. 8 (ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Feynman knew which elementary particles had been discovered by 1978, but he didn't know which ones hadn't been."
    glossedTokens := []
    context := "Of exactly two elementary particles only one had been discovered by 1978; Feynman's beliefs in 1978 are compatible with the actual world and with one where the discovered particle is the only elementary particle and the only one discovered."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def all : List Datum := [ex1_exhaustive, ex1_dedicto, ex6, ex17, ex18, ex19, ex20a, ex20b, ex21, ex24, fn8ii]

end Heim1994b.Examples
