module

public import Linglib.Data.Examples.Schema

/-!
# `BonehDoron2013` — typed example data

Auto-generated from `Linglib/Data/Examples/BonehDoron2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BonehDoron2013.Examples`.
-/

@[expose] public section

namespace BonehDoron2013.Examples

def ex2c : Datum :=
  { id := "bonehdoron2013_ex2c"
    source := ⟨"boneh-doron-2013", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the good old days, people would dress elegantly."
    glossedTokens := []
    context := "(At the opera). Look at how sloppily people are dressed."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "would")] }

def ex2d : Datum :=
  { id := "bonehdoron2013_ex2d"
    source := ⟨"boneh-doron-2013", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the good old days, people would dress elegantly to go to the opera."
    glossedTokens := []
    context := "(At the opera). Look at how sloppily people are dressed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "would")] }

def ex4a : Datum :=
  { id := "bonehdoron2013_ex4a"
    source := ⟨"boneh-doron-2013", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary smokes a cigarette after dinner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple")] }

def ex4b : Datum :=
  { id := "bonehdoron2013_ex4b"
    source := ⟨"boneh-doron-2013", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary smokes a cigarette."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple")] }

def ex6b : Datum :=
  { id := "bonehdoron2013_ex6b"
    source := ⟨"boneh-doron-2013", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A flower grows out behind the old shed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple")] }

def ex7b : Datum :=
  { id := "bonehdoron2013_ex7b"
    source := ⟨"boneh-doron-2013", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max killed a rabbit repeatedly."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple")] }

def ex30 : Datum :=
  { id := "bonehdoron2013_ex30"
    source := ⟨"boneh-doron-2013", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "... revivals of Broadway musicals that your parents used to go to. Still do."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo")] }

def ex33a : Datum :=
  { id := "bonehdoron2013_ex33a"
    source := ⟨"boneh-doron-2013", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since then, she has gone to work by bus."
    glossedTokens := []
    context := "Ruti sold her car in 1990."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "perfect")] }

def ex33b : Datum :=
  { id := "bonehdoron2013_ex33b"
    source := ⟨"boneh-doron-2013", "(33b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since then, she used to go to work by bus."
    glossedTokens := []
    context := "Ruti sold her car in 1990."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo")] }

def ex35a : Datum :=
  { id := "bonehdoron2013_ex35a"
    source := ⟨"boneh-doron-2013", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was very happy. She now went to work by bus."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple")] }

def ex35b : Datum :=
  { id := "bonehdoron2013_ex35b"
    source := ⟨"boneh-doron-2013", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was very happy. She now used to go to work by bus."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo")] }

def ex42a : Datum :=
  { id := "bonehdoron2013_ex42a"
    source := ⟨"boneh-doron-2013", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruti was such a modest person. She went to work by bus."
    glossedTokens := []
    context := "Ruti started a new job. She decided to go to work by bus. She only went there once, and shortly after that she died. In a eulogy, one could say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple"), ("truthValue", "true")] }

def ex42b : Datum :=
  { id := "bonehdoron2013_ex42b"
    source := ⟨"boneh-doron-2013", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruti was such a modest person. She would go to work by bus."
    glossedTokens := []
    context := "Ruti started a new job. She decided to go to work by bus. She only went there once, and shortly after that she died. In a eulogy, one could say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "would"), ("truthValue", "true")] }

def ex42c : Datum :=
  { id := "bonehdoron2013_ex42c"
    source := ⟨"boneh-doron-2013", "(42c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruti was such a modest person. She used to go to work by bus."
    glossedTokens := []
    context := "Ruti started a new job. She decided to go to work by bus. She only went there once, and shortly after that she died. In a eulogy, one could say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo"), ("truthValue", "false")] }

def ex47a_barePlural : Datum :=
  { id := "bonehdoron2013_ex47a_barePlural"
    source := ⟨"boneh-doron-2013", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the nineteenth century, French teachers would know Latin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "would"), ("subject", "barePlural")] }

def ex47a_indefinite : Datum :=
  { id := "bonehdoron2013_ex47a_indefinite"
    source := ⟨"boneh-doron-2013", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the nineteenth century, a French teacher would know Latin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "would"), ("subject", "indefiniteSingular")] }

def ex47b_barePlural : Datum :=
  { id := "bonehdoron2013_ex47b_barePlural"
    source := ⟨"boneh-doron-2013", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the nineteenth century, French teachers used to know Latin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo"), ("subject", "barePlural")] }

def ex47b_indefinite : Datum :=
  { id := "bonehdoron2013_ex47b_indefinite"
    source := ⟨"boneh-doron-2013", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the nineteenth century, a French teacher used to know Latin."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo"), ("subject", "indefiniteSingular")] }

def ex48a : Datum :=
  { id := "bonehdoron2013_ex48a"
    source := ⟨"boneh-doron-2013", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The London Bridge used to stand on the Thames, now it stands in Arizona."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "usedTo")] }

def ex48b : Datum :=
  { id := "bonehdoron2013_ex48b"
    source := ⟨"boneh-doron-2013", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The London Bridge would stand on the Thames, now it stands in Arizona."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "would")] }

def all : List Datum := [ex2c, ex2d, ex4a, ex4b, ex6b, ex7b, ex30, ex33a, ex33b, ex35a, ex35b, ex42a, ex42b, ex42c, ex47a_barePlural, ex47a_indefinite, ex47b_barePlural, ex47b_indefinite, ex48a, ex48b]

end BonehDoron2013.Examples
