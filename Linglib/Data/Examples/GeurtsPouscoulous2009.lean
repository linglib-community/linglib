module

public import Linglib.Data.Examples.Schema

/-!
# `GeurtsPouscoulous2009` — typed example data

Auto-generated from `Linglib/Data/Examples/GeurtsPouscoulous2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GeurtsPouscoulous2009.Examples`.
-/

@[expose] public section

namespace GeurtsPouscoulous2009.Examples

def t1_simple : Datum :=
  { id := "geurtspouscoulous2009_t1_simple"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 ∅"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Fred heard some of the Verdi operas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "simple"), ("rate1a", "93"), ("rate1b", "94")] }

def t1_all : Datum :=
  { id := "geurtspouscoulous2009_t1_all"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 all"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "All students heard some of the Verdi operas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "all"), ("rate1a", "27"), ("rate1b", "none")] }

def t1_must : Datum :=
  { id := "geurtspouscoulous2009_t1_must"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 must"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Fred has to hear some of the Verdi operas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "must"), ("rate1a", "3"), ("rate1b", "none")] }

def t1_think : Datum :=
  { id := "geurtspouscoulous2009_t1_think"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 think"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Betty thinks Fred heard some of the Verdi operas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "think"), ("rate1a", "50"), ("rate1b", "65")] }

def t1_want : Datum :=
  { id := "geurtspouscoulous2009_t1_want"
    source := ⟨"geurts-pouscoulous-2009", "Table 1 want"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Betty wants Fred to hear some of the Verdi operas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("embedding", "want"), ("rate1a", "none"), ("rate1b", "32")] }

def ex24 : Datum :=
  { id := "geurtspouscoulous2009_ex24"
    source := ⟨"geurts-pouscoulous-2009", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of the B's are in the box on the left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("embedding", "simple"), ("inferenceRate", "62"), ("verificationRate", "34")] }

def ex26a : Datum :=
  { id := "geurtspouscoulous2009_ex26a"
    source := ⟨"geurts-pouscoulous-2009", "(26a)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "All the squares are connected with some of the circles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "all"), ("trial", "none"), ("verificationRate", "100"), ("predictedRate", "0"), ("inferenceRate", "46"), ("exp4Yes", "95"), ("exp4No", "5"), ("exp4Both", "0")] }

def ex26b : Datum :=
  { id := "geurtspouscoulous2009_ex26b"
    source := ⟨"geurts-pouscoulous-2009", "(26b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "There is more than one square that is connected with some of the circles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "moreThanOne"), ("trial", "none"), ("verificationRate", "100"), ("predictedRate", "0"), ("inferenceRate", "62"), ("exp4Yes", "100"), ("exp4No", "0"), ("exp4Both", "0")] }

def ex27_a : Datum :=
  { id := "geurtspouscoulous2009_ex27_a"
    source := ⟨"geurts-pouscoulous-2009", "(27)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "There are exactly two squares that are connected with some of the circles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "exactlyTwo"), ("trial", "A"), ("verificationRate", "100"), ("predictedRate", "0"), ("inferenceRate", "50"), ("exp4Yes", "86"), ("exp4No", "5"), ("exp4Both", "9")] }

def ex27_b : Datum :=
  { id := "geurtspouscoulous2009_ex27_b"
    source := ⟨"geurts-pouscoulous-2009", "(27)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "There are exactly two squares that are connected with some of the circles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "exactlyTwo"), ("trial", "B"), ("verificationRate", "0"), ("predictedRate", "100"), ("inferenceRate", "50"), ("exp4Yes", "9"), ("exp4No", "77"), ("exp4Both", "14")] }

def ex25a : Datum :=
  { id := "geurtspouscoulous2009_ex25a"
    source := ⟨"geurts-pouscoulous-2009", "(25a)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Not all the squares are connected with some of the circles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "notAll"), ("trial", "none"), ("verificationRate", "4"), ("predictedRate", "0"), ("inferenceRate", "58"), ("exp4Yes", "9"), ("exp4No", "86"), ("exp4Both", "5")] }

def ex25b : Datum :=
  { id := "geurtspouscoulous2009_ex25b"
    source := ⟨"geurts-pouscoulous-2009", "(25b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "There isn't more than one square that is connected with some of the circles."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("quantifier", "notMoreThanOne"), ("trial", "none"), ("verificationRate", "4"), ("predictedRate", "0"), ("inferenceRate", "46"), ("exp4Yes", "9"), ("exp4No", "91"), ("exp4Both", "0")] }

def ex29a : Datum :=
  { id := "geurtspouscoulous2009_ex29a"
    source := ⟨"geurts-pouscoulous-2009", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The circles and the squares are connected with each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "82")] }

def ex29b : Datum :=
  { id := "geurtspouscoulous2009_ex29b"
    source := ⟨"geurts-pouscoulous-2009", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The green and the orange figures are connected with each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "73")] }

def ex29c : Datum :=
  { id := "geurtspouscoulous2009_ex29c"
    source := ⟨"geurts-pouscoulous-2009", "(29c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the figures are orange and green."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "59")] }

def ex29d : Datum :=
  { id := "geurtspouscoulous2009_ex29d"
    source := ⟨"geurts-pouscoulous-2009", "(29d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are green circles and squares."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "77")] }

def ex29e : Datum :=
  { id := "geurtspouscoulous2009_ex29e"
    source := ⟨"geurts-pouscoulous-2009", "(29e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The circles and the squares have the same colour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "4"), ("role", "ambiguousControl"), ("exp4Both", "59")] }

def ex31 : Datum :=
  { id := "geurtspouscoulous2009_ex31"
    source := ⟨"geurts-pouscoulous-2009", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob believes that Anna ate some of the cookies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "none"), ("embedding", "think")] }

def ex35 : Datum :=
  { id := "geurtspouscoulous2009_ex35"
    source := ⟨"geurts-pouscoulous-2009", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the customers shot at some of the salesmen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "none"), ("embedding", "all")] }

def all : List Datum := [t1_simple, t1_all, t1_must, t1_think, t1_want, ex24, ex26a, ex26b, ex27_a, ex27_b, ex25a, ex25b, ex29a, ex29b, ex29c, ex29d, ex29e, ex31, ex35]

end GeurtsPouscoulous2009.Examples
