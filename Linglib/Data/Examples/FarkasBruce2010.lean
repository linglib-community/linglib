module

public import Linglib.Data.Examples.Schema

/-!
# `FarkasBruce2010` — typed example data

Auto-generated from `Linglib/Data/Examples/FarkasBruce2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FarkasBruce2010.Examples`.
-/

@[expose] public section

namespace FarkasBruce2010.Examples

def ex_36_yes : Datum :=
  { id := "farkasbruce2010_36_yes"
    source := ⟨"farkas-bruce-2010", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is home. Yes, he is."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "positive"), ("particle", "yes")] }

def ex_36_no : Datum :=
  { id := "farkasbruce2010_36_no"
    source := ⟨"farkas-bruce-2010", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is home. No, he isn't."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "negative"), ("particle", "no")] }

def ex_37_yes : Datum :=
  { id := "farkasbruce2010_37_yes"
    source := ⟨"farkas-bruce-2010", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Sam home? Yes, he is."
    glossedTokens := []
    context := "Reacting to the polar question 'Is Sam home?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "positive"), ("particle", "yes")] }

def ex_37_no : Datum :=
  { id := "farkasbruce2010_37_no"
    source := ⟨"farkas-bruce-2010", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Sam home? No, he isn't."
    glossedTokens := []
    context := "Reacting to the polar question 'Is Sam home?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "negative"), ("particle", "no")] }

def ex_35_assertion_yes : Datum :=
  { id := "farkasbruce2010_35_assertion_yes"
    source := ⟨"farkas-bruce-2010", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is not home. Yes, he is."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is not home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "positive"), ("particle", "yes")] }

def ex_35_assertion_no : Datum :=
  { id := "farkasbruce2010_35_assertion_no"
    source := ⟨"farkas-bruce-2010", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is not home. No, he isn't."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is not home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "negative"), ("particle", "no")] }

def ex_35_question_yes : Datum :=
  { id := "farkasbruce2010_35_question_yes"
    source := ⟨"farkas-bruce-2010", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Sam not home? Yes, he is."
    glossedTokens := []
    context := "Reacting to the polar question 'Is Sam not home?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "negative"), ("response", "positive"), ("particle", "yes")] }

def ex_35_question_no : Datum :=
  { id := "farkasbruce2010_35_question_no"
    source := ⟨"farkas-bruce-2010", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Sam not home? No, he isn't."
    glossedTokens := []
    context := "Reacting to the polar question 'Is Sam not home?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "negative"), ("response", "negative"), ("particle", "no")] }

def ex_38_yes : Datum :=
  { id := "farkasbruce2010_38_yes"
    source := ⟨"farkas-bruce-2010", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is not home. Yes. He is not."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is not home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "negative"), ("particle", "yes")] }

def ex_38_no : Datum :=
  { id := "farkasbruce2010_38_no"
    source := ⟨"farkas-bruce-2010", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is not home. No. He is."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is not home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "positive"), ("particle", "no")] }

def ex_50_assertion : Datum :=
  { id := "farkasbruce2010_50_assertion"
    source := ⟨"farkas-bruce-2010", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is not home. Yeah no."
    glossedTokens := []
    context := "Reacting to the assertion 'Sam is not home.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "negative"), ("particle", "yes"), ("particle2", "no")] }

def ex_50_question : Datum :=
  { id := "farkasbruce2010_50_question"
    source := ⟨"farkas-bruce-2010", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Sam not home? Yeah no."
    glossedTokens := []
    context := "Reacting to the polar question 'Is Sam not home?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "negative"), ("response", "negative"), ("particle", "yes"), ("particle2", "no")] }

def ex_4_nu : Datum :=
  { id := "farkasbruce2010_4_nu"
    source := ⟨"farkas-bruce-2010", "(4)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Horea e acasă? Nu, nu e."
    glossedTokens := []
    context := "Reacting to the polar question 'Horea e acasă?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "negative"), ("particle", "nu")] }

def ex_4_ba_nu : Datum :=
  { id := "farkasbruce2010_4_ba_nu"
    source := ⟨"farkas-bruce-2010", "(4)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Horea e acasă? Ba nu, nu e."
    glossedTokens := []
    context := "Reacting to the polar question 'Horea e acasă?'."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "negative"), ("particle", "ba"), ("particle2", "nu")] }

def ex_5_nu : Datum :=
  { id := "farkasbruce2010_5_nu"
    source := ⟨"farkas-bruce-2010", "(5)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Horea e acasă. Nu, nu e."
    glossedTokens := []
    context := "Reacting to the assertion 'Horea e acasă.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "negative"), ("particle", "nu")] }

def ex_5_ba_nu : Datum :=
  { id := "farkasbruce2010_5_ba_nu"
    source := ⟨"farkas-bruce-2010", "(5)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Horea e acasă. Ba nu, nu e."
    glossedTokens := []
    context := "Reacting to the assertion 'Horea e acasă.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "negative"), ("particle", "ba"), ("particle2", "nu")] }

def ex_39_da : Datum :=
  { id := "farkasbruce2010_39_da"
    source := ⟨"farkas-bruce-2010", "(39)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat. Da, a plecat."
    glossedTokens := []
    context := "Reacting to the assertion 'Ana a plecat.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "positive"), ("particle", "da")] }

def ex_40_nu : Datum :=
  { id := "farkasbruce2010_40_nu"
    source := ⟨"farkas-bruce-2010", "(40)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana nu a plecat. Nu, n-a plecat."
    glossedTokens := []
    context := "Reacting to the assertion 'Ana nu a plecat.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "negative"), ("particle", "nu")] }

def ex_41_da : Datum :=
  { id := "farkasbruce2010_41_da"
    source := ⟨"farkas-bruce-2010", "(41)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat? Da, a plecat."
    glossedTokens := []
    context := "Reacting to the polar question 'Ana a plecat?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "positive"), ("particle", "da")] }

def ex_41_nu : Datum :=
  { id := "farkasbruce2010_41_nu"
    source := ⟨"farkas-bruce-2010", "(41)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat? Nu, n-a plecat."
    glossedTokens := []
    context := "Reacting to the polar question 'Ana a plecat?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "negative"), ("particle", "nu")] }

def ex_42_ba_nu : Datum :=
  { id := "farkasbruce2010_42_ba_nu"
    source := ⟨"farkas-bruce-2010", "(42)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat. Ba nu, n-a plecat."
    glossedTokens := []
    context := "Reacting to the assertion 'Ana a plecat.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "negative"), ("particle", "ba"), ("particle2", "nu")] }

def ex_42_nu : Datum :=
  { id := "farkasbruce2010_42_nu"
    source := ⟨"farkas-bruce-2010", "(42)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat. Nu, n-a plecat."
    glossedTokens := []
    context := "Reacting to the assertion 'Ana a plecat.'."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "positive"), ("response", "negative"), ("particle", "nu")] }

def ex_43_nu : Datum :=
  { id := "farkasbruce2010_43_nu"
    source := ⟨"farkas-bruce-2010", "(43)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat? Nu, n-a plecat."
    glossedTokens := []
    context := "Reacting to the polar question 'Ana a plecat?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "negative"), ("particle", "nu")] }

def ex_43_ba_nu : Datum :=
  { id := "farkasbruce2010_43_ba_nu"
    source := ⟨"farkas-bruce-2010", "(43)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana a plecat? Ba nu, n-a plecat."
    glossedTokens := []
    context := "Reacting to the polar question 'Ana a plecat?'."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "positive"), ("response", "negative"), ("particle", "ba"), ("particle2", "nu")] }

def ex_44_ba_da : Datum :=
  { id := "farkasbruce2010_44_ba_da"
    source := ⟨"farkas-bruce-2010", "(44)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana nu a plecat. Ba da, a plecat."
    glossedTokens := []
    context := "Reacting to the assertion 'Ana nu a plecat.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "positive"), ("particle", "ba"), ("particle2", "da")] }

def ex_45_ba_da : Datum :=
  { id := "farkasbruce2010_45_ba_da"
    source := ⟨"farkas-bruce-2010", "(45)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Ana nu a plecat? Ba da, a plecat."
    glossedTokens := []
    context := "Reacting to the polar question 'Ana nu a plecat?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "negative"), ("response", "positive"), ("particle", "ba"), ("particle2", "da")] }

def ex_46_si : Datum :=
  { id := "farkasbruce2010_46_si"
    source := ⟨"farkas-bruce-2010", "(46)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Anne n'est pas partie. Mais si."
    glossedTokens := []
    context := "Reacting to the assertion \"Anne n'est pas partie.\"."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "positive"), ("particle", "si")] }

def ex_47_si : Datum :=
  { id := "farkasbruce2010_47_si"
    source := ⟨"farkas-bruce-2010", "(47)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Anne n'est pas partie? Mais si."
    glossedTokens := []
    context := "Reacting to the polar question \"Anne n'est pas partie?\"."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "negative"), ("response", "positive"), ("particle", "si")] }

def ex_48_doch : Datum :=
  { id := "farkasbruce2010_48_doch"
    source := ⟨"farkas-bruce-2010", "(48)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Anna kommt nicht mit ins Kino. Doch! Sie kommt schon."
    glossedTokens := []
    context := "Reacting to the assertion 'Anna kommt nicht mit ins Kino.'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "assertion"), ("input", "negative"), ("response", "positive"), ("particle", "doch")] }

def ex_49_doch : Datum :=
  { id := "farkasbruce2010_49_doch"
    source := ⟨"farkas-bruce-2010", "(49)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wollen Sie den Job nicht? Doch! Ich brauche das Geld."
    glossedTokens := []
    context := "Reacting to the polar question 'Wollen Sie den Job nicht?'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("reaction", "question"), ("input", "negative"), ("response", "positive"), ("particle", "doch")] }

def all : List Datum := [ex_36_yes, ex_36_no, ex_37_yes, ex_37_no, ex_35_assertion_yes, ex_35_assertion_no, ex_35_question_yes, ex_35_question_no, ex_38_yes, ex_38_no, ex_50_assertion, ex_50_question, ex_4_nu, ex_4_ba_nu, ex_5_nu, ex_5_ba_nu, ex_39_da, ex_40_nu, ex_41_da, ex_41_nu, ex_42_ba_nu, ex_42_nu, ex_43_nu, ex_43_ba_nu, ex_44_ba_da, ex_45_ba_da, ex_46_si, ex_47_si, ex_48_doch, ex_49_doch]

end FarkasBruce2010.Examples
