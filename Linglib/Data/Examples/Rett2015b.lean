module

public import Linglib.Data.Examples.Schema

/-!
# `Rett2015b` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2015b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2015b.Examples`.
-/

@[expose] public section

namespace Rett2015b.Examples

def positive_tall : Datum :=
  { id := "rett2015b_positive_tall"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is tall."
    glossedTokens := []
    context := "Entails Adam's height exceeds the standard for tallness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "positive"), ("polarity", "positive"), ("evaluative", "true")] }

def positive_short : Datum :=
  { id := "rett2015b_positive_short"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is short."
    glossedTokens := []
    context := "Entails Adam's height is below the standard for shortness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "positive"), ("polarity", "negative"), ("evaluative", "true")] }

def comparative_tall : Datum :=
  { id := "rett2015b_comparative_tall"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is taller than Doug."
    glossedTokens := []
    context := "True even if both Adam and Doug are short."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "comparative"), ("polarity", "positive"), ("evaluative", "false")] }

def comparative_short : Datum :=
  { id := "rett2015b_comparative_short"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is shorter than Doug."
    glossedTokens := []
    context := "True even if both Adam and Doug are tall."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "comparative"), ("polarity", "negative"), ("evaluative", "false")] }

def equative_tall : Datum :=
  { id := "rett2015b_equative_tall"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is as tall as Doug."
    glossedTokens := []
    context := "Does not presuppose that either is tall."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equative"), ("polarity", "positive"), ("evaluative", "false")] }

def equative_short : Datum :=
  { id := "rett2015b_equative_short"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is as short as Doug."
    glossedTokens := []
    context := "Presupposes both Adam and Doug are short."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equative"), ("polarity", "negative"), ("evaluative", "true")] }

def mp_tall : Datum :=
  { id := "rett2015b_mp_tall"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is 6ft tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "measurePhrase"), ("polarity", "positive"), ("evaluative", "false")] }

def mp_short : Datum :=
  { id := "rett2015b_mp_short"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is 4ft short."
    glossedTokens := []
    context := "Measure phrases do not combine with negative-polar adjectives."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "measurePhrase"), ("polarity", "negative")] }

def question_tall : Datum :=
  { id := "rett2015b_question_tall"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How tall is Adam?"
    glossedTokens := []
    context := "Felicitous regardless of Adam's height."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degreeQuestion"), ("polarity", "positive"), ("evaluative", "false")] }

def question_short : Datum :=
  { id := "rett2015b_question_short"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How short is Adam?"
    glossedTokens := []
    context := "Presupposes Adam is short."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degreeQuestion"), ("polarity", "negative"), ("evaluative", "true")] }

def demonstrative_tall : Datum :=
  { id := "rett2015b_demonstrative_tall"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Doug's (about) that tall too."
    glossedTokens := []
    context := "A and B are looking at Adam, so his exact height is salient; acceptable after both 'Adam's really short' and 'Adam's really tall' ((17)-(18))."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degreeDemonstrative"), ("polarity", "positive"), ("evaluative", "false")] }

def demonstrative_short : Datum :=
  { id := "rett2015b_demonstrative_short"
    source := ⟨"rett-2015b", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Doug's (about) that short too."
    glossedTokens := []
    context := "A and B are looking at Adam, so his exact height is salient; acceptable after 'Adam's really short' and infelicitous after 'Adam's really tall' ((17)-(18))."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degreeDemonstrative"), ("polarity", "negative"), ("evaluative", "true")] }

def all : List Datum := [positive_tall, positive_short, comparative_tall, comparative_short, equative_tall, equative_short, mp_tall, mp_short, question_tall, question_short, demonstrative_tall, demonstrative_short]

end Rett2015b.Examples
