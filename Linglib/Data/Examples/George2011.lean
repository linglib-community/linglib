module

public import Linglib.Data.Examples.Schema

/-!
# `George2011` — typed example data

Auto-generated from `Linglib/Data/Examples/George2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace George2011.Examples`.
-/

@[expose] public section

namespace George2011.Examples

def ex12 : Datum :=
  { id := "george2011_ex12"
    source := ⟨"george-2011", "ch. 3 (12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maggie knows who was admitted to the program."
    glossedTokens := []
    context := "Three applicants, Riley, Adam and Robin; Riley and Adam were admitted and Robin rejected. Maggie, not on the admissions committee, was sent the complete list of admitted applicants and had never heard of any applicant before, so for all she knows Robin did not apply, or Wesley did."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence", "admittedKnown"), ("holds", "yes")] }

def ex13 : Datum :=
  { id := "george2011_ex13"
    source := ⟨"george-2011", "ch. 3 (13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maggie knows who wasn't admitted to the program."
    glossedTokens := []
    context := "Three applicants, Riley, Adam and Robin; Riley and Adam were admitted and Robin rejected. Maggie, not on the admissions committee, was sent the complete list of admitted applicants and had never heard of any applicant before, so for all she knows Robin did not apply, or Wesley did."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence", "notAdmittedKnown"), ("holds", "no")] }

def ex4 : Datum :=
  { id := "george2011_ex4"
    source := ⟨"george-2011", "ch. 3 (4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maggie knows who was admitted to the program, but she doesn't know who wasn't admitted."
    glossedTokens := []
    context := "Three applicants, Riley, Adam and Robin; Riley and Adam were admitted and Robin rejected. Maggie, not on the admissions committee, was sent the complete list of admitted applicants and had never heard of any applicant before, so for all she knows Robin did not apply, or Wesley did."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence", "admittedButNot"), ("holds", "yes")] }

def ex17 : Datum :=
  { id := "george2011_ex17"
    source := ⟨"george-2011", "ch. 3 (17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rupert knows which of his four students were admitted, but he doesn't know which weren't."
    glossedTokens := []
    context := "Rupert's four students are Anne, Red, Alex and Jonathan; Anne and Red were admitted, Jonathan rejected, and Alex falls into some other category, such as being waitlisted. Rupert has the complete list of admitted students but does not know, for Jonathan and Alex, whether they were rejected or fall into another category."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence", "fourStudents"), ("holds", "yes")] }

def ex33 : Datum :=
  { id := "george2011_ex33"
    source := ⟨"george-2011", "ch. 4 (33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Janna knows where Rupert can buy a newspaper."
    glossedTokens := []
    context := "Rupert can buy a newspaper at PaperWorld and not at Newstopia. Janna and Red both know the former and know the same propositions; Red falsely believes Rupert can buy one at Newstopia, Janna has no opinion about Newstopia."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence", "jannaNewspaper"), ("holds", "yes")] }

def ex34 : Datum :=
  { id := "george2011_ex34"
    source := ⟨"george-2011", "ch. 4 (34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Red knows where Rupert can buy a newspaper."
    glossedTokens := []
    context := "Rupert can buy a newspaper at PaperWorld and not at Newstopia. Janna and Red both know the former and know the same propositions; Red falsely believes Rupert can buy one at Newstopia, Janna has no opinion about Newstopia."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence", "redNewspaper"), ("holds", "no")] }

def all : List Datum := [ex12, ex13, ex4, ex17, ex33, ex34]

end George2011.Examples
