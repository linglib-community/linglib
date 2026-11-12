module

public import Linglib.Data.Examples.Schema

/-!
# `Geurts2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Geurts2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Geurts2010.Examples`.
-/

@[expose] public section

namespace Geurts2010.Examples

def table2_i : Datum :=
  { id := "geurts2010_table2_i"
    source := ⟨"geurts-2010", "Table 2 i, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma read some of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "false"), ("quantifier", "some"), ("alternative", "many"), ("alternative", "most"), ("alternative", "all")] }

def table2_ii : Datum :=
  { id := "geurts2010_table2_ii"
    source := ⟨"geurts-2010", "Table 2 ii, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma read many of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "false"), ("quantifier", "many"), ("alternative", "most"), ("alternative", "all")] }

def table2_iii : Datum :=
  { id := "geurts2010_table2_iii"
    source := ⟨"geurts-2010", "Table 2 iii, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma read most of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "false"), ("quantifier", "most"), ("alternative", "all")] }

def table2_iv : Datum :=
  { id := "geurts2010_table2_iv"
    source := ⟨"geurts-2010", "Table 2 iv, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma read all of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "false"), ("quantifier", "all")] }

def table2_v : Datum :=
  { id := "geurts2010_table2_v"
    source := ⟨"geurts-2010", "Table 2 v, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma didn't read any of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "true"), ("quantifier", "some")] }

def table2_vi : Datum :=
  { id := "geurts2010_table2_vi"
    source := ⟨"geurts-2010", "Table 2 vi, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma didn't read many of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "true"), ("quantifier", "many"), ("alternative", "some")] }

def table2_vii : Datum :=
  { id := "geurts2010_table2_vii"
    source := ⟨"geurts-2010", "Table 2 vii, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma didn't read most of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "true"), ("quantifier", "most"), ("alternative", "some"), ("alternative", "many")] }

def table2_viii : Datum :=
  { id := "geurts2010_table2_viii"
    source := ⟨"geurts-2010", "Table 2 viii, p. 58"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma didn't read all of the papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negated", "true"), ("quantifier", "all"), ("alternative", "some"), ("alternative", "many"), ("alternative", "most")] }

def ex_11 : Datum :=
  { id := "geurts2010_11"
    source := ⟨"geurts-2010", "(11), p. 110"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "George is British or Canadian."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "He may be British."), ("conveys", "true")] }

def ex_12 : Datum :=
  { id := "geurts2010_12"
    source := ⟨"geurts-2010", "(12), p. 110"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "George may be British or Canadian."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "He may be British."), ("conveys", "true")] }

def ex_19 : Datum :=
  { id := "geurts2010_19"
    source := ⟨"geurts-2010", "(19), p. 118"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You can have fruit or chocolate cake."
    glossedTokens := []
    context := "My son asks what is for dessert; the modal is deontic and performative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "You can have chocolate cake."), ("conveys", "true")] }

def ex_13 : Datum :=
  { id := "geurts2010_13"
    source := ⟨"geurts-2010", "(13), p. 112"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Many of the nurses were drunk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "sameLength"), ("inference", "George doesn't believe that all the nurses were drunk."), ("conveys", "true")] }

def ex_23 : Datum :=
  { id := "geurts2010_23"
    source := ⟨"geurts-2010", "(23), p. 122"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must have been a great party. I hear that well before midnight all the doctors, many though not all of the interns, and many of the nurses were drunk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "George doesn't know whether all the nurses were drunk."), ("conveys", "true")] }

def ex_26a : Datum :=
  { id := "geurts2010_26a"
    source := ⟨"geurts-2010", "(26a), p. 124"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I hurt my finger."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "sameLength"), ("inference", "I didn't hurt my thumb."), ("conveys", "true")] }

def ex_26b : Datum :=
  { id := "geurts2010_26b"
    source := ⟨"geurts-2010", "(26b), p. 124"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I hurt my toe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "longer"), ("inference", "I didn't hurt my big toe."), ("conveys", "false")] }

def ex_6_figs : Datum :=
  { id := "geurts2010_6_figs"
    source := ⟨"geurts-2010", "(6), p. 166"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo either had a mango or some of the figs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "figs"), ("inference", "Cleo didn't eat all the figs."), ("conveys", "true")] }

def ex_3 : Datum :=
  { id := "geurts2010_3"
    source := ⟨"geurts-2010", "(3), p. 165"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo either had a mango or some of the figs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "mango"), ("inference", "Cleo didn't have a mango."), ("conveys", "false")] }

def ex_31_x : Datum :=
  { id := "geurts2010_31_x"
    source := ⟨"geurts-2010", "(31), pp. 179-180"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last year, a Dutch sailor showed some symptoms of delirium."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "referent"), ("inference", "The sailor in question didn't show all the symptoms of delirium."), ("conveys", "true")] }

def ex_29 : Datum :=
  { id := "geurts2010_29"
    source := ⟨"geurts-2010", "(29), p. 144"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last year, a Dutch sailor showed some of the symptoms of delirium."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "everySailor"), ("inference", "Last year, no Dutch sailor showed all the symptoms of delirium."), ("conveys", "false")] }

def ex_61a : Datum :=
  { id := "geurts2010_61a"
    source := ⟨"geurts-2010", "(61a), p. 158"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the farmers in this region own goats or sheep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "all"), ("inference", "None of them own both."), ("conveys", "false")] }

def ex_61b : Datum :=
  { id := "geurts2010_61b"
    source := ⟨"geurts-2010", "(61b), p. 158"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At least 300 of the farmers in this region own goats or sheep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "moreThanOne"), ("inference", "At least 300 of them don't own both."), ("conveys", "false")] }

def ex_61c : Datum :=
  { id := "geurts2010_61c"
    source := ⟨"geurts-2010", "(61c), p. 158"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only six farmers in this region own goats or sheep."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "exactlyTwo"), ("inference", "Only six farmers in this region own goats or sheep but not both."), ("conveys", "false")] }

def ex_56a : Datum :=
  { id := "geurts2010_56a"
    source := ⟨"geurts-2010", "(56a), p. 156"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I hope that some of my relatives will remember my birthday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("attitude", "hope"), ("inference", "I hope that not all of them will remember it."), ("conveys", "false")] }

def ex_56b : Datum :=
  { id := "geurts2010_56b"
    source := ⟨"geurts-2010", "(56b), p. 156"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have to read some of these papers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("attitude", "have to"), ("inference", "You're not allowed to read all of them."), ("conveys", "false")] }

def ex_56c : Datum :=
  { id := "geurts2010_56c"
    source := ⟨"geurts-2010", "(56c), p. 156"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want you to give me some of your biscuits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("attitude", "want"), ("inference", "I want you not to give me all of your biscuits."), ("conveys", "false")] }

def all : List Datum := [table2_i, table2_ii, table2_iii, table2_iv, table2_v, table2_vi, table2_vii, table2_viii, ex_11, ex_12, ex_19, ex_13, ex_23, ex_26a, ex_26b, ex_6_figs, ex_3, ex_31_x, ex_29, ex_61a, ex_61b, ex_61c, ex_56a, ex_56b, ex_56c]

end Geurts2010.Examples
