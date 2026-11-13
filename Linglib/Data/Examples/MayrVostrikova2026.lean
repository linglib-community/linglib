module

public import Linglib.Data.Examples.Schema

/-!
# `MayrVostrikova2026` — typed example data

Auto-generated from `Linglib/Data/Examples/MayrVostrikova2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MayrVostrikova2026.Examples`.
-/

@[expose] public section

namespace MayrVostrikova2026.Examples

def ex_1_but : Datum :=
  { id := "mayrvostrikova2026_1_but"
    source := ⟨"mayr-vostrikova-2026", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every student who is not Ann passed, Ann did not pass, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("determiner", "every"), ("inference", "exception")] }

def ex_1_except : Datum :=
  { id := "mayrvostrikova2026_1_except"
    source := ⟨"mayr-vostrikova-2026", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every student who is not Ann passed, Ann did not pass, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "except"), ("determiner", "every"), ("inference", "exception")] }

def ex_1_besides : Datum :=
  { id := "mayrvostrikova2026_1_besides"
    source := ⟨"mayr-vostrikova-2026", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every student who is not Ann passed, Ann did not pass, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "besides"), ("determiner", "every"), ("inference", "exception")] }

def ex_2_but : Datum :=
  { id := "mayrvostrikova2026_2_but"
    source := ⟨"mayr-vostrikova-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no student who is not Ann passed, Ann passed, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("determiner", "no"), ("inference", "addition")] }

def ex_2_except : Datum :=
  { id := "mayrvostrikova2026_2_except"
    source := ⟨"mayr-vostrikova-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no student who is not Ann passed, Ann passed, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "except"), ("determiner", "no"), ("inference", "addition")] }

def ex_2_besides : Datum :=
  { id := "mayrvostrikova2026_2_besides"
    source := ⟨"mayr-vostrikova-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no student who is not Ann passed, Ann passed, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "besides"), ("determiner", "no"), ("inference", "addition")] }

def ex_3a_but : Datum :=
  { id := "mayrvostrikova2026_3a_but"
    source := ⟨"mayr-vostrikova-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "some")] }

def ex_3b_but_atLeast : Datum :=
  { id := "mayrvostrikova2026_3b_but_atLeast"
    source := ⟨"mayr-vostrikova-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At least one student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "at least")] }

def ex_3b_but_exactly : Datum :=
  { id := "mayrvostrikova2026_3b_but_exactly"
    source := ⟨"mayr-vostrikova-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly one student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "exactly")] }

def ex_3c_but_atMost : Datum :=
  { id := "mayrvostrikova2026_3c_but_atMost"
    source := ⟨"mayr-vostrikova-2026", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most one student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "at most")] }

def ex_3c_but_moreThan : Datum :=
  { id := "mayrvostrikova2026_3c_but_moreThan"
    source := ⟨"mayr-vostrikova-2026", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than one student but Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "more than")] }

def ex_3a_except : Datum :=
  { id := "mayrvostrikova2026_3a_except"
    source := ⟨"mayr-vostrikova-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except"), ("determiner", "some")] }

def ex_3b_except_atLeast : Datum :=
  { id := "mayrvostrikova2026_3b_except_atLeast"
    source := ⟨"mayr-vostrikova-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At least one student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except"), ("determiner", "at least")] }

def ex_3b_except_exactly : Datum :=
  { id := "mayrvostrikova2026_3b_except_exactly"
    source := ⟨"mayr-vostrikova-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly one student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except"), ("determiner", "exactly")] }

def ex_3c_except_atMost : Datum :=
  { id := "mayrvostrikova2026_3c_except_atMost"
    source := ⟨"mayr-vostrikova-2026", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most one student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except"), ("determiner", "at most")] }

def ex_3c_except_moreThan : Datum :=
  { id := "mayrvostrikova2026_3c_except_moreThan"
    source := ⟨"mayr-vostrikova-2026", "(3c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than one student except Ann passed."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except"), ("determiner", "more than")] }

def ex_4 : Datum :=
  { id := "mayrvostrikova2026_4"
    source := ⟨"mayr-vostrikova-2026", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some student besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("some student who is not Ann passed, Ann passed, and Ann is a student", .acceptable)]
    paperFeatures := [("exceptive", "besides"), ("determiner", "some"), ("inference", "addition")] }

def ex_5_at_least : Datum :=
  { id := "mayrvostrikova2026_5_at_least"
    source := ⟨"mayr-vostrikova-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At least one student besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "at least"), ("inference", "addition")] }

def ex_5_more_than : Datum :=
  { id := "mayrvostrikova2026_5_more_than"
    source := ⟨"mayr-vostrikova-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More than one student besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "more than"), ("inference", "addition")] }

def ex_5_exactly : Datum :=
  { id := "mayrvostrikova2026_5_exactly"
    source := ⟨"mayr-vostrikova-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly one student besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "exactly"), ("inference", "addition")] }

def ex_6_at_most : Datum :=
  { id := "mayrvostrikova2026_6_at_most"
    source := ⟨"mayr-vostrikova-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most two students besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "at most"), ("inference", "addition")] }

def ex_6_fewer_than : Datum :=
  { id := "mayrvostrikova2026_6_fewer_than"
    source := ⟨"mayr-vostrikova-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fewer than two students besides Ann passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "fewer than"), ("inference", "addition")] }

def ex_7a_but : Datum :=
  { id := "mayrvostrikova2026_7a_but"
    source := ⟨"mayr-vostrikova-2026", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which students but Ann passed?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "which")] }

def ex_7a_except : Datum :=
  { id := "mayrvostrikova2026_7a_except"
    source := ⟨"mayr-vostrikova-2026", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which students except Ann passed?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except"), ("determiner", "which")] }

def ex_7b : Datum :=
  { id := "mayrvostrikova2026_7b"
    source := ⟨"mayr-vostrikova-2026", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which students besides Ann passed?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "which"), ("inference", "addition")] }

def ex_43a : Datum :=
  { id := "mayrvostrikova2026_43a"
    source := ⟨"mayr-vostrikova-2026", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student besides Ann and Bill passed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Ann and Bill both did not pass", .acceptable)]
    paperFeatures := [("exceptive", "besides"), ("determiner", "every"), ("inference", "exception")] }

def all : List Datum := [ex_1_but, ex_1_except, ex_1_besides, ex_2_but, ex_2_except, ex_2_besides, ex_3a_but, ex_3b_but_atLeast, ex_3b_but_exactly, ex_3c_but_atMost, ex_3c_but_moreThan, ex_3a_except, ex_3b_except_atLeast, ex_3b_except_exactly, ex_3c_except_atMost, ex_3c_except_moreThan, ex_4, ex_5_at_least, ex_5_more_than, ex_5_exactly, ex_6_at_most, ex_6_fewer_than, ex_7a_but, ex_7a_except, ex_7b, ex_43a]

end MayrVostrikova2026.Examples
