module

public import Linglib.Data.Examples.Schema

/-!
# `BeaverKrahmer2001` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaverKrahmer2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaverKrahmer2001.Examples`.
-/

@[expose] public section

namespace BeaverKrahmer2001.Examples

def ex_1 : Datum :=
  { id := "beaverkrahmer2001_1"
    source := ⟨"karttunen-peters-1979", ""⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(1)"⟩
    language := "stan1293"
    primaryText := "Somebody managed to succeed George V on the throne of England."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "quantified presupposition trigger")] }

def ex_2 : Datum :=
  { id := "beaverkrahmer2001_2"
    source := ⟨"heim-1983", "(25)"⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(2)"⟩
    language := "stan1293"
    primaryText := "A fat man pushes his bicycle."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_3 : Datum :=
  { id := "beaverkrahmer2001_3"
    source := ⟨"heim-1983", "(23)"⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(3)"⟩
    language := "stan1293"
    primaryText := "Everyone who serves his king will be rewarded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_4 : Datum :=
  { id := "beaverkrahmer2001_4"
    source := ⟨"heim-1983", "(7)"⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(4)"⟩
    language := "stan1293"
    primaryText := "Every nation cherishes its king."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_5 : Datum :=
  { id := "beaverkrahmer2001_5"
    source := ⟨"beaver-krahmer-2001", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill regrets that Mary is sad."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "q<p>"), ("intuitive", "p"), ("strongPredicts", "p")] }

def ex_6 : Datum :=
  { id := "beaverkrahmer2001_6"
    source := ⟨"beaver-krahmer-2001", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill regrets that the king of France is bald."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "nested elementary presupposition")] }

def ex_7 : Datum :=
  { id := "beaverkrahmer2001_7"
    source := ⟨"beaver-krahmer-2001", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that Bill regrets that Mary is sad."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "~q<p>"), ("intuitive", "p"), ("strongPredicts", "p"), ("strongVerdict", "correct")] }

def ex_8 : Datum :=
  { id := "beaverkrahmer2001_8"
    source := ⟨"beaver-krahmer-2001", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill regrets that Mary is sad, then he'll soothe her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "q<p> -> r"), ("intuitive", "p"), ("strongPredicts", "p | r"), ("strongVerdict", "incorrect"), ("middlePredicts", "p"), ("middleVerdict", "correct")] }

def ex_9 : Datum :=
  { id := "beaverkrahmer2001_9"
    source := ⟨"beaver-krahmer-2001", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary is sad, then Bill regrets that Mary is sad."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "p -> q<p>"), ("intuitive", "none"), ("weakPredicts", "p"), ("weakVerdict", "incorrect")] }

def ex_10 : Datum :=
  { id := "beaverkrahmer2001_10"
    source := ⟨"karttunen-peters-1979", ""⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(10)"⟩
    language := "stan1293"
    primaryText := "Somebody managed to succeed George V (on the throne of England)."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "quantified presupposition trigger")] }

def ex_13 : Datum :=
  { id := "beaverkrahmer2001_13"
    source := ⟨"heim-1983", "(7)"⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(13)"⟩
    language := "stan1293"
    primaryText := "Every nation cherishes its king."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("predicted", "disjunctive")] }

def ex_16 : Datum :=
  { id := "beaverkrahmer2001_16"
    source := ⟨"beaver-krahmer-2001", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't know that Bill is happy, she merely believes it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "cancellation under negation")] }

def ex_17 : Datum :=
  { id := "beaverkrahmer2001_17"
    source := ⟨"beaver-1997", ""⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(17)"⟩
    language := "stan1293"
    primaryText := "If Mary knows that Bill is happy, then I'm a Dutchman - she merely believes it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "cancellation in a conditional")] }

def ex_18 : Datum :=
  { id := "beaverkrahmer2001_18"
    source := ⟨"beaver-krahmer-2001", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has stopped smoking, or he doesn't have enough money to buy cigarettes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "q<p> | r"), ("intuitive", "p"), ("projection", "leftProjects")] }

def ex_19 : Datum :=
  { id := "beaverkrahmer2001_19"
    source := ⟨"beaver-krahmer-2001", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill doesn't have enough money to buy cigarettes, or he's stopped smoking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "r | q<p>"), ("intuitive", "p"), ("projection", "rightProjects")] }

def ex_20 : Datum :=
  { id := "beaverkrahmer2001_20"
    source := ⟨"beaver-krahmer-2001", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has just stopped smoking, or else he's just started doing some exercise."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("projection", "bothProject")] }

def ex_21 : Datum :=
  { id := "beaverkrahmer2001_21"
    source := ⟨"beaver-krahmer-2001", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has just stopped smoking, or he never did smoke and just carried that lighter around as a pose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "q<p> | ~p"), ("intuitive", "none"), ("projection", "cancelLeft")] }

def ex_22 : Datum :=
  { id := "beaverkrahmer2001_22"
    source := ⟨"beaver-krahmer-2001", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill always did smoke, but only when nobody was watching, or else he's just started smoking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("projection", "cancelRight")] }

def ex_23 : Datum :=
  { id := "beaverkrahmer2001_23"
    source := ⟨"beaver-krahmer-2001", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill just stopped smoking, and never did drink, or else he just stopped drinking, and never did smoke."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("projection", "cancelBothAssertions")] }

def ex_24 : Datum :=
  { id := "beaverkrahmer2001_24"
    source := ⟨"beaver-krahmer-2001", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has just stopped smoking, or else he's just started smoking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "q<p> | r<~p>"), ("intuitive", "none"), ("projection", "cancelBothInconsistent")] }

def ex_25 : Datum :=
  { id := "beaverkrahmer2001_25"
    source := ⟨"beaver-krahmer-2001", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary is clever, she knows that Bill is happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "p -> q<r>"), ("intuitive", "r"), ("strongPredicts", "p -> r"), ("strongVerdict", "incorrect"), ("middlePredicts", "p -> r"), ("middleVerdict", "incorrect")] }

def ex_26 : Datum :=
  { id := "beaverkrahmer2001_26"
    source := ⟨"beaver-2001", "E154"⟩
    reportedIn := some ⟨"beaver-krahmer-2001", "(26)"⟩
    language := "stan1293"
    primaryText := "If Spaceman Spiff lands on Planet X, he will be bothered by the fact that his weight is higher than it would be on earth."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("schema", "p -> q<r>"), ("intuitive", "p -> r"), ("strongPredicts", "p -> r"), ("strongVerdict", "correct"), ("middlePredicts", "p -> r"), ("middleVerdict", "correct")] }

def ex_27 : Datum :=
  { id := "beaverkrahmer2001_27"
    source := ⟨"beaver-krahmer-2001", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The king of France is not bald, since there is no king of France."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("basic", "~(q<p>) &w ~p"), ("preferred", "~A(q<p>) &w ~p"), ("presupposes", "none")] }

def ex_28 : Datum :=
  { id := "beaverkrahmer2001_28"
    source := ⟨"beaver-krahmer-2001", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Either Bill has just stopped smoking, or else he's just started smoking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("basic", "q<p> |w r<~p>"), ("preferred", "A(q<p>) |w A(r<~p>)")] }

def ex_29 : Datum :=
  { id := "beaverkrahmer2001_29"
    source := ⟨"beaver-krahmer-2001", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary is sad, then Bill regrets that Mary is sad."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("basic", "p ->w q<p>"), ("preferred", "p ->w A(q<p>)"), ("presupposes", "none")] }

def ex_30 : Datum :=
  { id := "beaverkrahmer2001_30"
    source := ⟨"beaver-krahmer-2001", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spaceman Spiff stands on the weighing scale, he will be bothered by the fact that his weight is higher than it was yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "unconditional accommodation")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_13, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_29, ex_30]

end BeaverKrahmer2001.Examples
