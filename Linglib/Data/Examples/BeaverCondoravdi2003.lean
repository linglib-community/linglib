module

public import Linglib.Data.Examples.Schema

/-!
# `BeaverCondoravdi2003` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaverCondoravdi2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaverCondoravdi2003.Examples`.
-/

@[expose] public section

namespace BeaverCondoravdi2003.Examples

def ex_1 : Datum :=
  { id := "beavercondoravdi2003_1"
    source := ⟨"beaver-condoravdi-2003", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo left Europe before David did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before")] }

def ex_2 : Datum :=
  { id := "beavercondoravdi2003_2"
    source := ⟨"beaver-condoravdi-2003", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David left Europe after Cleo did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after")] }

def ex_3 : Datum :=
  { id := "beavercondoravdi2003_3"
    source := ⟨"beaver-condoravdi-2003", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo was in America before David was in America."
    glossedTokens := []
    context := "Cleo's stay starts before David's; their stays overlap."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "antisymmetry")] }

def ex_5 : Datum :=
  { id := "beavercondoravdi2003_5"
    source := ⟨"beaver-condoravdi-2003", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo was in America after David was in America."
    glossedTokens := []
    context := "Cleo's stay starts before David's; their stays overlap."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "antisymmetry")] }

def ex_9 : Datum :=
  { id := "beavercondoravdi2003_9"
    source := ⟨"beaver-condoravdi-2003", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred was dancing after Ginger was."
    glossedTokens := []
    context := "Ginger dances continuously; Fred dances in the middle; Delores does a quick routine after Fred stops, while Ginger still dances."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "transitivity")] }

def ex_10 : Datum :=
  { id := "beavercondoravdi2003_10"
    source := ⟨"beaver-condoravdi-2003", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ginger was dancing after Delores was."
    glossedTokens := []
    context := "Same situation (8)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "transitivity")] }

def ex_11 : Datum :=
  { id := "beavercondoravdi2003_11"
    source := ⟨"beaver-condoravdi-2003", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred was dancing after Delores was."
    glossedTokens := []
    context := "Same situation (8)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "transitivity")] }

def ex_12 : Datum :=
  { id := "beavercondoravdi2003_12"
    source := ⟨"beaver-condoravdi-2003", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Delores was dancing before Ginger was."
    glossedTokens := []
    context := "Same situation (8)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "converseness")] }

def ex_15 : Datum :=
  { id := "beavercondoravdi2003_15"
    source := ⟨"beaver-condoravdi-2003", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo leapt into action before David moved a muscle."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "npi-licensing")] }

def ex_16 : Datum :=
  { id := "beavercondoravdi2003_16"
    source := ⟨"beaver-condoravdi-2003", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo leapt into action after David moved a muscle."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "npi-licensing")] }

def ex_22 : Datum :=
  { id := "beavercondoravdi2003_22"
    source := ⟨"beaver-condoravdi-2003", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "On Dec. 9, the U.S. Supreme Court stopped the hand count before it was completed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")] }

def ex_23 : Datum :=
  { id := "beavercondoravdi2003_23"
    source := ⟨"beaver-condoravdi-2003", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Another booby-trapped bicycle and a bomb hidden in a supermarket cart were discovered and defused by police before they exploded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")] }

def ex_24 : Datum :=
  { id := "beavercondoravdi2003_24"
    source := ⟨"beaver-condoravdi-2003", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mozart died before he finished the Requiem and it was completed by his student, Franz Xavier [Süssmayr]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")] }

def ex_25 : Datum :=
  { id := "beavercondoravdi2003_25"
    source := ⟨"beaver-condoravdi-2003", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mozart died after he finished the Requiem."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "veridicality")] }

def ex_26 : Datum :=
  { id := "beavercondoravdi2003_26"
    source := ⟨"beaver-condoravdi-2003", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mozart finished the Requiem after he died."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "veridicality")] }

def ex_32 : Datum :=
  { id := "beavercondoravdi2003_32"
    source := ⟨"beaver-condoravdi-2003", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David ate lots of ketchup before he made a clean sweep of all the gold medals in the Sydney Olympics."
    glossedTokens := []
    context := "David never won a gold medal at anything."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "overgeneration")] }

def ex_34 : Datum :=
  { id := "beavercondoravdi2003_34"
    source := ⟨"beaver-condoravdi-2003", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo left exactly 5 seconds before David sang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "measure-phrase")] }

def ex_42 : Datum :=
  { id := "beavercondoravdi2003_42"
    source := ⟨"beaver-condoravdi-2003", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The police defused the bomb before it exploded."
    glossedTokens := []
    context := "It is taken for granted that there was a bomb ticking which ended up not exploding."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")] }

def ex_43 : Datum :=
  { id := "beavercondoravdi2003_43"
    source := ⟨"beaver-condoravdi-2003", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left the party before there was (any) trouble."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "non-committal")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_5, ex_9, ex_10, ex_11, ex_12, ex_15, ex_16, ex_22, ex_23, ex_24, ex_25, ex_26, ex_32, ex_34, ex_42, ex_43]

end BeaverCondoravdi2003.Examples
