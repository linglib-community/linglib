module

public import Linglib.Data.Examples.Schema

/-!
# `Umbach2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Umbach2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Umbach2004.Examples`.
-/

@[expose] public section

namespace Umbach2004.Examples

def ex_9a : Datum :=
  { id := "umbach2004_9a"
    source := ⟨"umbach-2004", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had a drink, and/but Mary had a martini."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "semantic independence"), ("construction", "coordination")] }

def ex_9b : Datum :=
  { id := "umbach2004_9b"
    source := ⟨"umbach-2004", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John bought the beer, and/but Mary bought the port."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("port as a drink", .acceptable), ("port as a harbour", .questionable)]
    paperFeatures := [("condition", "common integrator"), ("construction", "coordination")] }

def ex_10a : Datum :=
  { id := "umbach2004_10a"
    source := ⟨"umbach-2004", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only paid for the DRINKS, not for the MARTINI."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "semantic independence"), ("construction", "focus")] }

def ex_10b : Datum :=
  { id := "umbach2004_10b"
    source := ⟨"umbach-2004", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only paid for the BEER, not for the PORT."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("condition", "common integrator"), ("construction", "focus")] }

def ex_12 : Datum :=
  { id := "umbach2004_12"
    source := ⟨"umbach-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "RONALD made the hamburgers."
    glossedTokens := []
    context := "A: Mary made the salad, and Anna made the hamburgers."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "contrastive"), ("exclusion", "instead")] }

def ex_14a : Datum :=
  { id := "umbach2004_14a"
    source := ⟨"umbach-2004", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tonight, RONALD went shopping."
    glossedTokens := []
    context := "Things have changed at the Miller family."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "contrastive"), ("exclusion", "instead"), ("presupposition", "someone went shopping")] }

def ex_14b : Datum :=
  { id := "umbach2004_14b"
    source := ⟨"umbach-2004", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tonight, only RONALD went shopping."
    glossedTokens := []
    context := "Things have changed at the Miller family."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "only-phrase"), ("exclusion", "in addition"), ("presupposition", "Ronald went shopping")] }

def ex_16a : Datum :=
  { id := "umbach2004_16a"
    source := ⟨"umbach-2004", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "... but Bill has washed the DISHES."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "verb phrase"), ("contrast", "activity")] }

def ex_16b : Datum :=
  { id := "umbach2004_16b"
    source := ⟨"umbach-2004", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "... but BILL has washed the dishes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "subject"), ("contrast", "person")] }

def ex_17b : Datum :=
  { id := "umbach2004_17b"
    source := ⟨"umbach-2004", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[yes] John cleaned up his room and [yes] he washed the dishes."
    glossedTokens := []
    context := "Adam: Did John clean up his room and wash the dishes?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "and"), ("answer", "confirm+confirm")] }

def ex_17c : Datum :=
  { id := "umbach2004_17c"
    source := ⟨"umbach-2004", "(17c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[yes] John cleaned up his room, but [yes] he washed the dishes."
    glossedTokens := []
    context := "Adam: Did John clean up his room and wash the dishes?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "but"), ("answer", "confirm+confirm")] }

def ex_17d : Datum :=
  { id := "umbach2004_17d"
    source := ⟨"umbach-2004", "(17d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[no] John didn't clean up his room, but [no] he didn't wash the dishes."
    glossedTokens := []
    context := "Adam: Did John clean up his room and wash the dishes?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "but"), ("answer", "deny+deny")] }

def ex_17e : Datum :=
  { id := "umbach2004_17e"
    source := ⟨"umbach-2004", "(17e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[yes] John cleaned up his room, but [no] he didn't wash the dishes."
    glossedTokens := []
    context := "Adam: Did John clean up his room and wash the dishes?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "but"), ("answer", "confirm+deny")] }

def ex_17f : Datum :=
  { id := "umbach2004_17f"
    source := ⟨"umbach-2004", "(17f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[yes] John cleaned up his room, but [no] he skipped the washing-up."
    glossedTokens := []
    context := "Adam: Did John clean up his room and wash the dishes?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "but"), ("answer", "confirm+deny"), ("negation", "implicit")] }

def ex_17g : Datum :=
  { id := "umbach2004_17g"
    source := ⟨"umbach-2004", "(17g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[no] John didn't clean up his room, but [yes] he did the washing-up."
    glossedTokens := []
    context := "Adam: Did John clean up his room and wash the dishes?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "but"), ("answer", "deny+confirm")] }

def ex_19a : Datum :=
  { id := "umbach2004_19a"
    source := ⟨"umbach-2004", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cleaned up the ROOM, but he didn't wash the DISHES."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "but"), ("contrast", "simple"), ("exclusion", "in addition")] }

def ex_19b : Datum :=
  { id := "umbach2004_19b"
    source := ⟨"umbach-2004", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John only cleaned up the ROOM (he did not also wash the dishes)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focus", "only-phrase"), ("exclusion", "in addition")] }

def ex_21b : Datum :=
  { id := "umbach2004_21b"
    source := ⟨"umbach-2004", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "JOHN cleaned up the room, but BILL didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("contrast", "simple"), ("alternatives", "individuals")] }

def ex_22a : Datum :=
  { id := "umbach2004_22a"
    source := ⟨"umbach-2004", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "JOHN cleaned up the ROOM, but BILL did the DISHES."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("contrast", "double")] }

def ex_23a : Datum :=
  { id := "umbach2004_23a"
    source := ⟨"umbach-2004", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill didn't eat the apple but the banana."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "correction"), ("conjuncts", "non-sentential")] }

def ex_23b : Datum :=
  { id := "umbach2004_23b"
    source := ⟨"umbach-2004", "(23b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bill hat nicht den Apfel, sondern die Banane gegessen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "correction"), ("connective", "sondern")] }

def ex_23c : Datum :=
  { id := "umbach2004_23c"
    source := ⟨"umbach-2004", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill ate the apple but not the banana."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "contrast")] }

def ex_23d : Datum :=
  { id := "umbach2004_23d"
    source := ⟨"umbach-2004", "(23d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bill hat den Apfel, sondern nicht die Banane gegessen."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("relation", "correction"), ("connective", "sondern")] }

def ex_24a : Datum :=
  { id := "umbach2004_24a"
    source := ⟨"umbach-2004", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't go to Berlin but he went to Paris."
    glossedTokens := []
    context := "Did John go to Berlin and also to Paris?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "contrast"), ("counterfactual", "John might have gone to Berlin in addition to Paris")] }

def ex_25a : Datum :=
  { id := "umbach2004_25a"
    source := ⟨"umbach-2004", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't go to Berlin but to Paris."
    glossedTokens := []
    context := "Did John go to Berlin?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "correction"), ("counterfactual", "he might have gone to Berlin instead of Paris")] }

def ex_26b : Datum :=
  { id := "umbach2004_26b"
    source := ⟨"umbach-2004", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, Ronald did not go to the OPERA but to the CINEMA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "correction"), ("exclusion", "instead")] }

def ex_27b : Datum :=
  { id := "umbach2004_27b"
    source := ⟨"umbach-2004", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In Paris, Ronald went to the CINEMA, but he didn't go to the OPERA."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relation", "contrast"), ("exclusion", "in addition")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_10b, ex_12, ex_14a, ex_14b, ex_16a, ex_16b, ex_17b, ex_17c, ex_17d, ex_17e, ex_17f, ex_17g, ex_19a, ex_19b, ex_21b, ex_22a, ex_23a, ex_23b, ex_23c, ex_23d, ex_24a, ex_25a, ex_26b, ex_27b]

end Umbach2004.Examples
