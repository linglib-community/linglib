module

public import Linglib.Data.Examples.Schema

/-!
# `Grove2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Grove2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Grove2022.Examples`.
-/

@[expose] public section

namespace Grove2022.Examples

def ex_1 : Datum :=
  { id := "grove2022_1"
    source := ⟨"grove-2022", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Theo has a brother, he'll bring his wetsuit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("presupposes that Theo has a wetsuit", .acceptable), ("presupposes that Theo has a wetsuit if he has a brother", .questionable)]
    paperFeatures := [("section", "2.1"), ("phenomenon", "provisoProblem"), ("trigger", "his wetsuit"), ("filter", "conditional")] }

def ex_2 : Datum :=
  { id := "grove2022_2"
    source := ⟨"grove-2022", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Theo is a scuba diver, he'll bring his wetsuit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("presupposes that Theo has a wetsuit if he is a scuba diver", .acceptable)]
    paperFeatures := [("section", "2"), ("phenomenon", "provisoProblem"), ("trigger", "his wetsuit"), ("filter", "conditional")] }

def ex_6 : Datum :=
  { id := "grove2022_6"
    source := ⟨"heim-1992", "(71)"⟩
    reportedIn := some ⟨"grove-2022", "(6)"⟩
    language := "stan1293"
    primaryText := "John: I am already in bed. Mary: My parents think I am also in bed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("presupposes that John is in bed", .acceptable), ("presupposes that Mary's parents think John is in bed", .questionable)]
    paperFeatures := [("section", "2.1"), ("phenomenon", "trappedTrigger"), ("trigger", "also"), ("filter", "think")] }

def ex_7 : Datum :=
  { id := "grove2022_7"
    source := ⟨"grove-2022", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was limping earlier; I don't know why. Maybe he has a stress fracture. I don't know if he plays any sports, but if he has a stress fracture, then he'll stop running cross-country now."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "provisoProblem"), ("trigger", "stop"), ("filter", "conditional")] }

def ex_8 : Datum :=
  { id := "grove2022_8"
    source := ⟨"grove-2022", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John limping earlier. If he has a stress fracture, then I assume that he runs cross-country. Indeed, if he has a stress fracture, then he'll stop running cross-country now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "conditionalReadingContext"), ("trigger", "stop"), ("filter", "conditional")] }

def ex_9 : Datum :=
  { id := "grove2022_9"
    source := ⟨"grove-2022", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We're going scuba diving later, and I don't know if Theo owns a wetsuit. But it seems that everyone who has a brother got a wetsuit for Christmas. So, if Theo has a brother, he'll bring his wetsuit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "conditionalReadingContext"), ("trigger", "his wetsuit"), ("filter", "conditional")] }

def ex_22 : Datum :=
  { id := "grove2022_22"
    source := ⟨"grove-2022", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo believes he lost his wetsuit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("presupposes that Theo has a wetsuit, his wetsuit de re", .acceptable), ("presupposes that Theo believes he has a wetsuit, his wetsuit de dicto", .acceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "believe")] }

def ex_23 : Datum :=
  { id := "grove2022_23"
    source := ⟨"grove-2022", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo believes he has a wetsuit, and he believes he lost his wetsuit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "believe")] }

def ex_24 : Datum :=
  { id := "grove2022_24"
    source := ⟨"grove-2022", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo believes he has a wetsuit. He hopes his wetsuit is dry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "hope")] }

def ex_25 : Datum :=
  { id := "grove2022_25"
    source := ⟨"grove-2022", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo has a wetsuit, and he believes he lost his wetsuit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "believe")] }

def ex_26 : Datum :=
  { id := "grove2022_26"
    source := ⟨"grove-2022", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo has a wetsuit. He hopes his wetsuit is dry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "hope")] }

def all : List Datum := [ex_1, ex_2, ex_6, ex_7, ex_8, ex_9, ex_22, ex_23, ex_24, ex_25, ex_26]

end Grove2022.Examples
