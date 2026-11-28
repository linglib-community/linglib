module

public import Linglib.Data.Examples.Schema

/-!
# `VanRooy2003b` — typed example data

Auto-generated from `Linglib/Data/Examples/VanRooy2003b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanRooy2003b.Examples`.
-/

@[expose] public section

namespace VanRooy2003b.Examples

def ex_3 : Datum :=
  { id := "vanrooy2003b_3"
    source := ⟨"van-rooy-2003b", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is Muhammed Ali?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("referential: that man over there", .acceptable), ("descriptive: the greatest boxer ever", .acceptable)]
    paperFeatures := [("type", "identification question")] }

def ex_12 : Datum :=
  { id := "vanrooy2003b_12"
    source := ⟨"van-rooy-2003b", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I buy an Italian newspaper?"
    glossedTokens := []
    context := "The questioner wants a newspaper and can walk to the station or to the palace; in one world both sell it."
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some: at least at the station", .acceptable)]
    paperFeatures := [("type", "mention-some"), ("regions", "{u,w},{v,w}")] }

def ex_14 : Datum :=
  { id := "vanrooy2003b_14"
    source := ⟨"van-rooy-2003b", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who, for example, came to the party?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "explicitly non-exhaustive")] }

def ex_15 : Datum :=
  { id := "vanrooy2003b_15"
    source := ⟨"van-rooy-2003b", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows where he can buy an Italian newspaper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "embedded mention-some")] }

def ex_16 : Datum :=
  { id := "vanrooy2003b_16"
    source := ⟨"van-rooy-2003b", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who will come to the concert?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "contextual domain")] }

def ex_17 : Datum :=
  { id := "vanrooy2003b_17"
    source := ⟨"van-rooy-2003b", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who dates Mary?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "contextual domain")] }

def ex_18b : Datum :=
  { id := "vanrooy2003b_18b"
    source := ⟨"van-rooy-2003b", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many meters can you jump?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "degree question"), ("optimal value", "maximal")] }

def ex_19 : Datum :=
  { id := "vanrooy2003b_19"
    source := ⟨"van-rooy-2003b", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In how many seconds can you run the 100 meters?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "degree question"), ("optimal value", "minimal")] }

def ex_20 : Datum :=
  { id := "vanrooy2003b_20"
    source := ⟨"van-rooy-2003b", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I buy an Italian newspaper?"
    glossedTokens := []
    context := "The newspaper is sold at the station and at the palace; the best place is the station in one world, the palace in another, and either in a third."
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some: {u,w},{v,w}", .acceptable)]
    paperFeatures := [("type", "mention-some")] }

def ex_21 : Datum :=
  { id := "vanrooy2003b_21"
    source := ⟨"van-rooy-2003b", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where do you live?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("complete address, to send a letter", .acceptable), ("the city, to decide on a visit", .acceptable)]
    paperFeatures := [("type", "granularity")] }

def ex_22 : Datum :=
  { id := "vanrooy2003b_22"
    source := ⟨"van-rooy-2003b", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who killed spiderman?"
    glossedTokens := []
    context := "Either John or Bill did it, and the killer wears a blue or a green mask; who wears which is unknown."
    judgment := .acceptable
    contrasts := []
    readings := [("by name: {{u,v},{w,x}}", .acceptable), ("by mask: {{u,w},{v,x}}", .acceptable)]
    paperFeatures := [("type", "conceptual cover")] }

def ex_23 : Datum :=
  { id := "vanrooy2003b_23"
    source := ⟨"van-rooy-2003b", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is who?"
    glossedTokens := []
    context := "The spiderman scenario of (22)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "conceptual cover")] }

def ex_24 : Datum :=
  { id := "vanrooy2003b_24"
    source := ⟨"van-rooy-2003b", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many meters can't you jump?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("type", "degree question"), ("optimal value", "undefined"), ("felicity", "infelicitous")] }

def ex_25 : Datum :=
  { id := "vanrooy2003b_25"
    source := ⟨"van-rooy-2003b", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How tall can a polar bear be?"
    glossedTokens := []
    context := "Asked by an artist making a life-size sculpture of a polar bear."
    judgment := .acceptable
    contrasts := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("type", "degree question"), ("reading", "mention-some")] }

def ex_26 : Datum :=
  { id := "vanrooy2003b_26"
    source := ⟨"van-rooy-2003b", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which Beatles' autograph do you have?"
    glossedTokens := []
    context := "A Lennon autograph makes the others irrelevant, and a Harrison autograph makes a Starr autograph irrelevant."
    judgment := .acceptable
    contrasts := []
    readings := [("scalar: one resolving answer per Beatle", .acceptable)]
    paperFeatures := [("type", "scalar question")] }

def all : List Datum := [ex_3, ex_12, ex_14, ex_15, ex_16, ex_17, ex_18b, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26]

end VanRooy2003b.Examples
