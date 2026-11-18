module

public import Linglib.Data.Examples.Schema

/-!
# `DelPinal2015` — typed example data

Auto-generated from `Linglib/Data/Examples/DelPinal2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DelPinal2015.Examples`.
-/

@[expose] public section

namespace DelPinal2015.Examples

def fake_gun : Datum :=
  { id := "delpinal2015_fake_gun"
    source := ⟨"delpinal-2015", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake gun"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def counterfeit_rolex : Datum :=
  { id := "delpinal2015_counterfeit_rolex"
    source := ⟨"delpinal-2015", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "counterfeit Rolex"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def artificial_heart : Datum :=
  { id := "delpinal2015_artificial_heart"
    source := ⟨"delpinal-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "artificial heart"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def fake_chanel_handbag : Datum :=
  { id := "delpinal2015_fake_chanel_handbag"
    source := ⟨"delpinal-2015", "p. 7:15"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake Chanel handbag"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("[fake [Chanel handbag]]: not from Chanel, made to pass for a Chanel handbag", .acceptable), ("[fake [Chanel handbag]]: a fake handbag made by Chanel", .acceptable), ("[[fake Chanel] handbag]: a fake handbag made by Chanel", .unacceptable)]
    paperFeatures := [] }

def ex_26a : Datum :=
  { id := "delpinal2015_26a"
    source := ⟨"delpinal-2015", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "giant midget"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a midget, but a very large one", .acceptable)]
    paperFeatures := [] }

def ex_26b : Datum :=
  { id := "delpinal2015_26b"
    source := ⟨"delpinal-2015", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "midget giant"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a giant, but a very small one", .acceptable)]
    paperFeatures := [] }

def ex_27 : Datum :=
  { id := "delpinal2015_27"
    source := ⟨"delpinal-2015", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Something unbelievable happened at MIT. Scientists discovered a way of making, literally, stone lions and rubber rabbits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("stone lions and rubber rabbits taken literally, lions and rabbits made of stone and rubber", .acceptable)]
    paperFeatures := [] }

def ex_28 : Datum :=
  { id := "delpinal2015_28"
    source := ⟨"delpinal-2015", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bio-technology is advancing at an astonishing pace. I am convinced that, in the future, we will be able to make, literally, silicon cows."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("silicon cows taken literally, cows made of silicon", .acceptable)]
    paperFeatures := [] }

def ex_31 : Datum :=
  { id := "delpinal2015_31"
    source := ⟨"delpinal-2015", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Listen to this unbelievable story. Some immoral toy store owner was, literally, selling fake guns at his store."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("fake guns in the default sense, which are not guns", .acceptable), ("real guns that are fakes of some other kind, such as fake paintball guns", .unacceptable)]
    paperFeatures := [] }

def ex_32 : Datum :=
  { id := "delpinal2015_32"
    source := ⟨"delpinal-2015", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Something amazing happened at MIT. Some engineer managed to make, literally, a fake gun."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("a fake gun in the default sense, which is not a gun", .acceptable), ("a real gun that is a fake of some other kind, such as a fake paintball gun", .unacceptable)]
    paperFeatures := [] }

def evil_park_owner : Datum :=
  { id := "delpinal2015_evil_park_owner"
    source := ⟨"delpinal-2015", "p. 7:34"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake paintball gun"
    glossedTokens := []
    context := "Mark is an evil paintball gun park owner. He really hates John. Unaware of this secret hate, John goes to Mark's park to play. Mark comes up with the plan of secretly replacing John's paintball gun with a fake paintball gun that is actually a real gun, with the intention that John kill someone. Fortunately, when John handles the fake paintball gun he notices something suspiciously off with its weight and refuses to use it."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def evil_partygoer : Datum :=
  { id := "delpinal2015_evil_partygoer"
    source := ⟨"delpinal-2015", "p. 7:34"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake toy gun"
    glossedTokens := []
    context := "Peter is a clever terrorist who wants to cause havoc at a Halloween party. To evade the security measures, he designs a gun that is intended to look like a toy gun but is actually a very powerful gun. Fortunately the security personnel are suspicious of Peter and his fake toy gun, so he gets caught and his plot is averted."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [fake_gun, counterfeit_rolex, artificial_heart, fake_chanel_handbag, ex_26a, ex_26b, ex_27, ex_28, ex_31, ex_32, evil_park_owner, evil_partygoer]

end DelPinal2015.Examples
