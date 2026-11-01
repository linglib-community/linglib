module

public import Linglib.Data.Examples.Schema

/-!
# `Haslinger2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Haslinger2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Haslinger2025.Examples`.
-/

@[expose] public section

namespace Haslinger2025.Examples

def ch1_6a : Datum :=
  { id := "haslinger2025_ch1_6a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The doors are open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "lower")] }

def ch1_6b : Datum :=
  { id := "haslinger2025_ch1_6b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the doors are open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "higher")] }

def ch1_7a : Datum :=
  { id := "haslinger2025_ch1_7a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann owns 100 cars."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "lower")] }

def ch1_7b : Datum :=
  { id := "haslinger2025_ch1_7b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann owns exactly 100 cars."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "higher")] }

def ch1_8a : Datum :=
  { id := "haslinger2025_ch1_8a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[DEF [all doors]] [are open]"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "lower"), ("hypothetical", "yes")] }

def ch1_8b : Datum :=
  { id := "haslinger2025_ch1_8b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[all doors] [are open]"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "higher"), ("hypothetical", "yes")] }

def ch1_9a : Datum :=
  { id := "haslinger2025_ch1_9a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann and Bert have red hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "lower")] }

def ch1_9b : Datum :=
  { id := "haslinger2025_ch1_9b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both Ann and Bert have red hair."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "higher")] }

def ch2_19 : Datum :=
  { id := "haslinger2025_ch2_19"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Look, this guy owns 100 cars."
    glossedTokens := []
    context := "A new tax was introduced to discourage rich people from collecting cars. The tax rate per car increases if someone owns 10 or more cars, and increases yet again for people who own 100 or more. Ann is looking at the tax paperwork of someone who claims to own 98 cars."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "carsExact"), ("actualValue", "98")] }

def ch2_20 : Datum :=
  { id := "haslinger2025_ch2_20"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Look, this guy owns 100 cars."
    glossedTokens := []
    context := "Ann just read a newspaper report on how insanely rich Sam Bankman-Fried is. Among other things, the report claims that he owns 98 Teslas for his personal use."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "carsInexact"), ("actualValue", "98")] }

def ch2_164a : Datum :=
  { id := "haslinger2025_ch2_164a"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (164a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Bei diesem Spiel hat heute jeder 200 Münzen gesammelt."
    glossedTokens := []
    context := "On a TV game show, there is a game in which participants have to collect 200 coins in a very brief time interval. Participants that achieve a count of exactly 200 win €250. Participants that come very close to that number, but do not meet the goal exactly, receive €50. Today all ten participants managed to collect amounts that come close to 200—195, 198, 203, 205, 199 etc.—and therefore won €50. After the show, the producer wants to know how the individual games went. Her assistant points at the coins and says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "gameShow")] }

def ch2_164b : Datum :=
  { id := "haslinger2025_ch2_164b"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (164b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bei diesem Spiel hat heute niemand 200 Münzen gesammelt."
    glossedTokens := []
    context := "On a TV game show, there is a game in which participants have to collect 200 coins in a very brief time interval. Participants that achieve a count of exactly 200 win €250. Participants that come very close to that number, but do not meet the goal exactly, receive €50. Today all ten participants managed to collect amounts that come close to 200—195, 198, 203, 205, 199 etc.—and therefore won €50. After the show, the producer wants to know how the individual games went. Her assistant points at the coins and says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "gameShow")] }

def ch6_8a : Datum :=
  { id := "haslinger2025_ch6_8a"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The shirt cost 150 euros."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "tens")] }

def ch6_8b : Datum :=
  { id := "haslinger2025_ch6_8b"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The shirt cost 152 euros."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "units")] }

def ch6_9a : Datum :=
  { id := "haslinger2025_ch6_9a"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 10:45."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "quarterHours")] }

def ch6_9b : Datum :=
  { id := "haslinger2025_ch6_9b"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 10:46."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "minutes")] }

def ch7_19b : Datum :=
  { id := "haslinger2025_ch7_19b"
    source := ⟨"haslinger-2025-diss", "Ch. 7, (19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bert, Claire and Dora were there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Bert was there.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "7"), ("phenomenon", "conjunctionMaximality")] }

def all : List Datum := [ch1_6a, ch1_6b, ch1_7a, ch1_7b, ch1_8a, ch1_8b, ch1_9a, ch1_9b, ch2_19, ch2_20, ch2_164a, ch2_164b, ch6_8a, ch6_8b, ch6_9a, ch6_9b, ch7_19b]

end Haslinger2025.Examples
