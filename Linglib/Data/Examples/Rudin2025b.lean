module

public import Linglib.Data.Examples.Schema

/-!
# `Rudin2025b` — typed example data

Auto-generated from `Linglib/Data/Examples/Rudin2025b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rudin2025b.Examples`.
-/

@[expose] public section

namespace Rudin2025b.Examples

def ex6b_wonder : Datum :=
  { id := "rudin2025b_ex6b_wonder"
    source := ⟨"rudin-2025b", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka wondered, “Polina likes her job?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "wonder"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")] }

def ex7b_claim : Datum :=
  { id := "rudin2025b_ex7b_claim"
    source := ⟨"rudin-2025b", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka claimed, “Polina likes her job?”"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "claim"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")] }

def ex8_whisper : Datum :=
  { id := "rudin2025b_ex8_whisper"
    source := ⟨"rudin-2025b", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka whispered, “Polina likes her job?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "whisper"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "whispered")] }

def ex10_shout : Datum :=
  { id := "rudin2025b_ex10_shout"
    source := ⟨"rudin-2025b", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka shouted, “Does Polina like her job?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "shout"), ("material", "sentence"), ("mood", "interrogative"), ("tune", "rising"), ("volume", "loud")] }

def ex12a : Datum :=
  { id := "rudin2025b_ex12a"
    source := ⟨"rudin-2025b", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Then Polina asked me, “Are you married?”"
    glossedTokens := []
    context := "Ayka is talking to Bertrand about a conversation she had with Polina."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ask"), ("material", "sentence"), ("mood", "interrogative"), ("tune", "rising"), ("volume", "neutral")] }

def ex18a : Datum :=
  { id := "rudin2025b_ex18a"
    source := ⟨"rudin-2025b", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, “Polina likes her job.”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "neutral")] }

def ex37a : Datum :=
  { id := "rudin2025b_ex37a"
    source := ⟨"rudin-2025b", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I asked Ayka how she felt about the faculty meeting, and she said, *emits guttural howl of frustration*"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "inarticulate"), ("volume", "neutral")] }

def ex42a : Datum :=
  { id := "rudin2025b_ex42a"
    source := ⟨"rudin-2025b", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, *performs enthusiastic karate gestures*"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "none"), ("volume", "neutral")] }

def ex48 : Datum :=
  { id := "rudin2025b_ex48"
    source := ⟨"rudin-2025b", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, “Does Polina like her job?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "sentence"), ("mood", "interrogative"), ("tune", "rising"), ("volume", "neutral")] }

def ex49 : Datum :=
  { id := "rudin2025b_ex49"
    source := ⟨"rudin-2025b", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I asked Ayka for the wifi password, and she said, “x231&$8o.”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "inarticulate"), ("volume", "neutral")] }

def ex69a : Datum :=
  { id := "rudin2025b_ex69a"
    source := ⟨"rudin-2025b", "(69a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka yelled, “POLINA LIKES HER JOB!”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "yell"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "loud")] }

def ex69b : Datum :=
  { id := "rudin2025b_ex69b"
    source := ⟨"rudin-2025b", "(69b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka yelled, [in a hoarse whisper] “Polina likes her job.”"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "yell"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "whispered")] }

def ex70a : Datum :=
  { id := "rudin2025b_ex70a"
    source := ⟨"rudin-2025b", "(70a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka whispered, “POLINA LIKES HER JOB.”"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "whisper"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "loud")] }

def ex70b : Datum :=
  { id := "rudin2025b_ex70b"
    source := ⟨"rudin-2025b", "(70b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka whispered, [in a hoarse whisper] “Polina likes her job.”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "whisper"), ("material", "sentence"), ("mood", "declarative"), ("tune", "falling"), ("volume", "whispered")] }

def ex74a : Datum :=
  { id := "rudin2025b_ex74a"
    source := ⟨"rudin-2025b", "(74a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka said, “Polina likes her job?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "say"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")] }

def ex75 : Datum :=
  { id := "rudin2025b_ex75"
    source := ⟨"rudin-2025b", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka yelled, “POLINA LIKES HER JOB?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "yell"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "loud")] }

def ex78a : Datum :=
  { id := "rudin2025b_ex78a"
    source := ⟨"rudin-2025b", "(78a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka asserted, “Polina likes her job?”"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "assert"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")] }

def ex82a : Datum :=
  { id := "rudin2025b_ex82a"
    source := ⟨"rudin-2025b", "(82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ayka asked, “Polina likes her job?”"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ask"), ("material", "sentence"), ("mood", "declarative"), ("tune", "rising"), ("volume", "neutral")] }

def all : List Datum := [ex6b_wonder, ex7b_claim, ex8_whisper, ex10_shout, ex12a, ex18a, ex37a, ex42a, ex48, ex49, ex69a, ex69b, ex70a, ex70b, ex74a, ex75, ex78a, ex82a]

end Rudin2025b.Examples
