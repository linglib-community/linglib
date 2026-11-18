module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerSandtMaier2003` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerSandtMaier2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerSandtMaier2003.Examples`.
-/

@[expose] public section

namespace VanDerSandtMaier2003.Examples

def ex_1 : Datum :=
  { id := "vandersandtmaier2003_1"
    source := ⟨"van-der-sandt-maier-2003", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The King of France walks in the park. No, he doesn't, France doesn't have a king."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "presupposition"), ("sequence", "assertion-denial-correction")] }

def ex_3 : Datum :=
  { id := "vandersandtmaier2003_3"
    source := ⟨"van-der-sandt-maier-2003", "(3)"⟩
    reportedIn := some ⟨"strawson-1952", ""⟩
    language := "stan1293"
    primaryText := "A man jumped off the bridge. He didn't jump, he was pushed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "proposition"), ("problem", "referent must survive")] }

def ex_4 : Datum :=
  { id := "vandersandtmaier2003_4"
    source := ⟨"van-der-sandt-maier-2003", "(4)"⟩
    reportedIn := some ⟨"geurts-1998", ""⟩
    language := "stan1293"
    primaryText := "The King of France knows I quit smoking. No he doesn't, France doesn't have a king."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "presupposition"), ("problem", "one of two presuppositions")] }

def ex_5 : Datum :=
  { id := "vandersandtmaier2003_5"
    source := ⟨"van-der-sandt-maier-2003", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now, THAT's a nice lady. Yes, she is, but she's not a LAdy, she's my WIfe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "implicature"), ("problem", "part acknowledged, part denied")] }

def ex_9a : Datum :=
  { id := "vandersandtmaier2003_9a"
    source := ⟨"van-der-sandt-maier-2003", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible the Pope is right."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("layers", "pr: the Pope; fr: possibly right; imp: not necessarily right")] }

def ex_20 : Datum :=
  { id := "vandersandtmaier2003_20"
    source := ⟨"van-der-sandt-maier-2003", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible the Pope is right. No, it's not POssible, it's NEcessary that he's right."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "implicature"), ("off", "imp1")] }

def ex_21 : Datum :=
  { id := "vandersandtmaier2003_21"
    source := ⟨"van-der-sandt-maier-2003", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now, THAT's a nice lady. Yes, she is, but she's not a LAdy, she's my WIfe."
    glossedTokens := []
    context := "Someone points at a woman."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "implicature"), ("off", "imp1"), ("sequence", "assertion-affirmation-denial-correction")] }

def fn12 : Datum :=
  { id := "vandersandtmaier2003_fn12"
    source := ⟨"van-der-sandt-maier-2003", "footnote 12 (i)"⟩
    reportedIn := some ⟨"horn-1989", ""⟩
    language := "stan1293"
    primaryText := "They didn't call the POlice — they called the poLIce."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("denial", "register")] }

def all : List Datum := [ex_1, ex_3, ex_4, ex_5, ex_9a, ex_20, ex_21, fn12]

end VanDerSandtMaier2003.Examples
