module

public import Linglib.Data.Examples.Schema

/-!
# `Bruening2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Bruening2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bruening2021.Examples`.
-/

@[expose] public section

namespace Bruening2021.Examples

def ex_10a : Datum :=
  { id := "bruening2021_10a"
    source := ⟨"bruening-2021", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is going to serve the guests now, but I don't know what."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "serve"), ("sluiced", "secondObject")] }

def ex_10b : Datum :=
  { id := "bruening2021_10b"
    source := ⟨"bruening-2021", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is going to feed the dogs now, but didn't say what."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "feed"), ("sluiced", "secondObject")] }

def ex_10c : Datum :=
  { id := "bruening2021_10c"
    source := ⟨"bruening-2021", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ron has to pay the loan shark, but I don't know how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pay"), ("sluiced", "secondObject")] }

def ex_10d : Datum :=
  { id := "bruening2021_10d"
    source := ⟨"bruening-2021", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They charge every visitor, but their website doesn't say how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "charge"), ("sluiced", "secondObject")] }

def ex_10e : Datum :=
  { id := "bruening2021_10e"
    source := ⟨"bruening-2021", "(10e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are definitely going to fine you, I just don't know how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "fine"), ("sluiced", "secondObject")] }

def ex_10f : Datum :=
  { id := "bruening2021_10f"
    source := ⟨"bruening-2021", "(10f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I think you need to tip the waiter in Germany, but I don't know how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "tip"), ("sluiced", "secondObject")] }

def ex_10g : Datum :=
  { id := "bruening2021_10g"
    source := ⟨"bruening-2021", "(10g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It will cost you, I just don't know how much."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "cost"), ("sluiced", "secondObject")] }

def ex_10h : Datum :=
  { id := "bruening2021_10h"
    source := ⟨"bruening-2021", "(10h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He teaches high-schoolers, but I'm not sure what subject."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "teach"), ("sluiced", "secondObject")] }

def ex_11a : Datum :=
  { id := "bruening2021_11a"
    source := ⟨"bruening-2021", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They accidentally charged way too much, but we can't figure out who."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("They accidentally charged someone way too much, but we can't figure out who.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "charge"), ("sluiced", "firstObject")] }

def ex_11b : Datum :=
  { id := "bruening2021_11b"
    source := ⟨"bruening-2021", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That guy once tipped almost 300%, but I can't remember which waitress."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("That guy once tipped a waitress almost 300%, but I can't remember which waitress.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "tip"), ("sluiced", "firstObject")] }

def ex_11c : Datum :=
  { id := "bruening2021_11c"
    source := ⟨"bruening-2021", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That guy envies the big house and the expensive car, but I can't remember which of his neighbors."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("That guy envies one of his neighbors the big house and the expensive car, but I can't remember which of his neighbors.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "envy"), ("sluiced", "firstObject")] }

def ex_11d : Datum :=
  { id := "bruening2021_11d"
    source := ⟨"bruening-2021", "(11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pope once forgave blasphemy, but I don't know who."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("The pope once forgave someone blasphemy, but I don't know who.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "forgive"), ("sluiced", "firstObject")] }

def ex_11e : Datum :=
  { id := "bruening2021_11e"
    source := ⟨"bruening-2021", "(11e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The court denied due process, but they won't tell us who."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("The court denied one of the prisoners due process, but they won't tell us who.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "deny"), ("sluiced", "firstObject")] }

def ex_11f : Datum :=
  { id := "bruening2021_11f"
    source := ⟨"bruening-2021", "(11f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The warden will permit one last conjugal visit, but he didn't say who."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("The warden will permit someone one last conjugal visit, but he didn't say who.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "permit"), ("sluiced", "firstObject")] }

def ex_11g : Datum :=
  { id := "bruening2021_11g"
    source := ⟨"bruening-2021", "(11g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The black knight struck a killing blow, but we couldn't see which opponent."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := [("The black knight struck one of his opponents a killing blow, but we couldn't see which opponent.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "strike"), ("sluiced", "firstObject")] }

def ex_63a_doc : Datum :=
  { id := "bruening2021_63a_doc"
    source := ⟨"bruening-2021", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't show us yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "show"), ("implicit", "secondObject")] }

def ex_63a_pp : Datum :=
  { id := "bruening2021_63a_pp"
    source := ⟨"bruening-2021", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't show to us yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "show"), ("implicit", "directObject")] }

def ex_63b_doc : Datum :=
  { id := "bruening2021_63b_doc"
    source := ⟨"bruening-2021", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't ask us yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ask"), ("implicit", "secondObject")] }

def ex_63b_pp : Datum :=
  { id := "bruening2021_63b_pp"
    source := ⟨"bruening-2021", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't ask of us yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "ask"), ("implicit", "directObject")] }

def ex_63c_email_doc : Datum :=
  { id := "bruening2021_63c_email_doc"
    source := ⟨"bruening-2021", "(63c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't email me yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "email"), ("implicit", "secondObject")] }

def ex_63c_email_pp : Datum :=
  { id := "bruening2021_63c_email_pp"
    source := ⟨"bruening-2021", "(63c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't email to me yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "email"), ("implicit", "directObject")] }

def ex_63c_text_doc : Datum :=
  { id := "bruening2021_63c_text_doc"
    source := ⟨"bruening-2021", "(63c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't text me yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "text"), ("implicit", "secondObject")] }

def ex_63c_text_pp : Datum :=
  { id := "bruening2021_63c_text_pp"
    source := ⟨"bruening-2021", "(63c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't text to me yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "text"), ("implicit", "directObject")] }

def ex_63c_telegraph_doc : Datum :=
  { id := "bruening2021_63c_telegraph_doc"
    source := ⟨"bruening-2021", "(63c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't telegraph me yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "telegraph"), ("implicit", "secondObject")] }

def ex_63c_telegraph_pp : Datum :=
  { id := "bruening2021_63c_telegraph_pp"
    source := ⟨"bruening-2021", "(63c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't telegraph to me yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "telegraph"), ("implicit", "directObject")] }

def ex_63d_doc : Datum :=
  { id := "bruening2021_63d_doc"
    source := ⟨"bruening-2021", "(63d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't pay me yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pay"), ("implicit", "secondObject")] }

def ex_63d_pp : Datum :=
  { id := "bruening2021_63d_pp"
    source := ⟨"bruening-2021", "(63d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She didn't pay to me yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pay"), ("implicit", "directObject")] }

def ex_63e_doc : Datum :=
  { id := "bruening2021_63e_doc"
    source := ⟨"bruening-2021", "(63e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They didn't serve us yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "serve"), ("implicit", "secondObject")] }

def ex_63e_pp : Datum :=
  { id := "bruening2021_63e_pp"
    source := ⟨"bruening-2021", "(63e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They didn't serve to us yet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "serve"), ("implicit", "directObject")] }

def ex_63f_doc : Datum :=
  { id := "bruening2021_63f_doc"
    source := ⟨"bruening-2021", "(63f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You promised me!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "promise"), ("implicit", "secondObject")] }

def ex_63f_pp : Datum :=
  { id := "bruening2021_63f_pp"
    source := ⟨"bruening-2021", "(63f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You promised to me!"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "promise"), ("implicit", "directObject")] }

def ex_63g_doc : Datum :=
  { id := "bruening2021_63g_doc"
    source := ⟨"bruening-2021", "(63g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She teaches special-needs children."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "teach"), ("implicit", "secondObject")] }

def ex_63g_pp : Datum :=
  { id := "bruening2021_63g_pp"
    source := ⟨"bruening-2021", "(63g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She teaches to special-needs children."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "teach"), ("implicit", "directObject")] }

def ex_63h_doc : Datum :=
  { id := "bruening2021_63h_doc"
    source := ⟨"bruening-2021", "(63h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They're feeding the seals right now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "feed"), ("implicit", "secondObject")] }

def ex_63h_pp : Datum :=
  { id := "bruening2021_63h_pp"
    source := ⟨"bruening-2021", "(63h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They're feeding to the seals right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "feed"), ("implicit", "directObject")] }

def ex_64a_doc : Datum :=
  { id := "bruening2021_64a_doc"
    source := ⟨"bruening-2021", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wouldn't pass me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pass"), ("implicit", "secondObject")] }

def ex_64a_pp : Datum :=
  { id := "bruening2021_64a_pp"
    source := ⟨"bruening-2021", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wouldn't pass to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "pass"), ("implicit", "directObject")] }

def ex_64b_doc : Datum :=
  { id := "bruening2021_64b_doc"
    source := ⟨"bruening-2021", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wouldn't throw me."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "throw"), ("implicit", "secondObject")] }

def ex_64b_pp : Datum :=
  { id := "bruening2021_64b_pp"
    source := ⟨"bruening-2021", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wouldn't throw to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "throw"), ("implicit", "directObject")] }

def ex_64c_doc : Datum :=
  { id := "bruening2021_64c_doc"
    source := ⟨"bruening-2021", "(64c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She gives the Red Cross."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb", "give"), ("implicit", "secondObject")] }

def ex_64c_pp : Datum :=
  { id := "bruening2021_64c_pp"
    source := ⟨"bruening-2021", "(64c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She gives to the Red Cross."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "give"), ("implicit", "directObject")] }

def ex_65a : Datum :=
  { id := "bruening2021_65a"
    source := ⟨"bruening-2021", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wrote to me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "write"), ("implicit", "directObject")] }

def ex_65b : Datum :=
  { id := "bruening2021_65b"
    source := ⟨"bruening-2021", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wrote me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb", "write"), ("implicit", "secondObject")] }

def all : List Datum := [ex_10a, ex_10b, ex_10c, ex_10d, ex_10e, ex_10f, ex_10g, ex_10h, ex_11a, ex_11b, ex_11c, ex_11d, ex_11e, ex_11f, ex_11g, ex_63a_doc, ex_63a_pp, ex_63b_doc, ex_63b_pp, ex_63c_email_doc, ex_63c_email_pp, ex_63c_text_doc, ex_63c_text_pp, ex_63c_telegraph_doc, ex_63c_telegraph_pp, ex_63d_doc, ex_63d_pp, ex_63e_doc, ex_63e_pp, ex_63f_doc, ex_63f_pp, ex_63g_doc, ex_63g_pp, ex_63h_doc, ex_63h_pp, ex_64a_doc, ex_64a_pp, ex_64b_doc, ex_64b_pp, ex_64c_doc, ex_64c_pp, ex_65a, ex_65b]

end Bruening2021.Examples
