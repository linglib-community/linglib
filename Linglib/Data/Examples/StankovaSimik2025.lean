module

public import Linglib.Data.Examples.Schema

/-!
# `StankovaSimik2025` — typed example data

Auto-generated from `Linglib/Data/Examples/StankovaSimik2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace StankovaSimik2025.Examples`.
-/

@[expose] public section

namespace StankovaSimik2025.Examples

def ex13_v1_nci : Datum :=
  { id := "stankovasimik2025_ex13_v1_nci"
    source := ⟨"stankova-simik-2025", "(13) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezasadila tam Dana žádné květiny?"
    glossedTokens := [("Nezasadila", "NEG.planted"), ("tam", "there"), ("Dana", "Dana"), ("žádné", "DET.NCI"), ("květiny", "flowers")]
    context := "Dana má na zahradě záhon, který vybudovala před rokem. ('Dana has a garden bed, which she built a year ago.' — neutral, implying neither p nor ¬p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "nci"), ("context", "neutral")] }

def ex13_v1_ppi : Datum :=
  { id := "stankovasimik2025_ex13_v1_ppi"
    source := ⟨"stankova-simik-2025", "(13) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezasadila tam Dana nějaké květiny?"
    glossedTokens := [("Nezasadila", "NEG.planted"), ("tam", "there"), ("Dana", "Dana"), ("nějaké", "DET.PPI"), ("květiny", "flowers")]
    context := "Dana má na zahradě záhon, který vybudovala před rokem. ('Dana has a garden bed, which she built a year ago.' — neutral, implying neither p nor ¬p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "neutral")] }

def ex13_nonv1_nci : Datum :=
  { id := "stankovasimik2025_ex13_nonv1_nci"
    source := ⟨"stankova-simik-2025", "(13) B′"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Dana tam nezasadila žádné květiny?"
    glossedTokens := [("Dana", "Dana"), ("tam", "there"), ("nezasadila", "NEG.planted"), ("žádné", "DET.NCI"), ("květiny", "flowers")]
    context := "Dana má na zahradě záhon, kam zasadila zeleninu. ('Dana has a garden bed, where she planted vegetables.' — negative, implying ¬p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "nonv1"), ("indefinite", "nci"), ("context", "negative")] }

def ex13_nonv1_ppi : Datum :=
  { id := "stankovasimik2025_ex13_nonv1_ppi"
    source := ⟨"stankova-simik-2025", "(13) B′"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Dana tam nezasadila nějaké květiny?"
    glossedTokens := [("Dana", "Dana"), ("tam", "there"), ("nezasadila", "NEG.planted"), ("nějaké", "DET.PPI"), ("květiny", "flowers")]
    context := "Dana má na zahradě záhon, kam zasadila zeleninu. ('Dana has a garden bed, where she planted vegetables.' — negative, implying ¬p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "nonv1"), ("indefinite", "ppi"), ("context", "negative")] }

def ex14 : Datum :=
  { id := "stankovasimik2025_ex14"
    source := ⟨"stankova-simik-2025", "(14) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nevyhrála Eva nějakou cenu?"
    glossedTokens := [("Nevyhrála", "NEG.won"), ("Eva", "Eva"), ("nějakou", "DET.PPI"), ("cenu", "prize")]
    context := "Eva se zúčastnila lingvistické olympiády, kde skončila jako první. ('Eva participated in a linguistic olympiad, where she won the first place.' — positive evidence for p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "positive")] }

def ex17_ppi : Datum :=
  { id := "stankovasimik2025_ex17_ppi"
    source := ⟨"stankova-simik-2025", "(17) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezarezervoval si Mikuláš náhodou nějaké sedadlo?"
    glossedTokens := [("Nezarezervoval", "NEG.booked"), ("si", "REFL"), ("Mikuláš", "Mikuláš"), ("náhodou", "NÁHODOU"), ("nějaké", "DET.PPI"), ("sedadlo", "seat")]
    context := "Mikuláš cestoval vlakem, který jel do Košic. ('Mikuláš was on the train which went to Košice.' — neutral)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "neutral")] }

def ex17_nci : Datum :=
  { id := "stankovasimik2025_ex17_nci"
    source := ⟨"stankova-simik-2025", "(17) B"⟩
    reportedIn := none
    method := some .experiment
    language := "czec1258"
    primaryText := "Nezarezervoval si Mikuláš náhodou žádné sedadlo?"
    glossedTokens := [("Nezarezervoval", "NEG.booked"), ("si", "REFL"), ("Mikuláš", "Mikuláš"), ("náhodou", "NÁHODOU"), ("žádné", "DET.NCI"), ("sedadlo", "seat")]
    context := "Mikuláš cestoval vlakem, který jel do Košic. ('Mikuláš was on the train which went to Košice.' — neutral)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "v1"), ("indefinite", "nci"), ("context", "neutral")] }

def ex18 : Datum :=
  { id := "stankovasimik2025_ex18"
    source := ⟨"stankova-simik-2025", "(18) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "A Petr si náhodou nekoupil nějakou knihu?"
    glossedTokens := [("A", "and"), ("Petr", "Petr"), ("si", "REFL"), ("náhodou", "NÁHODOU"), ("nekoupil", "NEG.bought"), ("nějakou", "DET.PPI"), ("knihu", "book")]
    context := "Hanka si koupila knihu. ('Hanka bought a book.')"
    judgment := .acceptable
    alternatives := [("A Petr si náhodou nekoupil žádnou knihu?", .ungrammatical)]
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "nonv1"), ("indefinite", "ppi")] }

def all : List Datum := [ex13_v1_nci, ex13_v1_ppi, ex13_nonv1_nci, ex13_nonv1_ppi, ex14, ex17_ppi, ex17_nci, ex18]

end StankovaSimik2025.Examples
