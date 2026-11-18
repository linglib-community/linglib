module

public import Linglib.Data.Examples.Schema

/-!
# `XuEtAl2024` — typed example data

Auto-generated from `Linglib/Data/Examples/XuEtAl2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace XuEtAl2024.Examples`.
-/

@[expose] public section

namespace XuEtAl2024.Examples

def ex_1 : Datum :=
  { id := "xuetal2024_1"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "locker"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("deedbox", .acceptable), ("strongbox", .acceptable), ("storeroom", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1940+")] }

def ex_2 : Datum :=
  { id := "xuetal2024_2"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "printer"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1940+")] }

def ex_3 : Datum :=
  { id := "xuetal2024_3"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dish"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1940+")] }

def ex_4 : Datum :=
  { id := "xuetal2024_4"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "birthday card"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1900+")] }

def ex_5 : Datum :=
  { id := "xuetal2024_5"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "urban renewal"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("renewal", .acceptable), ("renovation", .acceptable), ("urban-renovation", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1940+")] }

def ex_6 : Datum :=
  { id := "xuetal2024_6"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "spreadsheet"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1980+")] }

def ex_7 : Datum :=
  { id := "xuetal2024_7"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "antenne"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1900+")] }

def ex_8 : Datum :=
  { id := "xuetal2024_8"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "publicité"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("réclame", .acceptable), ("annonce", .acceptable), ("pub", .acceptable), ("emballage", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1920+")] }

def ex_9 : Datum :=
  { id := "xuetal2024_9"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "émuler"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1960+")] }

def ex_10 : Datum :=
  { id := "xuetal2024_10"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "turbine à gaz"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("turbine", .acceptable), ("générateur", .acceptable), ("moteur-gaz", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1900+")] }

def ex_11 : Datum :=
  { id := "xuetal2024_11"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "galaxie spirale"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1900+")] }

def ex_12 : Datum :=
  { id := "xuetal2024_12"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "boîte noire"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1940+")] }

def ex_13 : Datum :=
  { id := "xuetal2024_13"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "lähetys"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("lasti", .acceptable), ("rahti", .acceptable), ("toimitus", .acceptable), ("kuorma", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1900+")] }

def ex_14 : Datum :=
  { id := "xuetal2024_14"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "suodatin"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1920+")] }

def ex_15 : Datum :=
  { id := "xuetal2024_15"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "ajaa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "reuse"), ("interval", "1940+")] }

def ex_16 : Datum :=
  { id := "xuetal2024_16"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "sotarikos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("rikos", .acceptable), ("laittomuus", .acceptable), ("sota-laittomuus", .acceptable)]
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1900+")] }

def ex_17 : Datum :=
  { id := "xuetal2024_17"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "taisteluväsymys"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1900+")] }

def ex_18 : Datum :=
  { id := "xuetal2024_18"
    source := ⟨"xu-etal-2024", "Table 1"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "kauppa-apulainen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("strategy", "compound"), ("interval", "1920+")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18]

end XuEtAl2024.Examples
