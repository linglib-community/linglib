module

public import Linglib.Data.Examples.Schema

/-!
# `JereticEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/JereticEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace JereticEtAl2025.Examples`.
-/

@[expose] public section

namespace JereticEtAl2025.Examples

def jeretic2025_1a : Datum :=
  { id := "jeretic2025_1a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lea broke all her arms."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "universal"), ("dual", "false")] }

def jeretic2025_1c : Datum :=
  { id := "jeretic2025_1c"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lea broke both her arms."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "universal"), ("dual", "true")] }

def jeretic2025_2a : Datum :=
  { id := "jeretic2025_2a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Léa s'est cassé tous les bras."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "universal"), ("dual", "false")] }

def jeretic2025_2b : Datum :=
  { id := "jeretic2025_2b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(2b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Léa s'est cassé les deux bras."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "universal"), ("dual", "true")] }

def jeretic2025_6a : Datum :=
  { id := "jeretic2025_6a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the sides of this sheet of paper has been used."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "negative"), ("dual", "false")] }

def jeretic2025_6a_neither : Datum :=
  { id := "jeretic2025_6a_neither"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Neither of the sides of this sheet of paper has been used."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "negative"), ("dual", "true")] }

def jeretic2025_6b : Datum :=
  { id := "jeretic2025_6b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aucun des côtés de cette feuille n'a été utilisé."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "negative"), ("dual", "false")] }

def jeretic2025_6c : Datum :=
  { id := "jeretic2025_6c"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(6c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Keine der Seiten dieses Blattes wurde verwendet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "german"), ("slot", "negative"), ("dual", "false")] }

def jeretic2025_7a : Datum :=
  { id := "jeretic2025_7a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(7a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Á hvor-um handlegg-num brotna-ði hún?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "icelandic"), ("slot", "which"), ("dual", "true")] }

def jeretic2025_7b : Datum :=
  { id := "jeretic2025_7b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(7b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Á hvaða handlegg brotna-ði hún?"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("language", "icelandic"), ("slot", "which"), ("dual", "false")] }

def jeretic2025_8a : Datum :=
  { id := "jeretic2025_8a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(8a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa dotti-no ude-o o-tta-no?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "which"), ("dual", "true")] }

def jeretic2025_8b : Datum :=
  { id := "jeretic2025_8b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(8b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa dono ude-o o-tta-no?"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "which"), ("dual", "false")] }

def jeretic2025_9a : Datum :=
  { id := "jeretic2025_9a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(9a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa dotti-no ude-mo o-tta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "each"), ("dual", "true")] }

def jeretic2025_9b : Datum :=
  { id := "jeretic2025_9b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(9b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa dono ude-mo o-tta."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "each"), ("dual", "false")] }

def jeretic2025_10a : Datum :=
  { id := "jeretic2025_10a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(10a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa dotti-no ude-ka-o o-tta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "one"), ("dual", "true")] }

def jeretic2025_10b : Datum :=
  { id := "jeretic2025_10b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(10b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa dono ude-ka-o o-tta."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "one"), ("dual", "false")] }

def jeretic2025_11a : Datum :=
  { id := "jeretic2025_11a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which arm hurts you?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "which"), ("dual", "false")] }

def jeretic2025_11b : Datum :=
  { id := "jeretic2025_11b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have a problem with each arm."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "each"), ("dual", "false")] }

def jeretic2025_11c : Datum :=
  { id := "jeretic2025_11c"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "One arm hurts me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "one"), ("dual", "false")] }

def jeretic2025_12a : Datum :=
  { id := "jeretic2025_12a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(12a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Quel bras te fait mal?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "which"), ("dual", "false")] }

def jeretic2025_12b : Datum :=
  { id := "jeretic2025_12b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(12b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai un problème à chaque bras."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "each"), ("dual", "false")] }

def jeretic2025_12c : Datum :=
  { id := "jeretic2025_12c"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(12c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Un bras me fait mal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "one"), ("dual", "false")] }

def jeretic2025_80a : Datum :=
  { id := "jeretic2025_80a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(80a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She came twice to visit us, and she always brought us flowers."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "always"), ("dual", "false")] }

def jeretic2025_80b : Datum :=
  { id := "jeretic2025_80b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(80b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She came twice to visit us, and both times she brought us flowers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "english"), ("slot", "always"), ("dual", "true")] }

def jeretic2025_81a : Datum :=
  { id := "jeretic2025_81a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(81a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Elle est venue deux fois nous rendre visite, et elle nous a toujours apporté des fleurs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "french"), ("slot", "always"), ("dual", "false")] }

def jeretic2025_83a : Datum :=
  { id := "jeretic2025_83a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(83a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat uns zweimal besucht und uns immer Blumen mitgebracht."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "german"), ("slot", "always"), ("dual", "false")] }

def jeretic2025_83b : Datum :=
  { id := "jeretic2025_83b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(83b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kanozyo-wa watasi-tati-o ni-kai tazunete-kite, itu-mo hana-o motte-kita."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "always"), ("dual", "false")] }

def jeretic2025_85 : Datum :=
  { id := "jeretic2025_85"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(85)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kanozyo-wa watasi-tati-o ni-kai tazunete-kite, ni-kai hana-o motte-kita."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("language", "japanese"), ("slot", "always"), ("dual", "true")] }

def jeretic2025_36 : Datum :=
  { id := "jeretic2025_36"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(36)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Računalnik-a sta pokvarjen-a"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("slot", "definite"), ("dual", "true")] }

def jeretic2025_25a : Datum :=
  { id := "jeretic2025_25a"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(25a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Tous les verres sont pleins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("example", "25")] }

def jeretic2025_25b : Datum :=
  { id := "jeretic2025_25b"
    source := ⟨"jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025", "(25b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les deux verres sont pleins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("example", "25")] }

def all : List Datum := [jeretic2025_1a, jeretic2025_1c, jeretic2025_2a, jeretic2025_2b, jeretic2025_6a, jeretic2025_6a_neither, jeretic2025_6b, jeretic2025_6c, jeretic2025_7a, jeretic2025_7b, jeretic2025_8a, jeretic2025_8b, jeretic2025_9a, jeretic2025_9b, jeretic2025_10a, jeretic2025_10b, jeretic2025_11a, jeretic2025_11b, jeretic2025_11c, jeretic2025_12a, jeretic2025_12b, jeretic2025_12c, jeretic2025_80a, jeretic2025_80b, jeretic2025_81a, jeretic2025_83a, jeretic2025_83b, jeretic2025_85, jeretic2025_36, jeretic2025_25a, jeretic2025_25b]

end JereticEtAl2025.Examples
