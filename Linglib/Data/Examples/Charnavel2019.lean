module

public import Linglib.Data.Examples.Schema

/-!
# `Charnavel2019` — typed example data

Auto-generated from `Linglib/Data/Examples/Charnavel2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Charnavel2019.Examples`.
-/

@[expose] public section

namespace Charnavel2019.Examples

def ex_2_2a : Datum :=
  { id := "charnavel2019_2_2a"
    source := ⟨"charnavel-sportiche-2016", "p. 43"⟩
    reportedIn := some ⟨"charnavel-2019", "chapter 2, (2a)"⟩
    language := "stan1290"
    primaryText := "Cette auberge fait de l'ombre à son propre jardin et à celui de la maison voisine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("animacy", "inanimate")] }

def ex_2_2b : Datum :=
  { id := "charnavel2019_2_2b"
    source := ⟨"charnavel-sportiche-2016", "p. 43"⟩
    reportedIn := some ⟨"charnavel-2019", "chapter 2, (2b)"⟩
    language := "stan1290"
    primaryText := "Cette auberge bénéficie du fait que son propre jardin est plus spacieux que celui des auberges voisines."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Cette auberge bénéficie du fait que son jardin est plus spacieux que celui des auberges voisines.", .acceptable)]
    readings := []
    paperFeatures := [("animacy", "inanimate")] }

def ex_2_8b : Datum :=
  { id := "charnavel2019_2_8b"
    source := ⟨"charnavel-2019", "chapter 2, (8b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Marie bénéficie du fait que son propre hôtel est plus spacieux que celui de ses concurrents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_2_3a : Datum :=
  { id := "charnavel2019_2_3a"
    source := ⟨"charnavel-2019", "chapter 2, (3a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "La Terre tourne sur elle-même."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("animacy", "inanimate")] }

def ex_2_3b : Datum :=
  { id := "charnavel2019_2_3b"
    source := ⟨"charnavel-2019", "chapter 2, (3b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "La Terre a bénéficié du fait que des photos d'elle-même et de son satellite ont montré les effets néfastes de la pollution."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("La Terre a bénéficié du fait que des photos d'elle et de son satellite ont montré les effets néfastes de la pollution.", .acceptable)]
    readings := []
    paperFeatures := [("animacy", "inanimate")] }

def ex_4_5 : Datum :=
  { id := "charnavel2019_4_5"
    source := ⟨"charnavel-2019", "chapter 4, (5)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Robert dit que son rival a voté pour son propre projet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "attitude holder")] }

def ex_4_12 : Datum :=
  { id := "charnavel2019_4_12"
    source := ⟨"charnavel-2019", "chapter 4, (12)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le courage de Paul a sauvé des flammes sa propre maison et celle de ses voisins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "empathy locus")] }

def ex_4_14 : Datum :=
  { id := "charnavel2019_4_14"
    source := ⟨"charnavel-2019", "chapter 4, (14)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les commentaires des internautes sur elle-même ont atteint le moral de Lucie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "empathy locus")] }

def ex_4_17 : Datum :=
  { id := "charnavel2019_4_17"
    source := ⟨"charnavel-2019", "chapter 4, (17)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Irène tient de Paul qu'hier, plusieurs journaux ont parlé de lui-même."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Irène tient de Paul qu'hier, plusieurs journaux ont parlé de lui.", .acceptable)]
    readings := []
    paperFeatures := [("antecedent", "non-attitudinal source")] }

def ex_4_20 : Datum :=
  { id := "charnavel2019_4_20"
    source := ⟨"charnavel-2019", "chapter 4, (20)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le tableau à la gauche de l'épinette pourrait contenir une représentation d'elle-même."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Le tableau à la gauche de l'épinette pourrait contenir une représentation d'elle.", .acceptable)]
    readings := []
    paperFeatures := [("animacy", "inanimate"), ("antecedent", "deictic center")] }

def ex_4_21a : Datum :=
  { id := "charnavel2019_4_21a"
    source := ⟨"charnavel-2019", "chapter 4, (21a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Sur ce tableau de ton cher ancêtre peut-être fini par un de ses élèves, le professeur de musique est placé à droite de sa propre élève penchée sur la belle épinette."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_21b : Datum :=
  { id := "charnavel2019_4_21b"
    source := ⟨"charnavel-2019", "chapter 4, (21b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Sur ce tableau de ton cher ancêtre peut-être fini par un de ses élèves, il semble qu'à la droite du professeur de musique, sa propre élève joue de l'épinette."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Sur ce tableau de ton cher ancêtre peut-être fini par un de ses élèves, il semble qu'à la droite du professeur de musique, son élève joue de l'épinette.", .acceptable)]
    readings := []
    paperFeatures := [("antecedent", "deictic center")] }

def ex_4_25a : Datum :=
  { id := "charnavel2019_4_25a"
    source := ⟨"charnavel-2019", "chapter 4, (25a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Julie pense que ma mère et sa propre mère devraient se parler."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_25 : Datum :=
  { id := "charnavel2019_4_25"
    source := ⟨"charnavel-2019", "chapter 4, (25a) and (25b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Julie pense que ma propre mère et sa propre mère devraient se parler."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_25b : Datum :=
  { id := "charnavel2019_4_25b"
    source := ⟨"charnavel-2019", "chapter 4, (25b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Julie pense que ma propre mère et sa mère devraient se parler."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_27 : Datum :=
  { id := "charnavel2019_4_27"
    source := ⟨"charnavel-2019", "chapter 4, (27)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Solange pense que Cyril est fier d'elle-même et de sa propre fille."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_39a : Datum :=
  { id := "charnavel2019_4_39a"
    source := ⟨"charnavel-2019", "chapter 4, (39a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les commentaires des internautes sur elle-même et sa soeur ont atteint le moral de Lucie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_39b : Datum :=
  { id := "charnavel2019_4_39b"
    source := ⟨"charnavel-2019", "chapter 4, (39b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les commentaires des internautes sur elle et sa propre soeur ont atteint le moral de Lucie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_38 : Datum :=
  { id := "charnavel2019_4_38"
    source := ⟨"charnavel-2019", "chapter 4, (38)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Les commentaires des internautes sur elle-même sur le blog de Lucie ont atteint son moral."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_43a : Datum :=
  { id := "charnavel2019_4_43a"
    source := ⟨"charnavel-2019", "chapter 4, (43a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "La Terre tourne sur elle."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("La Terre tourne sur elle-même.", .acceptable)]
    readings := []
    paperFeatures := [("animacy", "inanimate")] }

def all : List Datum := [ex_2_2a, ex_2_2b, ex_2_8b, ex_2_3a, ex_2_3b, ex_4_5, ex_4_12, ex_4_14, ex_4_17, ex_4_20, ex_4_21a, ex_4_21b, ex_4_25a, ex_4_25, ex_4_25b, ex_4_27, ex_4_39a, ex_4_39b, ex_4_38, ex_4_43a]

end Charnavel2019.Examples
