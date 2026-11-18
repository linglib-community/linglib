module

public import Linglib.Data.Examples.Schema

/-!
# `Gasparri2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Gasparri2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gasparri2025.Examples`.
-/

@[expose] public section

namespace Gasparri2025.Examples

def ex4a : Datum :=
  { id := "gasparri2025_ex4a"
    source := ⟨"gasparri-2025", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruth is common."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex4b : Datum :=
  { id := "gasparri2025_ex4b"
    source := ⟨"gasparri-2025", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruth is a dancer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex4c : Datum :=
  { id := "gasparri2025_ex4c"
    source := ⟨"gasparri-2025", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tiger is striped."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex4d : Datum :=
  { id := "gasparri2025_ex4d"
    source := ⟨"gasparri-2025", "(4d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tiger is widespread."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex5a : Datum :=
  { id := "gasparri2025_ex5a"
    source := ⟨"gasparri-2025", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Marias are common."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "pluralName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex5b : Datum :=
  { id := "gasparri2025_ex5b"
    source := ⟨"gasparri-2025", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(The) Jamals (in my town) are smart."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "pluralName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex6a : Datum :=
  { id := "gasparri2025_ex6a"
    source := ⟨"gasparri-2025", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruth is 40 years old."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex6b : Datum :=
  { id := "gasparri2025_ex6b"
    source := ⟨"gasparri-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruth is typically 40 years old."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex7a : Datum :=
  { id := "gasparri2025_ex7a"
    source := ⟨"gasparri-2025", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Rutgers professor is 40 years old."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex7b : Datum :=
  { id := "gasparri2025_ex7b"
    source := ⟨"gasparri-2025", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Rutgers professor is generally 40 years old."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex8a : Datum :=
  { id := "gasparri2025_ex8a"
    source := ⟨"gasparri-2025", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Coke bottle has a narrow neck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex8b : Datum :=
  { id := "gasparri2025_ex8b"
    source := ⟨"gasparri-2025", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Coke bottle generally has a narrow neck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex11a : Datum :=
  { id := "gasparri2025_ex11a"
    source := ⟨"gasparri-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In English, Leslie is generally a woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "locative"), ("qadv", "yes"), ("level", "characterizing")] }

def ex11b : Datum :=
  { id := "gasparri2025_ex11b"
    source := ⟨"gasparri-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In England, Leslie is generally a woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "locative"), ("qadv", "yes"), ("level", "characterizing")] }

def ex12 : Datum :=
  { id := "gasparri2025_ex12"
    source := ⟨"gasparri-2025", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Italian Andrea is generally (a) male, German Andrea is generally (a) female."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .marginal), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedName"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex13 : Datum :=
  { id := "gasparri2025_ex13"
    source := ⟨"gasparri-2025", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Italian Andrea is (a) male, German Andrea is (a) female."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex14a : Datum :=
  { id := "gasparri2025_ex14a"
    source := ⟨"gasparri-2025", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dish is nutritious."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex14b : Datum :=
  { id := "gasparri2025_ex14b"
    source := ⟨"gasparri-2025", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Italian dish is nutritious."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "modifiedCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex14c : Datum :=
  { id := "gasparri2025_ex14c"
    source := ⟨"gasparri-2025", "(14c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Italian dishes are nutritious."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareCommonPlural"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex15a : Datum :=
  { id := "gasparri2025_ex15a"
    source := ⟨"gasparri-2025", "(15a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'Andrea italiano è generalmente (un) maschio; l'Andrea tedesca è generalmente (una) femmina."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedName"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex15b : Datum :=
  { id := "gasparri2025_ex15b"
    source := ⟨"gasparri-2025", "(15b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "L'Andrea italien est généralement (un) homme, l'Andrea allemande est généralement (une) femme."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedName"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex16a : Datum :=
  { id := "gasparri2025_ex16a"
    source := ⟨"gasparri-2025", "(16a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'Andrea italiano è (un) maschio, l'Andrea tedesca è (una) femmina."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex16b : Datum :=
  { id := "gasparri2025_ex16b"
    source := ⟨"gasparri-2025", "(16b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "L'Andrea italien est (un) homme, l'Andrea allemande est (une) femme."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex17a : Datum :=
  { id := "gasparri2025_ex17a"
    source := ⟨"gasparri-2025", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Children who grow a new tooth show it off."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareCommonPlural"), ("context", "binding"), ("qadv", "no"), ("level", "characterizing")] }

def ex17b : Datum :=
  { id := "gasparri2025_ex17b"
    source := ⟨"gasparri-2025", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lions that see a gazelle chase it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareCommonPlural"), ("context", "binding"), ("qadv", "no"), ("level", "characterizing")] }

def ex18a : Datum :=
  { id := "gasparri2025_ex18a"
    source := ⟨"gasparri-2025", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The barn is typically red."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("token", .questionable), ("generic", .questionable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex18b : Datum :=
  { id := "gasparri2025_ex18b"
    source := ⟨"gasparri-2025", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every farm around here has a barn, and the barn is typically red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "binding"), ("qadv", "yes"), ("level", "characterizing")] }

def ex20 : Datum :=
  { id := "gasparri2025_ex20"
    source := ⟨"gasparri-2025", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman's husband is called Gerontius, and Gerontius is usually tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "binding"), ("qadv", "yes"), ("level", "characterizing")] }

def ex21 : Datum :=
  { id := "gasparri2025_ex21"
    source := ⟨"gasparri-2025", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the numbers, Ruth has good grades in biology, whereas Paul excels in latin."
    glossedTokens := []
    context := "We have collected data on school performance over the past 5 years across all public schools in the world, and categorized it by given name."
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "no"), ("level", "characterizing")] }

def ex22a : Datum :=
  { id := "gasparri2025_ex22a"
    source := ⟨"gasparri-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kangaroo rat is friendly to humans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex22b : Datum :=
  { id := "gasparri2025_ex22b"
    source := ⟨"gasparri-2025", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kangaroo rat is generally friendly to humans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "yes"), ("level", "characterizing")] }

def ex23b : Datum :=
  { id := "gasparri2025_ex23b"
    source := ⟨"gasparri-2025", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the numbers, Ruth generally has good grades in biology."
    glossedTokens := []
    context := "We have collected data on school performance over the past 5 years across all public schools in the world, and categorized it by given name."
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "yes"), ("level", "characterizing")] }

def ex26 : Datum :=
  { id := "gasparri2025_ex26"
    source := ⟨"gasparri-2025", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In other words, Paul falls in love with Ruth, not with Clementine."
    glossedTokens := []
    context := "People have a tendency to fall in love with individuals with names of comparable length to theirs."
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "no"), ("level", "characterizing")] }

def ex27a : Datum :=
  { id := "gasparri2025_ex27a"
    source := ⟨"gasparri-2025", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Regina is noble and determined."
    glossedTokens := []
    context := "Reading a baby-name catalog."
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "no"), ("level", "characterizing")] }

def ex28a : Datum :=
  { id := "gasparri2025_ex28a"
    source := ⟨"gasparri-2025", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Apolline is college educated, belongs to an upper middle class family, and her social milieu tends to engage in conspicuous consumption."
    glossedTokens := []
    context := "A discussion on the sociology of French names."
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "no"), ("level", "characterizing")] }

def ex28b : Datum :=
  { id := "gasparri2025_ex28b"
    source := ⟨"gasparri-2025", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Even in the absence of real data, we assume that Jean-Hubert hails from an affluent family and that Kevin has humble beginnings."
    glossedTokens := []
    context := "We have biases about names."
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "no"), ("level", "characterizing")] }

def ex31a : Datum :=
  { id := "gasparri2025_ex31a"
    source := ⟨"gasparri-2025", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The green bottle has a narrow neck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "modifiedCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex31b : Datum :=
  { id := "gasparri2025_ex31b"
    source := ⟨"gasparri-2025", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The green bottle has a narrow neck."
    glossedTokens := []
    context := "We manufacture three types of bottles in this plant: green, blue, and clear."
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedCommon"), ("context", "focusedKinds"), ("qadv", "no"), ("level", "characterizing")] }

def ex32a : Datum :=
  { id := "gasparri2025_ex32a"
    source := ⟨"gasparri-2025", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Indian rhinoceros is vertebrate."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "modifiedCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex32b : Datum :=
  { id := "gasparri2025_ex32b"
    source := ⟨"gasparri-2025", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mammal is vertebrate."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex32c : Datum :=
  { id := "gasparri2025_ex32c"
    source := ⟨"gasparri-2025", "(32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unlike the members of several other phyla, the mammal is vertebrate."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "contrast"), ("qadv", "no"), ("level", "characterizing")] }

def ex33a : Datum :=
  { id := "gasparri2025_ex33a"
    source := ⟨"gasparri-2025", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Romanov is refined and cultivated."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "definiteName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "characterizing")] }

def ex33b : Datum :=
  { id := "gasparri2025_ex33b"
    source := ⟨"gasparri-2025", "(33b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Romanov is refined and cultivated."
    glossedTokens := []
    context := "Reading a baby-name catalog."
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "naming"), ("qadv", "no"), ("level", "characterizing")] }

def ex34a : Datum :=
  { id := "gasparri2025_ex34a"
    source := ⟨"gasparri-2025", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(In India,) The dodo is extinct."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex34b : Datum :=
  { id := "gasparri2025_ex34b"
    source := ⟨"gasparri-2025", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book became common in the 19th century."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex34d : Datum :=
  { id := "gasparri2025_ex34d"
    source := ⟨"gasparri-2025", "(34d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(In Germany,) Tristan is extinct."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex34e : Datum :=
  { id := "gasparri2025_ex34e"
    source := ⟨"gasparri-2025", "(34e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John became common in the 19th century."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "bareName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex34f : Datum :=
  { id := "gasparri2025_ex34f"
    source := ⟨"gasparri-2025", "(34f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(In Germany,) 'Tristan' is extinct."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "quotedName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex34g : Datum :=
  { id := "gasparri2025_ex34g"
    source := ⟨"gasparri-2025", "(34g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'John' became common in the 19th century."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable)]
    paperFeatures := [("subject", "quotedName"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex35a : Datum :=
  { id := "gasparri2025_ex35a"
    source := ⟨"gasparri-2025", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mountains are widespread."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareCommonPlural"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex35b : Datum :=
  { id := "gasparri2025_ex35b"
    source := ⟨"gasparri-2025", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mountain is widespread."
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := [("generic", .questionable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex35c : Datum :=
  { id := "gasparri2025_ex35c"
    source := ⟨"gasparri-2025", "(35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mountain lakes emerged around 3.5 billion years ago."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject", "bareCommonPlural"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def ex35d : Datum :=
  { id := "gasparri2025_ex35d"
    source := ⟨"gasparri-2025", "(35d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mountain lake emerged around 3.5 billion years ago."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject", "definiteCommon"), ("context", "outOfTheBlue"), ("qadv", "no"), ("level", "kindLevel")] }

def all : List Datum := [ex4a, ex4b, ex4c, ex4d, ex5a, ex5b, ex6a, ex6b, ex7a, ex7b, ex8a, ex8b, ex11a, ex11b, ex12, ex13, ex14a, ex14b, ex14c, ex15a, ex15b, ex16a, ex16b, ex17a, ex17b, ex18a, ex18b, ex20, ex21, ex22a, ex22b, ex23b, ex26, ex27a, ex28a, ex28b, ex31a, ex31b, ex32a, ex32b, ex32c, ex33a, ex33b, ex34a, ex34b, ex34d, ex34e, ex34f, ex34g, ex35a, ex35b, ex35c, ex35d]

end Gasparri2025.Examples
