module

public import Linglib.Data.Examples.Schema

/-!
# `Chierchia2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Chierchia2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Chierchia2013.Examples`.
-/

@[expose] public section

namespace Chierchia2013.Examples

def ex1a : Datum :=
  { id := "chierchia2013_ex1a"
    source := ⟨"chierchia-2013", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If everything will go well, we'll hire either Mary or Sue"
    glossedTokens := []
    context := "Background: what will be the future departmental hires?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "conditionalConsequent"), ("reading", "exclusive")] }

def ex1b : Datum :=
  { id := "chierchia2013_ex1b"
    source := ⟨"chierchia-2013", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If we hire either Mary or Sue, everything will go well"
    glossedTokens := []
    context := "Background: what will be the future departmental hires?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "conditionalAntecedent"), ("reading", "inclusive")] }

def ex5a : Datum :=
  { id := "chierchia2013_ex5a"
    source := ⟨"chierchia-2013", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone here either likes Mary or likes Sue and will write to the dean"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "everyScope"), ("reading", "exclusive")] }

def ex5b : Datum :=
  { id := "chierchia2013_ex5b"
    source := ⟨"chierchia-2013", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone here who either likes Mary or likes Sue will write to the dean"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "universalRestrictor"), ("reading", "inclusive")] }

def ex12a : Datum :=
  { id := "chierchia2013_ex12a"
    source := ⟨"chierchia-2013", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Somebody in the department intends to hire either Mary or Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "positiveQuantifierScope"), ("reading", "exclusive")] }

def ex12b : Datum :=
  { id := "chierchia2013_ex12b"
    source := ⟨"chierchia-2013", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody in the department intends to hire either Mary or Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "nobody"), ("reading", "inclusive")] }

def ex12c : Datum :=
  { id := "chierchia2013_ex12c"
    source := ⟨"chierchia-2013", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John intends to hire Mary or Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "matrix"), ("reading", "exclusive")] }

def ex12d : Datum :=
  { id := "chierchia2013_ex12d"
    source := ⟨"chierchia-2013", "(12d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Molly does not intend to hire Mary or Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "negation"), ("reading", "inclusive")] }

def ex13 : Datum :=
  { id := "chierchia2013_ex13"
    source := ⟨"chierchia-2013", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody wants to hire Mary or Sue, anymore"
    glossedTokens := []
    context := "We are aware that Sue and Mary can only be hired together. We discussed it at length. And at this point, ... we all agreed to hire them both."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "nobody"), ("reading", "exclusive"), ("forced", "true")] }

def ex19a : Datum :=
  { id := "chierchia2013_ex19a"
    source := ⟨"chierchia-2013", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We won't hire Mary or Sue"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "or"), ("position", "negation"), ("reading", "inclusive")] }

def ex15ia : Datum :=
  { id := "chierchia2013_ex15ia"
    source := ⟨"chierchia-2013", "(15i a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you are hungry, there are any cookies in the oven"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "conditionalConsequent")] }

def ex15ib : Datum :=
  { id := "chierchia2013_ex15ib"
    source := ⟨"chierchia-2013", "(15i b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there are any cookies in the oven, you won't go hungry"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "conditionalAntecedent")] }

def ex15iia : Datum :=
  { id := "chierchia2013_ex15iia"
    source := ⟨"chierchia-2013", "(15ii a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone still has any cookies in the oven"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "everyScope")] }

def ex15iib : Datum :=
  { id := "chierchia2013_ex15iib"
    source := ⟨"chierchia-2013", "(15ii b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who still has any cookies in the oven should turn the oven off"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "universalRestrictor")] }

def ex15iiia : Datum :=
  { id := "chierchia2013_ex15iiia"
    source := ⟨"chierchia-2013", "(15iii a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Somebody brought any cookies"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "positiveQuantifierScope")] }

def ex15iiib : Datum :=
  { id := "chierchia2013_ex15iiib"
    source := ⟨"chierchia-2013", "(15iii b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody brought any cookies"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "nobody")] }

def ex16ia : Datum :=
  { id := "chierchia2013_ex16ia"
    source := ⟨"chierchia-2013", "(16i a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you visit Sienna, you should ever try homemade ricciarellis"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "conditionalConsequent")] }

def ex16ib : Datum :=
  { id := "chierchia2013_ex16ib"
    source := ⟨"chierchia-2013", "(16i b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you ever try homemade ricciarellis, you will become addicted"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "conditionalAntecedent")] }

def ex16iia : Datum :=
  { id := "chierchia2013_ex16iia"
    source := ⟨"chierchia-2013", "(16ii a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone ever ate homemade ricciarellis"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "everyScope")] }

def ex16iib : Datum :=
  { id := "chierchia2013_ex16iib"
    source := ⟨"chierchia-2013", "(16ii b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who ever ate homemade ricciarellis became addicted"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "universalRestrictor")] }

def ex16iiia : Datum :=
  { id := "chierchia2013_ex16iiia"
    source := ⟨"chierchia-2013", "(16iii a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Somebody ever tried homemade ricciarellis"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "positiveQuantifierScope")] }

def ex16iiib : Datum :=
  { id := "chierchia2013_ex16iiib"
    source := ⟨"chierchia-2013", "(16iii b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody ever tried homemade ricciarellis"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "nobody")] }

def ex21a : Datum :=
  { id := "chierchia2013_ex21a"
    source := ⟨"chierchia-2013", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are any cookies left"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "matrix")] }

def ex21b : Datum :=
  { id := "chierchia2013_ex21b"
    source := ⟨"chierchia-2013", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There ever were cookies in this house"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "matrix")] }

def ex21c : Datum :=
  { id := "chierchia2013_ex21c"
    source := ⟨"chierchia-2013", "(21c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that there are any cookies left"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "doubtVerb")] }

def ex21d : Datum :=
  { id := "chierchia2013_ex21d"
    source := ⟨"chierchia-2013", "(21d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that there ever were cookies in this house"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "doubtVerb")] }

def ex70ai : Datum :=
  { id := "chierchia2013_ex70ai"
    source := ⟨"chierchia-2013", "(70a i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may read any of these books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "modalPossibility")] }

def ex70aii : Datum :=
  { id := "chierchia2013_ex70aii"
    source := ⟨"chierchia-2013", "(70a ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may ever read these books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "modalPossibility")] }

def ex70ci : Datum :=
  { id := "chierchia2013_ex70ci"
    source := ⟨"chierchia-2013", "(70c i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Take any apple"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "any"), ("position", "imperative")] }

def ex70cii : Datum :=
  { id := "chierchia2013_ex70cii"
    source := ⟨"chierchia-2013", "(70c ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ever read these books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "ever"), ("position", "imperative")] }

def ex70di : Datum :=
  { id := "chierchia2013_ex70di"
    source := ⟨"chierchia-2013", "(70d i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Dubito che Leo abbia letto alcun libro di testo di linguistica"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "alcuno"), ("position", "doubtVerb")] }

def ex70dii : Datum :=
  { id := "chierchia2013_ex70dii"
    source := ⟨"chierchia-2013", "(70d ii)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Puoi leggere alcun libro di linguistica"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("item", "alcuno"), ("position", "modalPossibility")] }

def ex70ei : Datum :=
  { id := "chierchia2013_ex70ei"
    source := ⟨"chierchia-2013", "(70e i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Leo non ha letto qualsiasi libro di testo di linguistica"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("item", "qualsiasi"), ("position", "negation")] }

def ex70eii : Datum :=
  { id := "chierchia2013_ex70eii"
    source := ⟨"chierchia-2013", "(70e ii)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Puoi leggere qualsiasi libro di testo di linguistica"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "qualsiasi"), ("position", "modalPossibility")] }

def all : List Datum := [ex1a, ex1b, ex5a, ex5b, ex12a, ex12b, ex12c, ex12d, ex13, ex19a, ex15ia, ex15ib, ex15iia, ex15iib, ex15iiia, ex15iiib, ex16ia, ex16ib, ex16iia, ex16iib, ex16iiia, ex16iiib, ex21a, ex21b, ex21c, ex21d, ex70ai, ex70aii, ex70ci, ex70cii, ex70di, ex70dii, ex70ei, ex70eii]

end Chierchia2013.Examples
