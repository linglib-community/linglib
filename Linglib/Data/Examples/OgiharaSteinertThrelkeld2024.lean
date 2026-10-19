module

public import Linglib.Data.Examples.Schema

/-!
# `OgiharaSteinertThrelkeld2024` — typed example data

Auto-generated from `Linglib/Data/Examples/OgiharaSteinertThrelkeld2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace OgiharaSteinertThrelkeld2024.Examples`.
-/

@[expose] public section

namespace OgiharaSteinertThrelkeld2024.Examples

def ost2024_left_country : Datum :=
  { id := "ost2024_left_country"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left the country before anything happened."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("reading", "nonCommittal")] }

def ost2024_before_counterfactual_mozart : Datum :=
  { id := "ost2024_before_counterfactual_mozart"
    source := ⟨"beaver-condoravdi-2003", "(40)"⟩
    reportedIn := some ⟨"ogihara-steinert-threlkeld-2024", "(6a)"⟩
    language := "stan1293"
    primaryText := "Mozart died before he finished the Requiem."
    glossedTokens := []
    context := "Counterfactual reading of *before*: Mozart never finished the Requiem."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "veridicality"), ("connective", "before"), ("complement_entailed", "false"), ("precursor", "true")] }

def ost2024_beethoven : Datum :=
  { id := "ost2024_beethoven"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Beethoven died before he composed his 11th symphony."
    glossedTokens := []
    context := "Beethoven composed no 11th symphony, and nothing at his death was leading to one: he did not even compose a 10th."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antiVeridical"), ("precursor", "false")] }

def ost2024_ohtani : Datum :=
  { id := "ost2024_ohtani"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the 2021 MLB season will be over before Shohei Ohtani earns his 10th win of the season."
    glossedTokens := []
    context := "Uttered in the middle of September 2021. The A-time is the end of the 2021 MLB season; the complement (Ohtani's 10th win) can only occur during the season, before the A-time — a counterexample to B&C's forward-branching alt(w,t)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "counterfactual")] }

def ost2024_snow : Datum :=
  { id := "ost2024_snow"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "2020 might come to an end before it snows for the first time this year."
    glossedTokens := []
    context := "Uttered on Christmas Day 2020. *This year* refers to 2020; the first snow of 2020 can only occur in 2020, so a modal alternative placing it after 2020 does not work."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "nonCommittal")] }

def ost2024_nostradamus : Datum :=
  { id := "ost2024_nostradamus"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "July 1999 will come to an end before Nostradamus' prophecy about the end of the world comes true."
    glossedTokens := []
    context := "Uttered a few minutes before the end of July 1999. The prophecy (a King of terror in July 1999) can only come true in July 1999 — not after."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "counterfactual")] }

def ost2024_ohtani_japanese : Datum :=
  { id := "ost2024_ohtani_japanese"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(21)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Zannen-na koto-ni, 2021-nen-no siizun-wa Ootani-ga zyussyoome-o ageru mae ni owat-ta."
    glossedTokens := [("Zannen-na koto-ni", "unfortunately"), ("2021-nen-no", "2021-year-GEN"), ("siizun-wa", "season-TOP"), ("Ootani-ga", "Ohtani-NOM"), ("zyussyoome-o", "10th win-ACC"), ("ageru", "earn.NON-PAST"), ("mae", "before"), ("ni", "at"), ("owat-ta", "end-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "bc_counterexample"), ("reading", "counterfactual"), ("connective", "mae"), ("matrixTense", "past"), ("embeddedTense", "present")] }

def ost2024_noncommittal_available : Datum :=
  { id := "ost2024_noncommittal_available"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will leave the party before Bill gets drunk."
    glossedTokens := []
    context := "Non-committal reading available: felicitous and true if Mary thinks that Bill might get drunk at the party, which she does not wish to see, and will leave the party early."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "noncommittal"), ("noncommittal_available", "true")] }

def ost2024_noncommittal_unavailable : Datum :=
  { id := "ost2024_noncommittal_unavailable"
    source := ⟨"ogihara-steinert-threlkeld-2024", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary will leave the party before Quebec becomes an independent country."
    glossedTokens := []
    context := "Non-committal reading unavailable (#): in the same situation as (22a), Mary's leaving the party has nothing to do with the possibility of Quebec's becoming an independent country."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "noncommittal"), ("noncommittal_available", "false")] }

def all : List Datum := [ost2024_left_country, ost2024_before_counterfactual_mozart, ost2024_beethoven, ost2024_ohtani, ost2024_snow, ost2024_nostradamus, ost2024_ohtani_japanese, ost2024_noncommittal_available, ost2024_noncommittal_unavailable]

end OgiharaSteinertThrelkeld2024.Examples
