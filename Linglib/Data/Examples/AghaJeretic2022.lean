module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `AghaJeretic2022` — typed example data

Auto-generated from `Linglib/Data/Examples/AghaJeretic2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AghaJeretic2022.Examples`.
-/

@[expose] public section

namespace AghaJeretic2022.Examples

def ex_2a : Datum :=
  { id := "aghajeretic2022_2a"
    source := ⟨"agha-jeretic-2022", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Colegio de México, you should take a taxi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("continuation", "but you could also take a bus if you have all morning"), ("continuation_felicity", "felicitous")] }

def ex_2b : Datum :=
  { id := "aghajeretic2022_2b"
    source := ⟨"agha-jeretic-2022", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Colegio de México, you have to take a taxi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("continuation", "but you could also take a bus if you have all morning"), ("continuation_felicity", "infelicitous")] }

def ex_3a : Datum :=
  { id := "aghajeretic2022_3a"
    source := ⟨"agha-jeretic-2022", "(3a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Tu dois partir."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "devoir"), ("force", "strong")] }

def ex_3b : Datum :=
  { id := "aghajeretic2022_3b"
    source := ⟨"agha-jeretic-2022", "(3b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Tu devrais partir."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "devoir+CF"), ("force", "weak"), ("derivation", "CF"), ("base", "necessity")] }

def ex_4a : Datum :=
  { id := "aghajeretic2022_4a"
    source := ⟨"agha-jeretic-2022", "(4a)"⟩
    reportedIn := none
    language := "java1254"
    primaryText := "Yu Dur mesthi nek omah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "mesthi"), ("force", "strong")] }

def ex_4b : Datum :=
  { id := "aghajeretic2022_4b"
    source := ⟨"agha-jeretic-2022", "(4b)"⟩
    reportedIn := none
    language := "java1254"
    primaryText := "Yu Dur mesthi-ne nek omah."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "mesthi+NE"), ("force", "weak"), ("derivation", "NE"), ("base", "necessity")] }

def should_pos_all : Datum :=
  { id := "aghajeretic2022_should_pos_all"
    source := ⟨"agha-jeretic-2022", "(8a), (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "ALL"), ("modal", "should")] }

def should_pos_none : Datum :=
  { id := "aghajeretic2022_should_pos_none"
    source := ⟨"agha-jeretic-2022", "(8a), (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "NONE"), ("modal", "should")] }

def should_pos_gap : Datum :=
  { id := "aghajeretic2022_should_pos_gap"
    source := ⟨"agha-jeretic-2022", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should take the right door to go to the living room."
    glossedTokens := []
    context := "Two doors lead to the living room; both are equally good options."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("modal", "should"), ("gap_detected", "true")] }

def should_neg_all : Datum :=
  { id := "aghajeretic2022_should_neg_all"
    source := ⟨"agha-jeretic-2022", "(9a), (20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "ALL"), ("modal", "should")] }

def should_neg_none : Datum :=
  { id := "aghajeretic2022_should_neg_none"
    source := ⟨"agha-jeretic-2022", "(9a), (20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "NONE"), ("modal", "should")] }

def should_neg_gap : Datum :=
  { id := "aghajeretic2022_should_neg_gap"
    source := ⟨"agha-jeretic-2022", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("modal", "should"), ("force", "weak"), ("negation", "clausemate"), ("gap_detected", "true"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "infelicitous")] }

def haveTo_pos_gap : Datum :=
  { id := "aghajeretic2022_haveTo_pos_gap"
    source := ⟨"agha-jeretic-2022", "(8b), (9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you have to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("modal", "have to"), ("gap_detected", "false"), ("classical_value", "false")] }

def haveTo_neg_gap : Datum :=
  { id := "aghajeretic2022_haveTo_neg_gap"
    source := ⟨"agha-jeretic-2022", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you don't have to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("modal", "have to"), ("gap_detected", "false"), ("classical_value", "true"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "felicitous")] }

def ex_8a : Datum :=
  { id := "aghajeretic2022_8a"
    source := ⟨"agha-jeretic-2022", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "none"), ("continuation", "but you are allowed not to go"), ("continuation_felicity", "infelicitous")] }

def ex_8b : Datum :=
  { id := "aghajeretic2022_8b"
    source := ⟨"agha-jeretic-2022", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you have to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("negation", "none"), ("continuation", "but you are allowed not to go"), ("continuation_felicity", "infelicitous")] }

def ex_10a : Datum :=
  { id := "aghajeretic2022_10a"
    source := ⟨"agha-jeretic-2022", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, I don't think you should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "extra-clausal"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "infelicitous")] }

def ex_10b : Datum :=
  { id := "aghajeretic2022_10b"
    source := ⟨"agha-jeretic-2022", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, I don't think you have to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("negation", "extra-clausal"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "felicitous")] }

def ex_11a : Datum :=
  { id := "aghajeretic2022_11a"
    source := ⟨"agha-jeretic-2022", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, it's not the case that you should go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "extra-clausal"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "infelicitous")] }

def ex_11b : Datum :=
  { id := "aghajeretic2022_11b"
    source := ⟨"agha-jeretic-2022", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, it's not the case that you have to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("negation", "extra-clausal"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "felicitous")] }

def ex_12a : Datum :=
  { id := "aghajeretic2022_12a"
    source := ⟨"agha-jeretic-2022", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you mustn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "must"), ("force", "strong"), ("negation", "clausemate"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "infelicitous")] }

def ex_12b : Datum :=
  { id := "aghajeretic2022_12b"
    source := ⟨"agha-jeretic-2022", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, I don't think you must go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "must"), ("force", "strong"), ("negation", "extra-clausal"), ("continuation", "but you are allowed to go"), ("continuation_felicity", "felicitous")] }

def ex_14a : Datum :=
  { id := "aghajeretic2022_14a"
    source := ⟨"agha-jeretic-2022", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The advice was that you shouldn't go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "clausemate"), ("continuation", "but that you can go"), ("continuation_felicity", "infelicitous")] }

def ex_14b : Datum :=
  { id := "aghajeretic2022_14b"
    source := ⟨"agha-jeretic-2022", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The advice was that you shouldn't necessarily go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("remover", "necessarily"), ("continuation", "but that you can go"), ("continuation_felicity", "felicitous")] }

def ex_15a : Datum :=
  { id := "aghajeretic2022_15a"
    source := ⟨"agha-jeretic-2022", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should not work from home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("negation", "clausemate"), ("continuation", "but it is allowed"), ("continuation_felicity", "infelicitous")] }

def ex_15b : Datum :=
  { id := "aghajeretic2022_15b"
    source := ⟨"agha-jeretic-2022", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should not necessarily work from home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("remover", "necessarily"), ("continuation", "but it is allowed"), ("continuation_felicity", "felicitous")] }

def ex_17a_qud1 : Datum :=
  { id := "aghajeretic2022_17a_qud1"
    source := ⟨"agha-jeretic-2022", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you should do every exercise."
    glossedTokens := []
    context := "One can get a perfect grade by doing most exercises correctly; doing all gives extra credit."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("qud", "What is a way to get a perfect grade?")] }

def ex_17a_qud2 : Datum :=
  { id := "aghajeretic2022_17a_qud2"
    source := ⟨"agha-jeretic-2022", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you should do every exercise."
    glossedTokens := []
    context := "One can get a perfect grade by doing most exercises correctly; doing all gives extra credit."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("qud", "What are the minimal requirements to get a perfect grade?")] }

def ex_17b_qud1 : Datum :=
  { id := "aghajeretic2022_17b_qud1"
    source := ⟨"agha-jeretic-2022", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you have to do every exercise."
    glossedTokens := []
    context := "One can get a perfect grade by doing most exercises correctly; doing all gives extra credit."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("qud", "What is a way to get a perfect grade?")] }

def ex_17b_qud2 : Datum :=
  { id := "aghajeretic2022_17b_qud2"
    source := ⟨"agha-jeretic-2022", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you have to do every exercise."
    glossedTokens := []
    context := "One can get a perfect grade by doing most exercises correctly; doing all gives extra credit."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("qud", "What are the minimal requirements to get a perfect grade?")] }

def ex_19a : Datum :=
  { id := "aghajeretic2022_19a"
    source := ⟨"agha-jeretic-2022", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should take the right door to go to the living room."
    glossedTokens := []
    context := "Two doors lead to the living room; both are equally good options."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("denial", "No, that's not true, you don't have to, but you can"), ("denial_felicity", "infelicitous"), ("well_response_felicity", "felicitous")] }

def ex_19b : Datum :=
  { id := "aghajeretic2022_19b"
    source := ⟨"agha-jeretic-2022", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must take the right door to go to the living room."
    glossedTokens := []
    context := "Two doors lead to the living room; both are equally good options."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "must"), ("force", "strong"), ("denial", "No, that's not true, you don't have to, but you can"), ("denial_felicity", "felicitous"), ("well_response_felicity", "infelicitous")] }

def ex_31a : Datum :=
  { id := "aghajeretic2022_31a"
    source := ⟨"vander-klok-hohaus-2020", "(3a)"⟩
    reportedIn := some ⟨"agha-jeretic-2022", "(31a)"⟩
    language := "java1254"
    primaryText := "Aku iso ngelangi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "iso"), ("force", "possibility")] }

def ex_31b : Datum :=
  { id := "aghajeretic2022_31b"
    source := ⟨"vander-klok-hohaus-2020", "(3b)"⟩
    reportedIn := some ⟨"agha-jeretic-2022", "(31b)"⟩
    language := "java1254"
    primaryText := "Aku iso-ne ngelangi."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("modal", "iso+NE"), ("derivation", "NE"), ("base", "possibility")] }

def ex_32a : Datum :=
  { id := "aghajeretic2022_32a"
    source := ⟨"agha-jeretic-2022", "(32a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Tu devrais partir."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "devoir+CF"), ("derivation", "CF"), ("base", "necessity")] }

def ex_32b : Datum :=
  { id := "aghajeretic2022_32b"
    source := ⟨"agha-jeretic-2022", "(32b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Tu pourrais partir."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "pouvoir+CF"), ("derivation", "CF"), ("base", "possibility")] }

def ex_38a : Datum :=
  { id := "aghajeretic2022_38a"
    source := ⟨"agha-jeretic-2022", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not true that I'll be happy if I get a sodastream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "future conditional"), ("continuation", "but I might be"), ("continuation_felicity", "infelicitous")] }

def ex_38b : Datum :=
  { id := "aghajeretic2022_38b"
    source := ⟨"agha-jeretic-2022", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not necessarily true that I'll be happy if I get a sodastream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "future conditional"), ("remover", "necessarily"), ("continuation", "but I might be"), ("continuation_felicity", "felicitous")] }

def ex_40a : Datum :=
  { id := "aghajeretic2022_40a"
    source := ⟨"agha-jeretic-2022", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ticks don't carry lyme disease."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "generic"), ("continuation", "but some of them do"), ("continuation_felicity", "infelicitous")] }

def ex_40b : Datum :=
  { id := "aghajeretic2022_40b"
    source := ⟨"agha-jeretic-2022", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ticks don't necessarily carry lyme disease."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "generic"), ("remover", "necessarily"), ("continuation", "but some of them do"), ("continuation_felicity", "felicitous")] }

def ex_41a : Datum :=
  { id := "aghajeretic2022_41a"
    source := ⟨"agha-jeretic-2022", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't smoke."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "habitual"), ("continuation", "but I do sometimes"), ("continuation_felicity", "infelicitous")] }

def ex_41b : Datum :=
  { id := "aghajeretic2022_41b"
    source := ⟨"agha-jeretic-2022", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't necessarily smoke."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "habitual"), ("remover", "necessarily"), ("continuation", "but I do sometimes"), ("continuation_felicity", "felicitous")] }

def ex_47a : Datum :=
  { id := "aghajeretic2022_47a"
    source := ⟨"agha-jeretic-2022", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get to 10WP from Astoria, you should take the N."
    glossedTokens := []
    context := "To get to 10 Washington Place from Astoria, you can take the N or the R, but the N is faster."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "should"), ("force", "weak"), ("qud", "Which train is best?")] }

def ex_47b : Datum :=
  { id := "aghajeretic2022_47b"
    source := ⟨"agha-jeretic-2022", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get to 10WP from Astoria, you have to take the N."
    glossedTokens := []
    context := "To get to 10 Washington Place from Astoria, you can take the N or the R, but the N is faster."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modal", "have to"), ("force", "strong"), ("qud", "Which train is best?")] }

def all : List Datum := [ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b, should_pos_all, should_pos_none, should_pos_gap, should_neg_all, should_neg_none, should_neg_gap, haveTo_pos_gap, haveTo_neg_gap, ex_8a, ex_8b, ex_10a, ex_10b, ex_11a, ex_11b, ex_12a, ex_12b, ex_14a, ex_14b, ex_15a, ex_15b, ex_17a_qud1, ex_17a_qud2, ex_17b_qud1, ex_17b_qud2, ex_19a, ex_19b, ex_31a, ex_31b, ex_32a, ex_32b, ex_38a, ex_38b, ex_40a, ex_40b, ex_41a, ex_41b, ex_47a, ex_47b]

/-- In the scenarios of the grid all, none, or some but not all of the best worlds satisfy the prejacent. -/
inductive Scenario where
  /-- ALL: ALL -/
  | all
  /-- NONE: NONE -/
  | none
  /-- GAP: GAP -/
  | gap
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `condition`. -/
def condition (e : Datum) : Option Scenario :=
  e.parse? "condition" [("ALL", .all), ("NONE", .none), ("GAP", .gap)]

end AghaJeretic2022.Examples
