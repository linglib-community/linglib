module

public import Linglib.Data.Examples.Schema

/-!
# `Reichenbach1947` — typed example data

Auto-generated from `Linglib/Data/Examples/Reichenbach1947.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Reichenbach1947.Examples`.
-/

@[expose] public section

namespace Reichenbach1947.Examples

def past_perfect : Datum :=
  { id := "reichenbach1947_past_perfect"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I had seen John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Past Perfect"), ("structure", "E—R—S")] }

def simple_past : Datum :=
  { id := "reichenbach1947_simple_past"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Past"), ("structure", "R, E—S")] }

def present_perfect : Datum :=
  { id := "reichenbach1947_present_perfect"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have seen John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present Perfect"), ("structure", "E—S, R")] }

def present : Datum :=
  { id := "reichenbach1947_present"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I see John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present"), ("structure", "S, R, E")] }

def simple_future : Datum :=
  { id := "reichenbach1947_simple_future"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I shall see John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Future"), ("structure", "S, R—E")] }

def future_perfect : Datum :=
  { id := "reichenbach1947_future_perfect"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I shall have seen John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Future Perfect"), ("structure", "S—E—R")] }

def past_perfect_extended : Datum :=
  { id := "reichenbach1947_past_perfect_extended"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I had been seeing John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Past Perfect, Extended"), ("structure", "E—R—S")] }

def simple_past_extended : Datum :=
  { id := "reichenbach1947_simple_past_extended"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was seeing John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Past, Extended"), ("structure", "R, E—S")] }

def present_perfect_extended : Datum :=
  { id := "reichenbach1947_present_perfect_extended"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been seeing John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present Perfect, Extended"), ("structure", "E—S, R")] }

def present_extended : Datum :=
  { id := "reichenbach1947_present_extended"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I am seeing John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present, Extended"), ("structure", "S, R, E")] }

def simple_future_extended : Datum :=
  { id := "reichenbach1947_simple_future_extended"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I shall be seeing John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Future, Extended"), ("structure", "S, R—E")] }

def future_perfect_extended : Datum :=
  { id := "reichenbach1947_future_perfect_extended"
    source := ⟨"reichenbach-1947", "p. 290"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I shall have been seeing John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Future Perfect, Extended"), ("structure", "S—E—R")] }

def ex_1 : Datum :=
  { id := "reichenbach1947_1"
    source := ⟨"reichenbach-1947", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I had mailed the letter when John came and told me the news."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Past Perfect"), ("form", "Simple Past"), ("form", "Simple Past"), ("link", "when"), ("link", "when"), ("structure", "E—R—S"), ("structure", "R, E—S"), ("structure", "R, E—S")] }

def ex_1_has_come : Datum :=
  { id := "reichenbach1947_1_has_come"
    source := ⟨"reichenbach-1947", "p. 293"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I had mailed the letter when John has come."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Past Perfect"), ("form", "Present Perfect"), ("link", "when")] }

def ex_2 : Datum :=
  { id := "reichenbach1947_2"
    source := ⟨"reichenbach-1947", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have not decided which train I shall take."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present Perfect"), ("form", "Simple Future"), ("link", "which"), ("structure", "E—S, R"), ("structure", "S, R—E")] }

def ex_2_did_not_decide : Datum :=
  { id := "reichenbach1947_2_did_not_decide"
    source := ⟨"reichenbach-1947", "p. 293"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I did not decide which train I shall take."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Past"), ("form", "Simple Future"), ("link", "which")] }

def ex_3 : Datum :=
  { id := "reichenbach1947_3"
    source := ⟨"reichenbach-1947", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I did not know that you would be here."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Past"), ("form", "Conditional"), ("link", "that"), ("structure", "R, E—S"), ("structure", "R—S, E")] }

def ex_4 : Datum :=
  { id := "reichenbach1947_4"
    source := ⟨"reichenbach-1947", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How unfortunate! Now that John tells me this I have mailed the letter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present"), ("form", "Present Perfect"), ("link", "now that"), ("adverb", "now"), ("structure", "S, R, E"), ("structure", "E—S, R")] }

def ex_4_mailed : Datum :=
  { id := "reichenbach1947_4_mailed"
    source := ⟨"reichenbach-1947", "p. 294"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now that John tells me this I mailed the letter."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Present"), ("form", "Simple Past"), ("link", "now that"), ("adverb", "now")] }

def telephoned : Datum :=
  { id := "reichenbach1947_telephoned"
    source := ⟨"reichenbach-1947", "p. 295"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He telephoned before he came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Past"), ("form", "Simple Past"), ("link", "before")] }

def ex_5 : Datum :=
  { id := "reichenbach1947_5"
    source := ⟨"reichenbach-1947", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was healthier when I saw him than he is now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Past"), ("form", "Simple Past"), ("form", "Present"), ("link", "when"), ("link", "than"), ("structure", "R, E—S"), ("structure", "R, E—S"), ("structure", "S, R, E")] }

def now_shall_go : Datum :=
  { id := "reichenbach1947_now_shall_go"
    source := ⟨"reichenbach-1947", "p. 295"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now I shall go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Future"), ("adverb", "now"), ("structure", "S, R—E")] }

def shall_go_tomorrow : Datum :=
  { id := "reichenbach1947_shall_go_tomorrow"
    source := ⟨"reichenbach-1947", "p. 295"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I shall go tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Future"), ("adverb", "tomorrow"), ("structure", "S—R, E")] }

def photograph : Datum :=
  { id := "reichenbach1947_photograph"
    source := ⟨"reichenbach-1947", "p. 296"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I shall take your photograph when you come."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Future"), ("form", "Present"), ("link", "when"), ("pointOfSpeech", "neglected")] }

def record : Datum :=
  { id := "reichenbach1947_record"
    source := ⟨"reichenbach-1947", "p. 296"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We shall hear the record when we have dined."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Simple Future"), ("form", "Present Perfect"), ("link", "when"), ("pointOfSpeech", "neglected")] }

def all : List Datum := [past_perfect, simple_past, present_perfect, present, simple_future, future_perfect, past_perfect_extended, simple_past_extended, present_perfect_extended, present_extended, simple_future_extended, future_perfect_extended, ex_1, ex_1_has_come, ex_2, ex_2_did_not_decide, ex_3, ex_4, ex_4_mailed, telephoned, ex_5, now_shall_go, shall_go_tomorrow, photograph, record]

end Reichenbach1947.Examples
