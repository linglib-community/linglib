module

public import Linglib.Data.Examples.Schema

/-!
# `AlexandropoulouGotzner2024a` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexandropoulouGotzner2024a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexandropoulouGotzner2024a.Examples`.
-/

@[expose] public section

namespace AlexandropoulouGotzner2024a.Examples

def ag2024a_t2_anna : Datum :=
  { id := "ag2024a_t2_anna"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Anna's room was not tiny."
    glossedTokens := []
    context := "A group of friends goes on vacation. One friend named Tim writes a review for each person's room on booking.com. Please decide which rating the room receives in terms of its size based on Tim's statement. 1 = tiny; 5 = gigantic. Tim writes:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "gigantic"), ("adjectiveType", "relative"), ("adjective", "tiny"), ("strength", "strong"), ("polarity", "negative"), ("negation", "negated"), ("condition", "negated negative strong")] }

def ag2024a_t2_david : Datum :=
  { id := "ag2024a_t2_david"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "David's room was small."
    glossedTokens := []
    context := "A group of friends goes on vacation. One friend named Tim writes a review for each person's room on booking.com. Please decide which rating the room receives in terms of its size based on Tim's statement. 1 = tiny; 5 = gigantic. Tim writes:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "gigantic"), ("adjectiveType", "relative"), ("adjective", "small"), ("strength", "weak"), ("polarity", "negative"), ("negation", "nonNegated"), ("condition", "non-negated negative weak")] }

def ag2024a_t2_brian : Datum :=
  { id := "ag2024a_t2_brian"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 2"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Brian's room was gigantic."
    glossedTokens := []
    context := "A group of friends goes on vacation. One friend named Tim writes a review for each person's room on booking.com. Please decide which rating the room receives in terms of its size based on Tim's statement. 1 = tiny; 5 = gigantic. Tim writes:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("item", "gigantic"), ("adjectiveType", "relative"), ("adjective", "gigantic"), ("strength", "strong"), ("polarity", "positive"), ("negation", "nonNegated"), ("condition", "non-negated positive strong")] }

def ag2024a_t3_anthony : Datum :=
  { id := "ag2024a_t3_anthony"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 3"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "The Saint Anthony's Hospital is not filthy."
    glossedTokens := []
    context := "The government examines the hospitals of a big city for their hygiene standards. The examiner writes a review. Please decide which rating each hospital gets for its hygiene standards based on the examiner's statements. 1 = filthy; 5 = pristine. The examiner says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "pristine"), ("adjectiveType", "absolute"), ("adjective", "filthy"), ("strength", "strong"), ("polarity", "negative"), ("negation", "negated"), ("condition", "negated negative strong")] }

def ag2024a_t3_joseph : Datum :=
  { id := "ag2024a_t3_joseph"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 3"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "The Saint Joseph Hospital is not dirty."
    glossedTokens := []
    context := "The government examines the hospitals of a big city for their hygiene standards. The examiner writes a review. Please decide which rating each hospital gets for its hygiene standards based on the examiner's statements. 1 = filthy; 5 = pristine. The examiner says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "pristine"), ("adjectiveType", "absolute"), ("adjective", "dirty"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("condition", "negated negative weak")] }

def ag2024a_t3_mary : Datum :=
  { id := "ag2024a_t3_mary"
    source := ⟨"alexandropoulou-gotzner-2024a", "Table 3"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "The Saint's Mary's Hospital is pristine."
    glossedTokens := []
    context := "The government examines the hospitals of a big city for their hygiene standards. The examiner writes a review. Please decide which rating each hospital gets for its hygiene standards based on the examiner's statements. 1 = filthy; 5 = pristine. The examiner says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("item", "pristine"), ("adjectiveType", "absolute"), ("adjective", "pristine"), ("strength", "strong"), ("polarity", "positive"), ("negation", "nonNegated"), ("condition", "non-negated positive strong")] }

def all : List Datum := [ag2024a_t2_anna, ag2024a_t2_david, ag2024a_t2_brian, ag2024a_t3_anthony, ag2024a_t3_joseph, ag2024a_t3_mary]

end AlexandropoulouGotzner2024a.Examples
