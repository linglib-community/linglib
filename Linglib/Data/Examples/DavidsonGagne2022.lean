module

public import Linglib.Data.Examples.Schema

/-!
# `DavidsonGagne2022` — typed example data

Auto-generated from `Linglib/Data/Examples/DavidsonGagne2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DavidsonGagne2022.Examples`.
-/

@[expose] public section

namespace DavidsonGagne2022.Examples

def ex_32a : Datum :=
  { id := "davidsongagne2022_32a"
    source := ⟨"davidson-gagne-2022", "(32a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "FS(ALL)-neutral BECOME VAMPIRE"
    glossedTokens := []
    context := "The signer has just said: Last night I watched a movie with my friends about vampires. Afterwards I went to bed and I dreamt that…"
    judgment := .acceptable
    alternatives := []
    readings := [("contextual", .acceptable), ("widened", .unacceptable)]
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "neutral"), ("quantifier", "FS(ALL)"), ("realization", "simultaneous")] }

def ex_32b : Datum :=
  { id := "davidsongagne2022_32b"
    source := ⟨"davidson-gagne-2022", "(32b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "FS(ALL)-high BECOME VAMPIRE"
    glossedTokens := []
    context := "The signer has just said: Last night I watched a movie with my friends about vampires. Afterwards I went to bed and I dreamt that…"
    judgment := .acceptable
    alternatives := []
    readings := [("contextual", .unacceptable), ("widened", .acceptable)]
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "FS(ALL)"), ("realization", "simultaneous")] }

def ex_14a : Datum :=
  { id := "davidsongagne2022_14a"
    source := ⟨"davidson-gagne-2022", "(14a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "STUDENT IX-arc-a SMART. IX-arc-neutral-ā NOT."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "neutral"), ("locus", "implicit")] }

def ex_14b : Datum :=
  { id := "davidsongagne2022_14b"
    source := ⟨"davidson-gagne-2022", "(14b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "STUDENT IX-arc-a SMART. IX-arc-high NOT."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "high"), ("locus", "implicit")] }

def ex_15a : Datum :=
  { id := "davidsongagne2022_15a"
    source := ⟨"davidson-gagne-2022", "(15a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "POSS-1 FAMILY IX-arc-neutral WEAR CLOTHES."
    glossedTokens := []
    context := "Discussing an accidental family visit to a nudist colony. The family is a subset of people at the nudist colony, who are in turn a subset of people in the world."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "neutral"), ("levels", "3")] }

def ex_15b : Datum :=
  { id := "davidsongagne2022_15b"
    source := ⟨"davidson-gagne-2022", "(15b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "IX-arc-mid NOT WEAR CLOTHES."
    glossedTokens := []
    context := "Discussing an accidental family visit to a nudist colony. The family is a subset of people at the nudist colony, who are in turn a subset of people in the world."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "mid"), ("levels", "3")] }

def ex_15c : Datum :=
  { id := "davidsongagne2022_15c"
    source := ⟨"davidson-gagne-2022", "(15c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "IX-arc-high WEAR CLOTHES."
    glossedTokens := []
    context := "Discussing an accidental family visit to a nudist colony. The family is a subset of people at the nudist colony, who are in turn a subset of people in the world."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "high"), ("levels", "3")] }

def ex_16a : Datum :=
  { id := "davidsongagne2022_16a"
    source := ⟨"davidson-gagne-2022", "(16a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "IX-arc-neutral NOT WEAR CLOTHES."
    glossedTokens := []
    context := "Discussing an accidental family visit to a nudist colony. The family is a subset of people at the nudist colony, who are in turn a subset of people in the world."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "neutral"), ("levels", "2")] }

def ex_16b : Datum :=
  { id := "davidsongagne2022_16b"
    source := ⟨"davidson-gagne-2022", "(16b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "IX-arc-high WEAR CLOTHES."
    glossedTokens := []
    context := "Discussing an accidental family visit to a nudist colony. The family is a subset of people at the nudist colony, who are in turn a subset of people in the world."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("heightOn", "pronoun"), ("height", "high"), ("levels", "2")] }

def ex_17a : Datum :=
  { id := "davidsongagne2022_17a"
    source := ⟨"davidson-gagne-2022", "(17a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "(IX-1) LIKE (IX-arc)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("heightOn", "none"), ("locusOn", "pronoun"), ("verb", "LIKE"), ("verbClass", "plain")] }

def ex_17b : Datum :=
  { id := "davidsongagne2022_17b"
    source := ⟨"davidson-gagne-2022", "(17b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "(IX-1) LIKE-arc-a"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("heightOn", "none"), ("locusOn", "verb"), ("verb", "LIKE"), ("verbClass", "plain")] }

def ex_18a : Datum :=
  { id := "davidsongagne2022_18a"
    source := ⟨"davidson-gagne-2022", "(18a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-INFORM-arc-a"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("heightOn", "none"), ("locusOn", "verb"), ("verb", "INFORM"), ("verbClass", "directional")] }

def ex_18b : Datum :=
  { id := "davidsongagne2022_18b"
    source := ⟨"davidson-gagne-2022", "(18b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-INFORM-a"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("heightOn", "none"), ("locusOn", "verb"), ("verb", "INFORM"), ("verbClass", "directional")] }

def ex_18c : Datum :=
  { id := "davidsongagne2022_18c"
    source := ⟨"davidson-gagne-2022", "(18c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "a-INFORM-1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("heightOn", "none"), ("locusOn", "verb"), ("verb", "INFORM"), ("verbClass", "directional")] }

def ex_21a : Datum :=
  { id := "davidsongagne2022_21a"
    source := ⟨"davidson-gagne-2022", "(21a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "(IX-1) LIKE-arc-neutral"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "neutral"), ("verb", "LIKE"), ("verbClass", "plain")] }

def ex_21b : Datum :=
  { id := "davidsongagne2022_21b"
    source := ⟨"davidson-gagne-2022", "(21b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "(IX-1) LIKE IX-arc-neutral"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "pronoun"), ("height", "neutral"), ("verb", "LIKE"), ("verbClass", "plain")] }

def ex_21c : Datum :=
  { id := "davidsongagne2022_21c"
    source := ⟨"davidson-gagne-2022", "(21c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "(IX-1) LIKE-arc-high"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "high"), ("verb", "LIKE"), ("verbClass", "plain")] }

def ex_21d : Datum :=
  { id := "davidsongagne2022_21d"
    source := ⟨"davidson-gagne-2022", "(21d)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "(IX-1) LIKE IX-arc-high"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "pronoun"), ("height", "high"), ("verb", "LIKE"), ("verbClass", "plain")] }

def ex_22a : Datum :=
  { id := "davidsongagne2022_22a"
    source := ⟨"davidson-gagne-2022", "(22a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-INFORM-arc-neutral"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "neutral"), ("verb", "INFORM"), ("verbClass", "directional")] }

def ex_22b : Datum :=
  { id := "davidsongagne2022_22b"
    source := ⟨"davidson-gagne-2022", "(22b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-INFORM-arc-high"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "high"), ("verb", "INFORM"), ("verbClass", "directional")] }

def ex_23a : Datum :=
  { id := "davidsongagne2022_23a"
    source := ⟨"davidson-gagne-2022", "(23a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-PICK-FROM(alternating repetition)-arc-neutral"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "neutral"), ("verb", "PICK-FROM"), ("verbClass", "directional")] }

def ex_23b : Datum :=
  { id := "davidsongagne2022_23b"
    source := ⟨"davidson-gagne-2022", "(23b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "1-PICK-FROM(alternating repetition)-arc-high"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "high"), ("verb", "PICK-FROM"), ("verbClass", "directional")] }

def ex_24a : Datum :=
  { id := "davidsongagne2022_24a"
    source := ⟨"davidson-gagne-2022", "(24a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIVE-OUT-neutral CLASS, HAVE LEFT."
    glossedTokens := []
    context := "Someone is talking about a bunch of fliers they've printed to advertise for an upcoming event."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "neutral"), ("verb", "GIVE-OUT"), ("verbClass", "directional"), ("levels", "3")] }

def ex_24b : Datum :=
  { id := "davidsongagne2022_24b"
    source := ⟨"davidson-gagne-2022", "(24b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIVE-OUT-mid CAMPUS, STILL HAVE LEFT."
    glossedTokens := []
    context := "Someone is talking about a bunch of fliers they've printed to advertise for an upcoming event."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "mid"), ("verb", "GIVE-OUT"), ("verbClass", "directional"), ("levels", "3")] }

def ex_24c : Datum :=
  { id := "davidsongagne2022_24c"
    source := ⟨"davidson-gagne-2022", "(24c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "GIVE-OUT-high OTHER PEOPLE MY TOWN."
    glossedTokens := []
    context := "Someone is talking about a bunch of fliers they've printed to advertise for an upcoming event."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "high"), ("verb", "GIVE-OUT"), ("verbClass", "directional"), ("levels", "3")] }

def ex_25 : Datum :=
  { id := "davidsongagne2022_25"
    source := ⟨"davidson-gagne-2022", "(25)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "INFORM-2 WORLD WILL MESS. IX-arc-neutral(thumb) GOVERNMENT HAVE SPECIALf BOAT READY. UNDERSTAND IX-arc-neutral PICK-neutral(alternating-repetition) LIMIT PEOPLE WHObent FILE-ON ON BOAT IX-left. UNDERSTAND IX-arc-right-neutral RESPONSIBILITY WHATpu-rq. POSS-neutral-right DRESS BAG EAT INVOLVE BRING FILE-ON-left. UNDERSTAND GOVERNMENT PROVIDE BOAT FINISH."
    glossedTokens := []
    context := "A story about an apocalyptic event."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "neutral"), ("verb", "PICK"), ("verbClass", "directional"), ("anaphora", "locus")] }

def ex_26 : Datum :=
  { id := "davidsongagne2022_26"
    source := ⟨"davidson-gagne-2022", "(26)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "WORLD HAPPEN MESS PU. INFORM GOVERNMENT HAVE SPECIAL BOAT READY FOR. UNDERSTAND IX-right-high PICK-high(alternating repetition) PEOPLE WHObent CAN FILE-ON-left. UNDERSTAND IX-arc-right-high RESPONSIBILITY WHATpu-rq. POSS-right-mid BAG DRESS EAT INCLUDE. GOVERNMENT PROVIDE WHATpu-rq BOAT FINISH."
    glossedTokens := []
    context := "A story about an apocalyptic event."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("heightOn", "verb"), ("height", "high"), ("verb", "PICK"), ("verbClass", "directional"), ("anaphora", "locus")] }

def ex_27 : Datum :=
  { id := "davidsongagne2022_27"
    source := ⟨"davidson-gagne-2022", "(27)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amer1248"
    primaryText := "IX-1 WANT DOG-high"
    glossedTokens := []
    context := "Talking about adopting a pet."
    judgment := .marginal
    alternatives := []
    readings := [("widened", .unacceptable), ("physical", .marginal)]
    paperFeatures := [("section", "3.3"), ("heightOn", "noun"), ("height", "high")] }

def ex_28 : Datum :=
  { id := "davidsongagne2022_28"
    source := ⟨"davidson-gagne-2022", "(28)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "IX-1 WANT DOG, SOMETHING-high"
    glossedTokens := []
    context := "Talking about adopting a pet."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "SOMETHING"), ("realization", "simultaneous")] }

def ex_33a : Datum :=
  { id := "davidsongagne2022_33a"
    source := ⟨"davidson-gagne-2022", "(33a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "NONEsym-neutral ALONE"
    glossedTokens := []
    context := "Discussion of whether anyone in the signer's family is Deaf."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "neutral"), ("quantifier", "NONEsym"), ("realization", "simultaneous")] }

def ex_33b : Datum :=
  { id := "davidsongagne2022_33b"
    source := ⟨"davidson-gagne-2022", "(33b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "NONEsym-high ALONE"
    glossedTokens := []
    context := "Discussion of whether anyone in the signer's family is Deaf."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "NONEsym"), ("realization", "simultaneous")] }

def ex_34a : Datum :=
  { id := "davidsongagne2022_34a"
    source := ⟨"davidson-gagne-2022", "(34a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "NONEsym-neutral BANANAS."
    glossedTokens := []
    context := "Lack of bananas first at store, then in town, then in whole country."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "neutral"), ("quantifier", "NONEsym"), ("realization", "simultaneous"), ("levels", "3")] }

def ex_34b : Datum :=
  { id := "davidsongagne2022_34b"
    source := ⟨"davidson-gagne-2022", "(34b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "amer1248"
    primaryText := "NONEsym-mid BANANAS."
    glossedTokens := []
    context := "Lack of bananas first at store, then in town, then in whole country."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "mid"), ("quantifier", "NONEsym"), ("realization", "simultaneous"), ("levels", "3")] }

def ex_34c : Datum :=
  { id := "davidsongagne2022_34c"
    source := ⟨"davidson-gagne-2022", "(34c)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "NONEsym-high BANANAS."
    glossedTokens := []
    context := "Lack of bananas first at store, then in town, then in whole country."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "NONEsym"), ("realization", "simultaneous"), ("levels", "3")] }

def ex_35neutral : Datum :=
  { id := "davidsongagne2022_35neutral"
    source := ⟨"davidson-gagne-2022", "(35)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "TYPICALLY NONEsym-neutral FAIL."
    glossedTokens := []
    context := "The signer is discussing the numerous tests that he gives out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "neutral"), ("quantifier", "NONEsym"), ("realization", "simultaneous"), ("bound", "typically")] }

def ex_35high : Datum :=
  { id := "davidsongagne2022_35high"
    source := ⟨"davidson-gagne-2022", "(35)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "TYPICALLY NONEsym-high FAIL."
    glossedTokens := []
    context := "The signer is discussing the numerous tests that he gives out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "NONEsym"), ("realization", "simultaneous"), ("bound", "typically")] }

def ex_36a : Datum :=
  { id := "davidsongagne2022_36a"
    source := ⟨"davidson-gagne-2022", "(36a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "TYPICALLY SOMEONE-neutral LIKE MUSTARD."
    glossedTokens := []
    context := "Deciding condiments to put out at a party. The host says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "neutral"), ("quantifier", "SOMEONE"), ("realization", "simultaneous"), ("bound", "typically")] }

def ex_36b : Datum :=
  { id := "davidsongagne2022_36b"
    source := ⟨"davidson-gagne-2022", "(36b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "TYPICALLY SOMEONE-high LIKE MUSTARD."
    glossedTokens := []
    context := "Deciding condiments to put out at a party. The host says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "SOMEONE"), ("realization", "simultaneous"), ("bound", "typically")] }

def ex_37a : Datum :=
  { id := "davidsongagne2022_37a"
    source := ⟨"davidson-gagne-2022", "(37a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "FEW IX-arc-neutral FEEL HIT SICK"
    glossedTokens := []
    context := "My family goes to the beach every year."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "pronoun"), ("height", "neutral"), ("quantifier", "FEW"), ("realization", "sequential")] }

def ex_37b : Datum :=
  { id := "davidsongagne2022_37b"
    source := ⟨"davidson-gagne-2022", "(37b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "FEW IX-arc-high FEEL HIT SICK"
    glossedTokens := []
    context := "My family goes to the beach every year."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "pronoun"), ("height", "high"), ("quantifier", "FEW"), ("realization", "sequential")] }

def ex_38a : Datum :=
  { id := "davidsongagne2022_38a"
    source := ⟨"davidson-gagne-2022", "(38a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "FS(ALL)-high IX-arc-neutral SICK"
    glossedTokens := []
    context := "My family goes to the beach every year."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "FS(ALL)"), ("realization", "both")] }

def ex_39a_none : Datum :=
  { id := "davidsongagne2022_39a_none"
    source := ⟨"davidson-gagne-2022", "(39a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "NONE-high FAIL."
    glossedTokens := []
    context := "Discussing an exam."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "NONEsym"), ("realization", "simultaneous")] }

def ex_39a_each : Datum :=
  { id := "davidsongagne2022_39a_each"
    source := ⟨"davidson-gagne-2022", "(39a)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "[EACH IX-arc-high] FAIL."
    glossedTokens := []
    context := "Discussing an exam."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "pronoun"), ("height", "high"), ("quantifier", "EACH"), ("realization", "sequential")] }

def ex_39b_one : Datum :=
  { id := "davidsongagne2022_39b_one"
    source := ⟨"davidson-gagne-2022", "(39b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "ONE-high FAIL."
    glossedTokens := []
    context := "Discussing an exam."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "ONE"), ("realization", "simultaneous")] }

def ex_39b_two : Datum :=
  { id := "davidsongagne2022_39b_two"
    source := ⟨"davidson-gagne-2022", "(39b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "TWO-high FAIL."
    glossedTokens := []
    context := "Discussing an exam."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "quantifier"), ("height", "high"), ("quantifier", "TWO"), ("realization", "simultaneous")] }

def ex_39b_many : Datum :=
  { id := "davidsongagne2022_39b_many"
    source := ⟨"davidson-gagne-2022", "(39b)"⟩
    reportedIn := none
    language := "amer1248"
    primaryText := "[MANY IX-arc-high] FAIL."
    glossedTokens := []
    context := "Discussing an exam."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("heightOn", "pronoun"), ("height", "high"), ("quantifier", "MANY"), ("realization", "sequential")] }

def ex_54a : Datum :=
  { id := "davidsongagne2022_54a"
    source := ⟨"davidson-gagne-2022", "(54a)"⟩
    reportedIn := none
    language := "japa1238"
    primaryText := "CLASSMATE DEAF-FAMILY NONE(@chest) SELF FINISH"
    glossedTokens := []
    context := "A native signer of Japanese Sign Language contrasting his class, his school and his prefecture; a spontaneous example shared by Kazumi Matsuoka."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("heightOn", "quantifier"), ("height", "neutral"), ("levels", "3")] }

def ex_54b : Datum :=
  { id := "davidsongagne2022_54b"
    source := ⟨"davidson-gagne-2022", "(54b)"⟩
    reportedIn := none
    language := "japa1238"
    primaryText := "SCHOOL DEAF-FAMILY NONE(@cheek) SELF FINISH"
    glossedTokens := []
    context := "A native signer of Japanese Sign Language contrasting his class, his school and his prefecture; a spontaneous example shared by Kazumi Matsuoka."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("heightOn", "quantifier"), ("height", "mid"), ("levels", "3")] }

def ex_54c : Datum :=
  { id := "davidsongagne2022_54c"
    source := ⟨"davidson-gagne-2022", "(54c)"⟩
    reportedIn := none
    language := "japa1238"
    primaryText := "WAKAYAMA DEAF-FAMILY NONE(@forehead) SELF FINISH"
    glossedTokens := []
    context := "A native signer of Japanese Sign Language contrasting his class, his school and his prefecture; a spontaneous example shared by Kazumi Matsuoka."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("heightOn", "quantifier"), ("height", "high"), ("levels", "3")] }

def all : List Datum := [ex_32a, ex_32b, ex_14a, ex_14b, ex_15a, ex_15b, ex_15c, ex_16a, ex_16b, ex_17a, ex_17b, ex_18a, ex_18b, ex_18c, ex_21a, ex_21b, ex_21c, ex_21d, ex_22a, ex_22b, ex_23a, ex_23b, ex_24a, ex_24b, ex_24c, ex_25, ex_26, ex_27, ex_28, ex_33a, ex_33b, ex_34a, ex_34b, ex_34c, ex_35neutral, ex_35high, ex_36a, ex_36b, ex_37a, ex_37b, ex_38a, ex_39a_none, ex_39a_each, ex_39b_one, ex_39b_two, ex_39b_many, ex_54a, ex_54b, ex_54c]

end DavidsonGagne2022.Examples
