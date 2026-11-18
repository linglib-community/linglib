module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintelGillies2010` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintelGillies2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintelGillies2010.Examples`.
-/

@[expose] public section

namespace VonFintelGillies2010.Examples

def keys_drawer : Datum :=
  { id := "vonfintelgillies2010_keys_drawer"
    source := ⟨"von-fintel-gillies-2010", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They must be in the kitchen drawer."
    glossedTokens := []
    context := "Answer to: Where are the keys? The speaker infers the location rather than seeing it."
    judgment := .acceptable
    contrasts := [("They are in the kitchen drawer.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def john_left : Datum :=
  { id := "vonfintelgillies2010_john_left"
    source := ⟨"von-fintel-gillies-2010", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John must have left."
    glossedTokens := []
    context := "General epistemic context; the speaker infers John's departure."
    judgment := .acceptable
    contrasts := [("John left.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def john_home : Datum :=
  { id := "vonfintelgillies2010_john_home"
    source := ⟨"von-fintel-gillies-2010", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John must be at home."
    glossedTokens := []
    context := "General epistemic context; the speaker infers John's whereabouts."
    judgment := .acceptable
    contrasts := [("John is at home.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def mount_toby : Datum :=
  { id := "vonfintelgillies2010_mount_toby"
    source := ⟨"kratzer-1991", ""⟩
    reportedIn := some ⟨"von-fintel-gillies-2010", "(5b)"⟩
    language := "stan1293"
    primaryText := "She must have climbed Mount Toby."
    glossedTokens := []
    context := "General epistemic context; the speaker infers the climb."
    judgment := .acceptable
    contrasts := [("She climbed Mount Toby.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def billy_sees_rain : Datum :=
  { id := "vonfintelgillies2010_billy_sees_rain"
    source := ⟨"von-fintel-gillies-2010", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    glossedTokens := []
    context := "Billy sees the pouring rain through the window."
    judgment := .questionable
    contrasts := [("It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "direct"), ("must_entails_prejacent", "true")] }

def billy_wet_gear : Datum :=
  { id := "vonfintelgillies2010_billy_wet_gear"
    source := ⟨"von-fintel-gillies-2010", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining."
    glossedTokens := []
    context := "Billy sees people coming in with wet umbrellas, slickers, and galoshes, and knows for sure that rain is the only possible cause."
    judgment := .acceptable
    contrasts := [("It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def chris_ball : Datum :=
  { id := "vonfintelgillies2010_chris_ball"
    source := ⟨"von-fintel-gillies-2010", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball is in A or in B or in C. It is not in A. ... It is not in B. So, it must be in C."
    glossedTokens := []
    context := "Chris has lost her ball, but she knows with full certainty that it is either in Box A or B or C."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "elimination"), ("must_entails_prejacent", "true")] }

def cant_mastermind : Datum :=
  { id := "vonfintelgillies2010_cant_mastermind"
    source := ⟨"von-fintel-gillies-2010", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There can't be two reds."
    glossedTokens := []
    context := "Mastermind game: the conclusion is inferred from the clues, not directly observed."
    judgment := .acceptable
    contrasts := [("There aren't two reds.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "cant"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def cant_sunshine : Datum :=
  { id := "vonfintelgillies2010_cant_sunshine"
    source := ⟨"von-fintel-gillies-2010", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It can't be raining."
    glossedTokens := []
    context := "Billy sees brilliant sunshine."
    judgment := .questionable
    contrasts := [("It's not raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "cant"), ("evidence", "direct"), ("must_entails_prejacent", "true")] }

def cant_sun_gear : Datum :=
  { id := "vonfintelgillies2010_cant_sun_gear"
    source := ⟨"von-fintel-gillies-2010", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It can't be raining."
    glossedTokens := []
    context := "Billy sees people coming in with sun gear and knows sunshine is the only possible explanation."
    judgment := .acceptable
    contrasts := [("It's not raining.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "cant"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def must_be_hungry : Datum :=
  { id := "vonfintelgillies2010_must_be_hungry"
    source := ⟨"von-fintel-gillies-2010", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must be hungry."
    glossedTokens := []
    context := "Speaker reflecting on their own internal state."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def modus_ponens : Datum :=
  { id := "vonfintelgillies2010_modus_ponens"
    source := ⟨"von-fintel-gillies-2010", "(14)-(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Carl is at the party, then Lenny must be at the party. Carl is at the party. So: Lenny is at the party."
    glossedTokens := []
    context := "Assessing the validity of the argument form: if phi, must psi; phi; therefore psi."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "modus_ponens")] }

def must_perhaps : Datum :=
  { id := "vonfintelgillies2010_must_perhaps"
    source := ⟨"von-fintel-gillies-2010", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be raining but perhaps it isn't raining."
    glossedTokens := []
    context := "Flat-footed conjunction of must phi with perhaps not-phi."
    judgment := .unacceptable
    contrasts := [("Perhaps it isn't raining but it must be.", .unacceptable)]
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "epistemic_contradiction")] }

def might_retraction : Datum :=
  { id := "vonfintelgillies2010_might_retraction"
    source := ⟨"von-fintel-gillies-2010", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex: It might be raining. Billy: [Opens curtains] No it isn't. You were wrong. Alex: I was not! Look, I didn't say it was raining. I only said it might be raining. Stop picking on me!"
    glossedTokens := []
    context := "Alex asserted a might-claim; the prejacent turns out false; Alex retracts commitment to the prejacent."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "retraction"), ("modal", "might")] }

def must_no_retraction : Datum :=
  { id := "vonfintelgillies2010_must_no_retraction"
    source := ⟨"von-fintel-gillies-2010", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex: It must be raining. Billy: [Opens curtains] No it isn't. You were wrong. Alex: I was not! Look, I didn't say it was raining. I only said it must be raining. Stop picking on me!"
    glossedTokens := []
    context := "Alex asserted a must-claim; the prejacent turns out false; Alex attempts the might-style retraction."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "retraction"), ("modal", "must")] }

def hedging : Datum :=
  { id := "vonfintelgillies2010_hedging"
    source := ⟨"von-fintel-gillies-2010", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is probably raining."
    glossedTokens := []
    context := "Speaker is pretty sure rain explains the wet gear but feels a twinge of doubt and wants to hedge."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "hedging")] }

def hey_wait_a_minute : Datum :=
  { id := "vonfintelgillies2010_hey_wait_a_minute"
    source := ⟨"von-fintel-gillies-2010", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex: It must be raining. Billy: Hey! Wait a minute. Whaddya mean, must? Aren't you looking outside?"
    glossedTokens := []
    context := "Billy challenges Alex's use of must while Alex is looking out the window."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "hwam_test")] }

def all : List Datum := [keys_drawer, john_left, john_home, mount_toby, billy_sees_rain, billy_wet_gear, chris_ball, cant_mastermind, cant_sunshine, cant_sun_gear, must_be_hungry, modus_ponens, must_perhaps, might_retraction, must_no_retraction, hedging, hey_wait_a_minute]

end VonFintelGillies2010.Examples
