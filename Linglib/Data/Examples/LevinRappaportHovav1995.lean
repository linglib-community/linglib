module

public import Linglib.Data.Examples.Schema

/-!
# `LevinRappaportHovav1995` — typed example data

Auto-generated from `Linglib/Data/Examples/LevinRappaportHovav1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LevinRappaportHovav1995.Examples`.
-/

@[expose] public section

namespace LevinRappaportHovav1995.Examples

def ex4_8 : Datum :=
  { id := "levinrappaporthovav1995_ex4_8"
    source := ⟨"levin-hovav-1995", "(8) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The beacons flared the news through the land."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "flare"), ("class", "43.1")] }

def ex4_9a : Datum :=
  { id := "levinrappaporthovav1995_ex4_9a"
    source := ⟨"levin-hovav-1995", "(9a) of chapter 4"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The phone rang me out of a dreamless oblivion at seven-fifteen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "ring"), ("class", "43.2")] }

def ex4_9c : Datum :=
  { id := "levinrappaporthovav1995_ex4_9c"
    source := ⟨"levin-hovav-1995", "(9c) of chapter 4"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Then he watched as it gurgled its way into a whiskey tumbler."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "gurgle"), ("class", "43.2")] }

def ex4_10a : Datum :=
  { id := "levinrappaporthovav1995_ex4_10a"
    source := ⟨"levin-hovav-1995", "(10a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The skunk stank us out of house and home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "stink"), ("class", "43.3")] }

def ex4_10b : Datum :=
  { id := "levinrappaporthovav1995_ex4_10b"
    source := ⟨"levin-hovav-1995", "(10b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He stank his smelly way home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "stink"), ("class", "43.3")] }

def ex4_25a : Datum :=
  { id := "levinrappaporthovav1995_ex4_25a"
    source := ⟨"levin-hovav-1995", "(25a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bag broke open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "break"), ("class", "45.1")] }

def ex4_25b : Datum :=
  { id := "levinrappaporthovav1995_ex4_25b"
    source := ⟨"levin-hovav-1995", "(25b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The toast burned black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "burn"), ("class", "45.4")] }

def ex4_25c : Datum :=
  { id := "levinrappaporthovav1995_ex4_25c"
    source := ⟨"levin-hovav-1995", "(25c) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ice froze solid."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "freeze"), ("class", "45.4")] }

def ex4_28a : Datum :=
  { id := "levinrappaporthovav1995_ex4_28a"
    source := ⟨"levin-hovav-1995", "(28a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mirror broke a jagged break."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cognateObject"), ("verb", "break"), ("class", "45.1")] }

def ex4_28b : Datum :=
  { id := "levinrappaporthovav1995_ex4_28b"
    source := ⟨"levin-hovav-1995", "(28b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The toast burned its crust black."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "burn"), ("class", "45.4")] }

def ex4_31a : Datum :=
  { id := "levinrappaporthovav1995_ex4_31a"
    source := ⟨"levin-hovav-1995", "(31a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She arrived a glamorous arrival."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cognateObject"), ("verb", "arrive"), ("class", "51.1"), ("agentive", "yes")] }

def ex4_31b : Datum :=
  { id := "levinrappaporthovav1995_ex4_31b"
    source := ⟨"levin-hovav-1995", "(31b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apples fell a smooth fall."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cognateObject"), ("verb", "fall"), ("class", "51.1"), ("agentive", "no")] }

def ex4_32a : Datum :=
  { id := "levinrappaporthovav1995_ex4_32a"
    source := ⟨"levin-hovav-1995", "(32a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The oil rose its way to the top."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "rise"), ("class", "51.1"), ("agentive", "no")] }

def ex4_32b : Datum :=
  { id := "levinrappaporthovav1995_ex4_32b"
    source := ⟨"levin-hovav-1995", "(32b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apples fell their way into the crates."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "fall"), ("class", "51.1"), ("agentive", "no")] }

def ex4_32c : Datum :=
  { id := "levinrappaporthovav1995_ex4_32c"
    source := ⟨"levin-hovav-1995", "(32c) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She arrived her way to the front of the line."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "arrive"), ("class", "51.1"), ("agentive", "yes")] }

def ex4_45a : Datum :=
  { id := "levinrappaporthovav1995_ex4_45a"
    source := ⟨"levin-hovav-1995", "(45a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The statue stood a heroic stance in the middle of the common."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cognateObject"), ("verb", "stand"), ("class", "47.6"), ("agentive", "no")] }

def ex4_45b : Datum :=
  { id := "levinrappaporthovav1995_ex4_45b"
    source := ⟨"levin-hovav-1995", "(45b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The city sprawled an extensive sprawl around the bay."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cognateObject"), ("verb", "sprawl"), ("class", "47.6"), ("agentive", "no")] }

def ex4_50a : Datum :=
  { id := "levinrappaporthovav1995_ex4_50a"
    source := ⟨"levin-hovav-1995", "(50a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The jogger ran his soles thin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "run"), ("class", "51.3.2"), ("agentive", "yes")] }

def ex4_50b : Datum :=
  { id := "levinrappaporthovav1995_ex4_50b"
    source := ⟨"levin-hovav-1995", "(50b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Don't expect to swim yourself sober!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "swim"), ("class", "51.3.2"), ("agentive", "yes")] }

def ex4_51a : Datum :=
  { id := "levinrappaporthovav1995_ex4_51a"
    source := ⟨"levin-hovav-1995", "(51a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The jogger ran sore."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "run"), ("class", "51.3.2"), ("agentive", "yes")] }

def ex4_51b : Datum :=
  { id := "levinrappaporthovav1995_ex4_51b"
    source := ⟨"levin-hovav-1995", "(51b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Don't expect to swim sober!"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "swim"), ("class", "51.3.2"), ("agentive", "yes")] }

def ex4_52a : Datum :=
  { id := "levinrappaporthovav1995_ex4_52a"
    source := ⟨"levin-hovav-1995", "(52a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door rolled open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "roll"), ("class", "51.3.1"), ("agentive", "no")] }

def ex4_52b : Datum :=
  { id := "levinrappaporthovav1995_ex4_52b"
    source := ⟨"levin-hovav-1995", "(52b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The shutter swung shut."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "swing"), ("class", "51.3.1"), ("agentive", "no")] }

def ex4_53a : Datum :=
  { id := "levinrappaporthovav1995_ex4_53a"
    source := ⟨"levin-hovav-1995", "(53a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door rolled itself open."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "roll"), ("class", "51.3.1"), ("agentive", "no")] }

def ex4_53b : Datum :=
  { id := "levinrappaporthovav1995_ex4_53b"
    source := ⟨"levin-hovav-1995", "(53b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The shutter swung itself shut."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "swing"), ("class", "51.3.1"), ("agentive", "no")] }

def ex4_54a : Datum :=
  { id := "levinrappaporthovav1995_ex4_54a"
    source := ⟨"levin-hovav-1995", "(54a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The jogger ran his way to better health."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "run"), ("class", "51.3.2"), ("agentive", "yes")] }

def ex4_54b : Datum :=
  { id := "levinrappaporthovav1995_ex4_54b"
    source := ⟨"levin-hovav-1995", "(54b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Swim your way to a new you!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "swim"), ("class", "51.3.2"), ("agentive", "yes")] }

def ex4_55a : Datum :=
  { id := "levinrappaporthovav1995_ex4_55a"
    source := ⟨"levin-hovav-1995", "(55a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pebbles rolled their way into the stream."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "roll"), ("class", "51.3.1"), ("agentive", "no")] }

def ex4_55b : Datum :=
  { id := "levinrappaporthovav1995_ex4_55b"
    source := ⟨"levin-hovav-1995", "(55b) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball bounced its way into the street."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "bounce"), ("class", "51.3.1"), ("agentive", "no")] }

def ex6_1 : Datum :=
  { id := "levinrappaporthovav1995_ex6_1"
    source := ⟨"levin-hovav-1995", "(1) of chapter 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the distance appeared the towers and spires of a town which greatly resembled Oxford."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "locativeInversion"), ("verb", "appear"), ("class", "48.1.1")] }

def ex6_4a : Datum :=
  { id := "levinrappaporthovav1995_ex6_4a"
    source := ⟨"levin-hovav-1995", "(4a) of chapter 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the distance there appeared the towers and spires of a town which greatly resembled Oxford."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "thereInsertion"), ("verb", "appear"), ("class", "48.1.1")] }

def ex6_18a : Datum :=
  { id := "levinrappaporthovav1995_ex6_18a"
    source := ⟨"levin-hovav-1995", "(18a) of chapter 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "On the top floor of the skyscraper broke many windows."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "locativeInversion"), ("verb", "break"), ("class", "45.1")] }

def ex6_22a : Datum :=
  { id := "levinrappaporthovav1995_ex6_22a"
    source := ⟨"levin-hovav-1995", "(22a) of chapter 6"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "In the hall ticked the long-case clock that had been a wedding present from her parents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "locativeInversion"), ("verb", "tick"), ("class", "43.2")] }

def all : List Datum := [ex4_8, ex4_9a, ex4_9c, ex4_10a, ex4_10b, ex4_25a, ex4_25b, ex4_25c, ex4_28a, ex4_28b, ex4_31a, ex4_31b, ex4_32a, ex4_32b, ex4_32c, ex4_45a, ex4_45b, ex4_50a, ex4_50b, ex4_51a, ex4_51b, ex4_52a, ex4_52b, ex4_53a, ex4_53b, ex4_54a, ex4_54b, ex4_55a, ex4_55b, ex6_1, ex6_4a, ex6_18a, ex6_22a]

end LevinRappaportHovav1995.Examples
