module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Cruse1973` — typed example data

Auto-generated from `Linglib/Data/Examples/Cruse1973.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cruse1973.Examples`.
-/

@[expose] public section

namespace Cruse1973.Examples

def ex_7 : Datum :=
  { id := "cruse1973_7"
    source := ⟨"cruse-1973", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the vase entails John did something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_8 : Datum :=
  { id := "cruse1973_8"
    source := ⟨"cruse-1973", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase broke does not entail The vase did something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", ""), ("participant", "the vase"), ("animate", "false"), ("entailment", "denied")] }

def ex_9 : Datum :=
  { id := "cruse1973_9"
    source := ⟨"cruse-1973", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the vase: it therefore follows that he did something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_10 : Datum :=
  { id := "cruse1973_10"
    source := ⟨"cruse-1973", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase broke: therefore it did something."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", ""), ("participant", "the vase"), ("animate", "false")] }

def ex_11 : Datum :=
  { id := "cruse1973_11"
    source := ⟨"cruse-1973", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John marched the prisoners entails The prisoners did something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", "agentive"), ("participant", "the prisoners"), ("inferred", "true")] }

def ex_12 : Datum :=
  { id := "cruse1973_12"
    source := ⟨"cruse-1973", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John shot the prisoners does not entail The prisoners did something."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", ""), ("participant", "the prisoners"), ("entailment", "denied")] }

def ex_13 : Datum :=
  { id := "cruse1973_13"
    source := ⟨"cruse-1973", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the wind did was blow the tree down."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "agentive"), ("participant", "the wind"), ("animate", "false"), ("inferred", "true")] }

def ex_14 : Datum :=
  { id := "cruse1973_14"
    source := ⟨"cruse-1973", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to the wind was that it blew the tree down."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "agentive"), ("participant", "the wind"), ("animate", "false"), ("inferred", "true")] }

def ex_15 : Datum :=
  { id := "cruse1973_15"
    source := ⟨"cruse-1973", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the computer is doing is calculating the correlation coefficient."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "agentive"), ("participant", "the computer"), ("animate", "false"), ("inferred", "true")] }

def ex_16 : Datum :=
  { id := "cruse1973_16"
    source := ⟨"cruse-1973", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What is happening to the computer is that it is calculating the correlation coefficient."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "agentive"), ("participant", "the computer"), ("animate", "false"), ("inferred", "true")] }

def ex_17 : Datum :=
  { id := "cruse1973_17"
    source := ⟨"cruse-1973", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bullet smashed John's collar-bone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "effective"), ("participant", "the bullet"), ("animate", "false"), ("inferred", "true")] }

def ex_18 : Datum :=
  { id := "cruse1973_18"
    source := ⟨"cruse-1973", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the bullet did was smash John's collar-bone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "effective"), ("participant", "the bullet"), ("animate", "false"), ("inferred", "true")] }

def ex_19 : Datum :=
  { id := "cruse1973_19"
    source := ⟨"cruse-1973", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to the bullet was that it smashed John's collar-bone."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "effective"), ("participant", "the bullet"), ("animate", "false"), ("inferred", "true")] }

def ex_20 : Datum :=
  { id := "cruse1973_20"
    source := ⟨"cruse-1973", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Why does the door do that? B: What? A: Fly open every time the wind blows."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", ""), ("participant", "the door"), ("animate", "false"), ("neutralized", "true")] }

def ex_21 : Datum :=
  { id := "cruse1973_21"
    source := ⟨"cruse-1973", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Why does the vase do that? B: What? A: Keep falling off the shelf."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", ""), ("participant", "the vase"), ("animate", "false"), ("neutralized", "true")] }

def ex_22 : Datum :=
  { id := "cruse1973_22"
    source := ⟨"cruse-1973", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Why does that happen to the door? B: What? A: Why does it fly open every time the wind blows?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", ""), ("participant", "the door"), ("animate", "false"), ("neutralized", "true")] }

def ex_23 : Datum :=
  { id := "cruse1973_23"
    source := ⟨"cruse-1973", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Christ died in order to save us from our sins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "volitive"), ("participant", "Christ"), ("verbClass", "process")] }

def ex_24 : Datum :=
  { id := "cruse1973_24"
    source := ⟨"cruse-1973", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What Christ did was die in order to save us from our sins."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "volitive"), ("participant", "Christ"), ("verbClass", "process")] }

def ex_25 : Datum :=
  { id := "cruse1973_25"
    source := ⟨"cruse-1973", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to Christ was that he died in order to save us from our sins."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "volitive"), ("participant", "Christ"), ("verbClass", "process")] }

def ex_26 : Datum :=
  { id := "cruse1973_26"
    source := ⟨"cruse-1973", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John is doing is standing/sitting/lying in the middle of the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("participant", "John"), ("verbClass", "stative")] }

def ex_27 : Datum :=
  { id := "cruse1973_27"
    source := ⟨"cruse-1973", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What I did was have my passport ready."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("participant", "I"), ("verbClass", "stative")] }

def ex_28 : Datum :=
  { id := "cruse1973_28"
    source := ⟨"cruse-1973", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I am having my passport ready."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "progressive"), ("participant", "I"), ("verbClass", "stative")] }

def ex_29 : Datum :=
  { id := "cruse1973_29"
    source := ⟨"cruse-1973", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What you must do is be absent that day."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("participant", "you"), ("verbClass", "stative")] }

def ex_30 : Datum :=
  { id := "cruse1973_30"
    source := ⟨"cruse-1973", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are being absent."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "progressive"), ("participant", "you"), ("verbClass", "stative")] }

def ex_31 : Datum :=
  { id := "cruse1973_31"
    source := ⟨"cruse-1973", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was drift two miles further down the river, so as to avoid landing in enemy territory."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "volitive"), ("participant", "John")] }

def ex_32 : Datum :=
  { id := "cruse1973_32"
    source := ⟨"cruse-1973", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was not eat anything for two days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "volitive"), ("participant", "John")] }

def ex_33 : Datum :=
  { id := "cruse1973_33"
    source := ⟨"cruse-1973", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was be ready."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "volitive"), ("participant", "John"), ("verbClass", "stative")] }

def ex_34 : Datum :=
  { id := "cruse1973_34"
    source := ⟨"cruse-1973", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was not sleep that night, so as to forestall any surprise attack."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "volitive"), ("participant", "John")] }

def ex_35 : Datum :=
  { id := "cruse1973_35"
    source := ⟨"cruse-1973", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to John was that he did not sleep that night, so as to forestall any surprise attack."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "volitive"), ("participant", "John")] }

def ex_36 : Datum :=
  { id := "cruse1973_36"
    source := ⟨"cruse-1973", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was not sleep that night, through no fault of his own."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", ""), ("participant", "John")] }

def ex_37 : Datum :=
  { id := "cruse1973_37"
    source := ⟨"cruse-1973", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to John was that he did not sleep that night, through no fault of his own."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", ""), ("participant", "John")] }

def ex_38 : Datum :=
  { id := "cruse1973_38"
    source := ⟨"cruse-1973", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was die in a car accident."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", ""), ("participant", "John"), ("verbClass", "process")] }

def ex_39 : Datum :=
  { id := "cruse1973_39"
    source := ⟨"cruse-1973", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to John was that he died in a car accident."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", ""), ("participant", "John"), ("verbClass", "process")] }

def ex_40 : Datum :=
  { id := "cruse1973_40"
    source := ⟨"cruse-1973", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John accidentally trod on the toy, in order to punish the child."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "purpose"), ("features", "agentive"), ("participant", "John")] }

def ex_41 : Datum :=
  { id := "cruse1973_41"
    source := ⟨"cruse-1973", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was kick the bucket over accidentally."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_42 : Datum :=
  { id := "cruse1973_42"
    source := ⟨"cruse-1973", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kick the bucket over accidentally!"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "imperative"), ("features", "agentive"), ("participant", "the addressee"), ("inferred", "true")] }

def ex_43 : Datum :=
  { id := "cruse1973_43"
    source := ⟨"cruse-1973", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was sneeze."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_44 : Datum :=
  { id := "cruse1973_44"
    source := ⟨"cruse-1973", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to John was that he sneezed."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_45 : Datum :=
  { id := "cruse1973_45"
    source := ⟨"cruse-1973", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What John did was cry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_46 : Datum :=
  { id := "cruse1973_46"
    source := ⟨"cruse-1973", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to John was that he cried."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_47 : Datum :=
  { id := "cruse1973_47"
    source := ⟨"cruse-1973", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John carefully fell out of the window."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "carefully"), ("features", ""), ("participant", "John"), ("inferred", "true")] }

def ex_48 : Datum :=
  { id := "cruse1973_48"
    source := ⟨"cruse-1973", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John carefully and accidentally pushed the door open."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "carefully"), ("features", "agentive"), ("participant", "John"), ("inferred", "true")] }

def ex_49 : Datum :=
  { id := "cruse1973_49"
    source := ⟨"cruse-1973", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John carefully pushed the door open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "carefully"), ("features", "volitive+agentive"), ("participant", "John")] }

def ex_50 : Datum :=
  { id := "cruse1973_50"
    source := ⟨"cruse-1973", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These columns support the weight of the pediment."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "effective"), ("participant", "these columns"), ("animate", "false")] }

def ex_51 : Datum :=
  { id := "cruse1973_51"
    source := ⟨"cruse-1973", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What these columns do is support the weight of the pediment."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "effective"), ("participant", "these columns"), ("animate", "false")] }

def ex_52 : Datum :=
  { id := "cruse1973_52"
    source := ⟨"cruse-1973", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happens to these columns is that they support the weight of the pediment."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "effective"), ("participant", "these columns"), ("animate", "false")] }

def ex_53 : Datum :=
  { id := "cruse1973_53"
    source := ⟨"cruse-1973", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The flying stone broke the window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "effective"), ("participant", "the flying stone"), ("animate", "false")] }

def ex_54 : Datum :=
  { id := "cruse1973_54"
    source := ⟨"cruse-1973", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the flying stone did was break the window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "do"), ("features", "effective"), ("participant", "the flying stone"), ("animate", "false")] }

def ex_55 : Datum :=
  { id := "cruse1973_55"
    source := ⟨"cruse-1973", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What happened to the flying stone was that it broke the window."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "happen"), ("features", "effective"), ("participant", "the flying stone"), ("animate", "false")] }

def ex_56 : Datum :=
  { id := "cruse1973_56"
    source := ⟨"cruse-1973", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The wind opened the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "agentive"), ("participant", "the wind"), ("animate", "false")] }

def ex_57 : Datum :=
  { id := "cruse1973_57"
    source := ⟨"cruse-1973", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The stone broke the window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("participant", "the stone"), ("animate", "false")] }

def ex_58 : Datum :=
  { id := "cruse1973_58"
    source := ⟨"cruse-1973", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the window with a stone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "instrumental"), ("participant", "a stone"), ("animate", "false")] }

def ex_59 : Datum :=
  { id := "cruse1973_59"
    source := ⟨"cruse-1973", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the window with the stone: it therefore follows that the stone did something."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "entails"), ("features", "instrumental"), ("participant", "the stone"), ("animate", "false")] }

def ex_60 : Datum :=
  { id := "cruse1973_60"
    source := ⟨"cruse-1973", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "As a result of the explosion, a stone flew across the road and broke the window."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "effective"), ("participant", "a stone"), ("animate", "false")] }

def ex_61 : Datum :=
  { id := "cruse1973_61"
    source := ⟨"cruse-1973", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This key will open the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "instrumental"), ("participant", "this key"), ("animate", "false")] }

def ex_62 : Datum :=
  { id := "cruse1973_62"
    source := ⟨"cruse-1973", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The warder marched the prisoners across the yard."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "initiative"), ("participant", "the warder")] }

def ex_63 : Datum :=
  { id := "cruse1973_63"
    source := ⟨"cruse-1973", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John galloped the horse around the field."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "initiative"), ("participant", "John")] }

def ex_64 : Datum :=
  { id := "cruse1973_64"
    source := ⟨"cruse-1973", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John galloped the horse, which had died the previous day, round the field."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "initiativeDenial"), ("features", "initiative"), ("participant", "John")] }

def ex_65 : Datum :=
  { id := "cruse1973_65"
    source := ⟨"cruse-1973", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John galloped the horse, with which he had no means of communicating, around the field."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "initiativeDenial"), ("features", "initiative"), ("participant", "John")] }

def ex_66 : Datum :=
  { id := "cruse1973_66"
    source := ⟨"cruse-1973", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The warder marched the prisoners, who were successfully resisting any form of persuasion or command, across the yard."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "initiativeDenial"), ("features", "initiative"), ("participant", "the warder")] }

def ex_67 : Datum :=
  { id := "cruse1973_67"
    source := ⟨"cruse-1973", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John moved (himself) to avoid the falling stones."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "John")] }

def ex_68 : Datum :=
  { id := "cruse1973_68"
    source := ⟨"cruse-1973", "(68)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The machine automatically switches (itself) off at 6 p.m."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "the machine"), ("animate", "false")] }

def ex_69 : Datum :=
  { id := "cruse1973_69"
    source := ⟨"cruse-1973", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fire rapidly spread (itself) through the building."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "the fire"), ("animate", "false")] }

def ex_70 : Datum :=
  { id := "cruse1973_70"
    source := ⟨"cruse-1973", "(70)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every year, the sea, by constantly eating away at the shore, inched (itself) closer to the village."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "the sea"), ("animate", "false")] }

def ex_71 : Datum :=
  { id := "cruse1973_71"
    source := ⟨"cruse-1973", "(71)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The stone flew through the air."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", ""), ("participant", "the stone"), ("animate", "false"), ("inferred", "true")] }

def ex_72 : Datum :=
  { id := "cruse1973_72"
    source := ⟨"cruse-1973", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The stone flew itself through the air."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", ""), ("participant", "the stone"), ("animate", "false"), ("inferred", "true")] }

def ex_73 : Datum :=
  { id := "cruse1973_73"
    source := ⟨"cruse-1973", "(73)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball rolled across the floor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", ""), ("participant", "the ball"), ("animate", "false"), ("inferred", "true")] }

def ex_74 : Datum :=
  { id := "cruse1973_74"
    source := ⟨"cruse-1973", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball rolled itself across the floor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "the ball"), ("animate", "false"), ("inferred", "true")] }

def ex_75 : Datum :=
  { id := "cruse1973_75"
    source := ⟨"cruse-1973", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John laughed himself sore."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "John")] }

def ex_76 : Datum :=
  { id := "cruse1973_76"
    source := ⟨"cruse-1973", "(76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John shouted himself hoarse."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", "agentive"), ("participant", "John")] }

def ex_77 : Datum :=
  { id := "cruse1973_77"
    source := ⟨"cruse-1973", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fainted himself cold."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", ""), ("participant", "John")] }

def ex_78 : Datum :=
  { id := "cruse1973_78"
    source := ⟨"cruse-1973", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fell himself flat."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "reflexive"), ("features", ""), ("participant", "John")] }

def ex_79 : Datum :=
  { id := "cruse1973_79"
    source := ⟨"cruse-1973", "(79)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The stone flew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", ""), ("participant", "the stone"), ("animate", "false"), ("inferred", "true")] }

def ex_80 : Datum :=
  { id := "cruse1973_80"
    source := ⟨"cruse-1973", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The hawk flew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "agentive"), ("participant", "the hawk"), ("inferred", "true")] }

def ex_81 : Datum :=
  { id := "cruse1973_81"
    source := ⟨"cruse-1973", "(81)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The model aeroplane flew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "agentive"), ("participant", "the model aeroplane"), ("animate", "false"), ("inferred", "true")] }

def ex_82 : Datum :=
  { id := "cruse1973_82"
    source := ⟨"cruse-1973", "(82)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John flew the stone."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "causative"), ("features", ""), ("participant", "the stone"), ("animate", "false")] }

def ex_83 : Datum :=
  { id := "cruse1973_83"
    source := ⟨"cruse-1973", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John flew the hawk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "causative"), ("features", "agentive"), ("participant", "the hawk"), ("inferred", "true")] }

def ex_84 : Datum :=
  { id := "cruse1973_84"
    source := ⟨"cruse-1973", "(84)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John flew the model aeroplane."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "causative"), ("features", "agentive"), ("participant", "the model aeroplane"), ("animate", "false"), ("inferred", "true")] }

def ex_85a : Datum :=
  { id := "cruse1973_85a"
    source := ⟨"cruse-1973", "(85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The machine crushed the bottle when it fell on it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "effective"), ("participant", "the machine"), ("animate", "false")] }

def ex_85b : Datum :=
  { id := "cruse1973_85b"
    source := ⟨"cruse-1973", "(85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The machine crushed the bottle when we switched it on."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "agentive"), ("participant", "the machine"), ("animate", "false")] }

def ex_86a : Datum :=
  { id := "cruse1973_86a"
    source := ⟨"cruse-1973", "(86a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John smashed the window when he fell against it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "effective"), ("participant", "John")] }

def ex_86b : Datum :=
  { id := "cruse1973_86b"
    source := ⟨"cruse-1973", "(86b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John smashed the window with a stone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "plain"), ("features", "agentive"), ("participant", "John")] }

def ex_87 : Datum :=
  { id := "cruse1973_87"
    source := ⟨"cruse-1973", "(87)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The machine powerfully crushed the bottle when we switched it on."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "manner"), ("features", "agentive"), ("participant", "the machine"), ("animate", "false")] }

def ex_88 : Datum :=
  { id := "cruse1973_88"
    source := ⟨"cruse-1973", "(88)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The machine powerfully crushed the bottle when it fell on it."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "manner"), ("features", "effective"), ("participant", "the machine"), ("animate", "false")] }

def ex_89 : Datum :=
  { id := "cruse1973_89"
    source := ⟨"cruse-1973", "(89)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John vigorously smashed the window with a stone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("frame", "manner"), ("features", "agentive"), ("participant", "John")] }

def ex_90 : Datum :=
  { id := "cruse1973_90"
    source := ⟨"cruse-1973", "(90)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John vigorously smashed the window when he fell against it."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "manner"), ("features", "effective"), ("participant", "John")] }

def ex_91 : Datum :=
  { id := "cruse1973_91"
    source := ⟨"cruse-1973", "(91)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John vigorously looked at Mary."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("frame", "manner"), ("participant", "John")] }

def all : List Datum := [ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35, ex_36, ex_37, ex_38, ex_39, ex_40, ex_41, ex_42, ex_43, ex_44, ex_45, ex_46, ex_47, ex_48, ex_49, ex_50, ex_51, ex_52, ex_53, ex_54, ex_55, ex_56, ex_57, ex_58, ex_59, ex_60, ex_61, ex_62, ex_63, ex_64, ex_65, ex_66, ex_67, ex_68, ex_69, ex_70, ex_71, ex_72, ex_73, ex_74, ex_75, ex_76, ex_77, ex_78, ex_79, ex_80, ex_81, ex_82, ex_83, ex_84, ex_85a, ex_85b, ex_86a, ex_86b, ex_87, ex_88, ex_89, ex_90, ex_91]

/-- Lyons's verb classes at issue in the received opinions. -/
inductive VerbClass where
  /-- process: an obligatorily process verb, *die* -/
  | process
  /-- stative: A stative verb, *stand*, *have* -/
  | stative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `verbClass`. -/
def verbClass (e : Datum) : Option VerbClass :=
  e.parse? "verbClass" [("process", .process), ("stative", .stative)]

end Cruse1973.Examples
