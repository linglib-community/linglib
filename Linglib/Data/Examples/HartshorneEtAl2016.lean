module

public import Linglib.Data.Examples.Schema

/-!
# `HartshorneEtAl2016` — typed example data

Auto-generated from `Linglib/Data/Examples/HartshorneEtAl2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartshorneEtAl2016.Examples`.
-/

@[expose] public section

namespace HartshorneEtAl2016.Examples

def fear : Datum :=
  { id := "hartshorneetal2016_fear"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes feared Bartholomew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "fearType"), ("verbType", "fear"), ("subject", "experiencer")] }

def frighten : Datum :=
  { id := "hartshorneetal2016_frighten"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes frightened Bartholomew."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "frightenType"), ("verbType", "frighten"), ("subject", "stimulus")] }

def episode : Datum :=
  { id := "hartshorneetal2016_episode"
    source := ⟨"hartshorne-etal-2016", "§2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bats swooped out of the cave and frightened Agnes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The bats swooped out of the cave and Agnes feared them.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "frightenType"), ("verbType", "frighten")] }

def stageLevel : Datum :=
  { id := "hartshorneetal2016_stageLevel"
    source := ⟨"hartshorne-etal-2016", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Agnes concerned Bartholomew yesterday in the kitchen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Agnes feared Bartholomew yesterday in the kitchen.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "1.2"), ("phenomenon", "frightenType"), ("verbType", "frighten")] }

def exp1 : Datum :=
  { id := "hartshorneetal2016_exp1"
    source := ⟨"hartshorne-etal-2016", "§2.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sally frightened Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1.1"), ("phenomenon", "durationRating"), ("experiment", "1")] }

def exp2 : Datum :=
  { id := "hartshorneetal2016_exp2"
    source := ⟨"hartshorne-etal-2016", "§2.2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary frightened Sally."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.1"), ("phenomenon", "causationJudgment"), ("experiment", "2")] }

def ex_2a : Datum :=
  { id := "hartshorneetal2016_2a"
    source := ⟨"hartshorne-etal-2016", "(2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa koomori-o kowagat-ta."
    glossedTokens := [("Taro-wa", "Taro-TOPIC"), ("koomori-o", "bat-ACC"), ("kowagat-ta", "fear-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "fearType"), ("verbType", "fear")] }

def ex_2b : Datum :=
  { id := "hartshorneetal2016_2b"
    source := ⟨"hartshorne-etal-2016", "(2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Koomori-wa Taro-o kowagar-ase-ta."
    glossedTokens := [("Koomori-wa", "bat-TOPIC"), ("Taro-o", "Taro-ACC"), ("kowagar-ase-ta", "fear-CAUS-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "frightenType"), ("verbType", "frighten"), ("causativeAffix", "sase")] }

def ex_3a : Datum :=
  { id := "hartshorneetal2016_3a"
    source := ⟨"hartshorne-etal-2016", "(3a)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Ken douyos the unexpected exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1.1"), ("phenomenon", "novelVerb"), ("experiment", "5"), ("syntax", "fear")] }

def ex_3b : Datum :=
  { id := "hartshorneetal2016_3b"
    source := ⟨"hartshorne-etal-2016", "(3b)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "The unexpected exam douyos Ken."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1.1"), ("phenomenon", "novelVerb"), ("experiment", "5"), ("syntax", "frighten")] }

def ex_5 : Datum :=
  { id := "hartshorneetal2016_5"
    source := ⟨"hartshorne-etal-2016", "(5)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Some people wixter each other. Do you know what wixter is? Wixter is when you want something that somebody else has. Or maybe you think somebody else is so cool you wish you were just like them. That means you feel wixter. Do you feel wixter for anybody? [Discussion] What is your favorite thing to do? [Discussion] What if you knew a kid who got to do [favorite thing] all the time? You'd probably feel wixter, wouldn't you?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9"), ("semanticType", "attitude")] }

def ex_6 : Datum :=
  { id := "hartshorneetal2016_6"
    source := ⟨"hartshorne-etal-2016", "(6)"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Some people gorfin each other. Do you know what gorfin is? You feel gorfin when you see something really, really gross. Or if you had to hold something really slimy, you might feel gorfin. Can you think of any times you felt gorfin? [Discussion] What's the grossest thing you can think of? [Discussion] If you saw that, you might feel gorfin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9"), ("semanticType", "episode")] }

def exp9q : Datum :=
  { id := "hartshorneetal2016_exp9q"
    source := ⟨"hartshorne-etal-2016", "§4.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did Bear wixter?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "novelVerb"), ("experiment", "9")] }

def ex_7 : Datum :=
  { id := "hartshorneetal2016_7"
    source := ⟨"hartshorne-etal-2016", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The newspaper frightened John about the housing bubble."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.4.3"), ("phenomenon", "frightenType"), ("verbType", "frighten")] }

def all : List Datum := [fear, frighten, episode, stageLevel, exp1, exp2, ex_2a, ex_2b, ex_3a, ex_3b, ex_5, ex_6, exp9q, ex_7]

end HartshorneEtAl2016.Examples
