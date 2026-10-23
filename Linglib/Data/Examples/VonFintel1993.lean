module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintel1993` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintel1993.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintel1993.Examples`.
-/

@[expose] public section

namespace VonFintel1993.Examples

def ex_1a : Datum :=
  { id := "vonfintel1993_1a"
    source := ⟨"von-fintel-1993", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student but John attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John is the only student who did not attend", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("determiner", "every")] }

def ex_1b : Datum :=
  { id := "vonfintel1993_1b"
    source := ⟨"von-fintel-1993", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for John, every student attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("determiner", "every")] }

def ex_2b : Datum :=
  { id := "vonfintel1993_2b"
    source := ⟨"von-fintel-1993", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student but John attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John is the only student who attended", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("determiner", "no")] }

def ex_4 : Datum :=
  { id := "vonfintel1993_4"
    source := ⟨"hoeksema-1990", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(4)"⟩
    language := "stan1293"
    primaryText := "Well, except for Dr. Samuels everybody has an alibi, inspector. Let's go see Dr. Samuels to find out if he's got one too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("test", "cancellability")] }

def ex_5 : Datum :=
  { id := "vonfintel1993_5"
    source := ⟨"von-fintel-1993", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, everybody but Dr. Samuels has an alibi, inspector. Let's go see Dr. Samuels to find out if he's got one too."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("test", "cancellability")] }

def ex_7 : Datum :=
  { id := "vonfintel1993_7"
    source := ⟨"von-fintel-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I just noticed that every student but John attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the speaker noticed that every other student attended and that John did not", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("test", "embedding")] }

def ex_10_everyone : Datum :=
  { id := "vonfintel1993_10_everyone"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "everyone but Mary"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "every")] }

def ex_10_nobody : Datum :=
  { id := "vonfintel1993_10_nobody"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "nobody but John"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "no")] }

def ex_10_anyone : Datum :=
  { id := "vonfintel1993_10_anyone"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "anyone but Carter"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "any")] }

def ex_10_somebody : Datum :=
  { id := "vonfintel1993_10_somebody"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "somebody but Kim"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "some")] }

def ex_10_somewhere : Datum :=
  { id := "vonfintel1993_10_somewhere"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "somewhere but here"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("anywhere but here", .acceptable)]
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "some")] }

def ex_10_all_of : Datum :=
  { id := "vonfintel1993_10_all_of"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "all of my friends but Chris"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("none of my friends but Chris", .acceptable)]
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "all")] }

def ex_10_most_of : Datum :=
  { id := "vonfintel1993_10_most_of"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "most of my friends but Chris"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("many of my friends but Chris", .ungrammatical), ("three of my friends but Chris", .ungrammatical), ("some of my friends but Chris", .ungrammatical)]
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "most")] }

def ex_10_everything : Datum :=
  { id := "vonfintel1993_10_everything"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "everything but the kitchen sink"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "every")] }

def ex_10_none : Datum :=
  { id := "vonfintel1993_10_none"
    source := ⟨"horn-1989", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(10)"⟩
    language := "stan1293"
    primaryText := "None but the brave deserves the fair."
    glossedTokens := []
    context := "Dryden."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "no")] }

def ex_13 : Datum :=
  { id := "vonfintel1993_13"
    source := ⟨"von-fintel-1993", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every human being is mortal. Therefore every male human being is mortal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("No human being is mortal. Therefore no male human being is mortal.", .acceptable)]
    readings := []
    paperFeatures := [("inference", "valid"), ("property", "left downward monotonicity")] }

def ex_14 : Datum :=
  { id := "vonfintel1993_14"
    source := ⟨"von-fintel-1993", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student but John attended the meeting. Therefore every student but John and Jill attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := [("No student but John attended the meeting. Therefore no student but John and Jill attended the meeting.", .unacceptable)]
    readings := []
    paperFeatures := [("inference", "invalid"), ("property", "left downward monotonicity")] }

def ex_16 : Datum :=
  { id := "vonfintel1993_16"
    source := ⟨"hoeksema-1987", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(16)"⟩
    language := "stan1293"
    primaryText := "all the students but each foreigner"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("complement", "quantifier")] }

def ex_19 : Datum :=
  { id := "vonfintel1993_19"
    source := ⟨"von-fintel-1993", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some female human being is an athlete. Therefore some human being is an athlete."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "valid"), ("property", "left upward monotonicity")] }

def ex_22 : Datum :=
  { id := "vonfintel1993_22"
    source := ⟨"von-fintel-1993", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student but John and Mary attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John and Mary are the students who did not attend", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("determiner", "every")] }

def ex_25a : Datum :=
  { id := "vonfintel1993_25a"
    source := ⟨"von-fintel-1993", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most students attended the meeting."
    glossedTokens := []
    context := "Tom, John and Harry did not attend; Bill and Mary did."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("determiner", "most")] }

def ex_25b : Datum :=
  { id := "vonfintel1993_25b"
    source := ⟨"von-fintel-1993", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most students but Tom and John attended the meeting."
    glossedTokens := []
    context := "Tom, John and Harry did not attend; Bill and Mary did."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("determiner", "most")] }

def ex_27a : Datum :=
  { id := "vonfintel1993_27a"
    source := ⟨"von-fintel-1993", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who but a total idiot would have said a thing like that?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("rhetorical: nobody but a total idiot would have", .acceptable)]
    paperFeatures := [("exceptive", "but"), ("construction", "wh-question")] }

def ex_27b : Datum :=
  { id := "vonfintel1993_27b"
    source := ⟨"von-fintel-1993", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who but Leslie is coming to a party?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("construction", "wh-question")] }

def ex_28a : Datum :=
  { id := "vonfintel1993_28a"
    source := ⟨"geis-1973", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(28a)"⟩
    language := "stan1293"
    primaryText := "Everybody but John and but Mary attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Everybody but John and Mary attended the meeting.", .acceptable)]
    readings := []
    paperFeatures := [("exceptive", "but"), ("construction", "conjunction")] }

def ex_31b : Datum :=
  { id := "vonfintel1993_31b"
    source := ⟨"von-fintel-1993", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for the famous detective, no one suspected the cook."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("No one, except for the famous detective, suspected the cook.", .acceptable), ("No one suspected the cook, except for the famous detective.", .acceptable)]
    readings := []
    paperFeatures := [("exceptive", "except for"), ("position", "peripheral")] }

def ex_32 : Datum :=
  { id := "vonfintel1993_32"
    source := ⟨"von-fintel-1993", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone loved the new show and no one thought it would be canceled so soon. Except for George, of course."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("use", "afterthought")] }

def ex_33a : Datum :=
  { id := "vonfintel1993_33a"
    source := ⟨"von-fintel-1993", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for Joan, most cabinet members liked the proposal."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Except for John, few employees accepted the pay cut.", .acceptable)]
    readings := [("appositive: Joan is a notable exception", .acceptable)]
    paperFeatures := [("exceptive", "except for"), ("use", "appositive"), ("determiner", "most")] }

def ex_34a : Datum :=
  { id := "vonfintel1993_34a"
    source := ⟨"von-fintel-1993", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for Jim, no one really liked the soup."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("use", "restrictive"), ("determiner", "no")] }

def ex_34b : Datum :=
  { id := "vonfintel1993_34b"
    source := ⟨"von-fintel-1993", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for Jane, my relatives are (all) total bores."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("use", "restrictive"), ("determiner", "definite")] }

def ex_34c : Datum :=
  { id := "vonfintel1993_34c"
    source := ⟨"von-fintel-1993", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for the assistant professors, most faculty members supported the dean."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("use", "restrictive"), ("determiner", "most")] }

def ex_35a : Datum :=
  { id := "vonfintel1993_35a"
    source := ⟨"hoeksema-1987", ""⟩
    reportedIn := some ⟨"von-fintel-1993", "(35a)"⟩
    language := "stan1293"
    primaryText := "Except for John, who would say a thing like that?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Who but John would say a thing like that?", .acceptable)]
    readings := [("ordinary informative question", .acceptable)]
    paperFeatures := [("exceptive", "except for"), ("construction", "wh-question")] }

def ex_36a : Datum :=
  { id := "vonfintel1993_36a"
    source := ⟨"von-fintel-1993", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for John and except for Mary, nobody complained."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("construction", "conjunction")] }

def ex_36b : Datum :=
  { id := "vonfintel1993_36b"
    source := ⟨"von-fintel-1993", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nobody but John and but Mary complained."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "but"), ("construction", "conjunction")] }

def ex_37 : Datum :=
  { id := "vonfintel1993_37"
    source := ⟨"von-fintel-1993", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Except for John, everybody likes John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "except for"), ("test", "sentence-level subtraction")] }

def ex_42 : Datum :=
  { id := "vonfintel1993_42"
    source := ⟨"von-fintel-1993", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Besides John, five other students attended the meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exceptive", "besides"), ("determiner", "numeral")] }

def all : List Datum := [ex_1a, ex_1b, ex_2b, ex_4, ex_5, ex_7, ex_10_everyone, ex_10_nobody, ex_10_anyone, ex_10_somebody, ex_10_somewhere, ex_10_all_of, ex_10_most_of, ex_10_everything, ex_10_none, ex_13, ex_14, ex_16, ex_19, ex_22, ex_25a, ex_25b, ex_27a, ex_27b, ex_28a, ex_31b, ex_32, ex_33a, ex_34a, ex_34b, ex_34c, ex_35a, ex_36a, ex_36b, ex_37, ex_42]

end VonFintel1993.Examples
