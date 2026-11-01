module

public import Linglib.Data.Examples.Schema

/-!
# `ArnoldEtAl2000` — typed example data

Auto-generated from `Linglib/Data/Examples/ArnoldEtAl2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ArnoldEtAl2000.Examples`.
-/

@[expose] public section

namespace ArnoldEtAl2000.Examples

def ex_1 : Datum :=
  { id := "arnoldetal2000_1"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The waiter brought the wine we had ordered to the table"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The waiter brought to the table the wine we had ordered", .acceptable)]
    readings := []
    paperFeatures := [("construction", "HNPS")] }

def ex_2 : Datum :=
  { id := "arnoldetal2000_2"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris gave a bowl of Mom's traditional cranberry sauce to Terry"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Chris gave Terry a bowl of Mom's traditional cranberry sauce", .acceptable)]
    readings := []
    paperFeatures := [("construction", "DA")] }

def ex_3 : Datum :=
  { id := "arnoldetal2000_3"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy picked the freshly baked apple pie up."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Sandy picked up the freshly baked apple pie.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "verb-particle")] }

def ex_5 : Datum :=
  { id := "arnoldetal2000_5"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave to Mary the valuable book that was extremely difficult to find"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I gave the valuable book that was extremely difficult to find to Mary", .acceptable)]
    readings := []
    paperFeatures := [("construction", "HNPS"), ("first", "to Mary"), ("second", "the valuable book that was extremely difficult to find"), ("eicWords", "4")] }

def ex_6 : Datum :=
  { id := "arnoldetal2000_6"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Informativeness account shares with the processing account the claim that a subjectless sentence is not a grammatical option for the child, and that the omission is due to some aspect of performance"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The Informativeness account shares the claim that a subjectless sentence is not a grammatical option for the child, and that the omission is due to some aspect of performance with the processing account", .acceptable)]
    readings := []
    paperFeatures := [("construction", "HNPS"), ("first", "with the processing account"), ("second", "the claim that a subjectless sentence is not a grammatical option for the child, and that the omission is due to some aspect of performance")] }

def ex_8 : Datum :=
  { id := "arnoldetal2000_8"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That brings to the plate Barry Bonds."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "HNPS"), ("first", "to the plate"), ("second", "Barry Bonds"), ("exception", "planning")] }

def ex_9 : Datum :=
  { id := "arnoldetal2000_9"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "to take as input a grammar and to associate with it, as output, an optimal structure"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "HNPS"), ("shifted", "a grammar; an optimal structure"), ("newness", "new")] }

def ex_10 : Datum :=
  { id := "arnoldetal2000_10"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to identify in the inner city the fifth graders who could really take off"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "HNPS"), ("first", "in the inner city"), ("second", "the fifth graders who could really take off"), ("function", "ambiguity avoidance")] }

def ex_11 : Datum :=
  { id := "arnoldetal2000_11"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When Kennedy announced last July his plans to quit"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "HNPS"), ("first", "last July"), ("second", "his plans to quit"), ("function", "ambiguity avoidance")] }

def t1_bring : Datum :=
  { id := "arnoldetal2000_t1_bring"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 1"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "It is enough to bring tears to the eyes of the Statue of Justice that stands silently in front of the Supreme Court of Canada."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "HNPS"), ("verb", "bring to"), ("order", "nonshifted"), ("first", "tears"), ("second", "to the eyes of the Statue of Justice that stands silently in front of the Supreme Court of Canada")] }

def t1_take : Datum :=
  { id := "arnoldetal2000_t1_take"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 1"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "It takes into account the need not to be overtaken by the constant evolution of the labour market."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "HNPS"), ("verb", "take into account"), ("order", "shifted"), ("first", "into account"), ("second", "the need not to be overtaken by the constant evolution of the labour market")] }

def t1_give : Datum :=
  { id := "arnoldetal2000_t1_give"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 1"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The bank was told it should give its business to a friend of the Government."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "DA"), ("verb", "give"), ("order", "prepositional"), ("first", "its business"), ("second", "to a friend of the Government")] }

def ex_12 : Datum :=
  { id := "arnoldetal2000_12"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: What about the yellow duck? B: Give it the small green crayon. A: What about the. . . ."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "DA")] }

def ex_13 : Datum :=
  { id := "arnoldetal2000_13"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Object-mover: What about the red dog, the yellow dog, and the purple dog? Director: Um, you should look for the tic tacs and find the box with the white and green tic tacs and give that to the red dog."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "DA"), ("order", "prepositional"), ("given", "theme"), ("first", "that"), ("second", "to the red dog")] }

def ex_14 : Datum :=
  { id := "arnoldetal2000_14"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are going to give the ducks objects. You are going to give the yellow duck A key. 'Kay. You're going to give a du- the red duck, um, a melon. And you're going to give THE um pink duck A um rectangular eraser, it's black."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "DA"), ("order", "double object"), ("given", "both")] }

def ex_16 : Datum :=
  { id := "arnoldetal2000_16"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give the pink giraffe the plum, the green giraffe the pear ... and the yellow giraffe the tur er uhh plum."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "DA"), ("elliptical", "true")] }

def ex_17 : Datum :=
  { id := "arnoldetal2000_17"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Having given much consideration and attention to it ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "DA"), ("first", "much consideration and attention"), ("second", "to it"), ("newness", "first new, second given"), ("exception", "other factors")] }

def t4_do : Datum :=
  { id := "arnoldetal2000_t4_do"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give the white rabbit the carrot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "double object"), ("orderClass", "goal first")] }

def t4_hnps : Datum :=
  { id := "arnoldetal2000_t4_hnps"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give to the white rabbit the carrot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "heavy-NP-shifted"), ("orderClass", "goal first")] }

def t4_passg : Datum :=
  { id := "arnoldetal2000_t4_passg"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The white rabbit should be given the carrot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passivized goal"), ("orderClass", "goal first")] }

def t4_dotop : Datum :=
  { id := "arnoldetal2000_t4_dotop"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The white rabbit, give the carrot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "double object, goal topicalized"), ("orderClass", "goal first")] }

def t4_preptop : Datum :=
  { id := "arnoldetal2000_t4_preptop"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To the white rabbit, give the carrot."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "prepositional, goal topicalized"), ("orderClass", "goal first")] }

def t4_prep : Datum :=
  { id := "arnoldetal2000_t4_prep"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give the carrot to the white rabbit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "prepositional"), ("orderClass", "theme first")] }

def t4_passt : Datum :=
  { id := "arnoldetal2000_t4_passt"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The carrot should be given to the white rabbit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passivized theme"), ("orderClass", "theme first")] }

def t4_prepttop : Datum :=
  { id := "arnoldetal2000_t4_prepttop"
    source := ⟨"arnold-losongco-wasow-ginstrom-2000", "Table 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The carrot, give to the white rabbit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "prepositional, theme topicalized"), ("orderClass", "theme first")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_5, ex_6, ex_8, ex_9, ex_10, ex_11, t1_bring, t1_take, t1_give, ex_12, ex_13, ex_14, ex_16, ex_17, t4_do, t4_hnps, t4_passg, t4_dotop, t4_preptop, t4_prep, t4_passt, t4_prepttop]

end ArnoldEtAl2000.Examples
