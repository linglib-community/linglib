module

public import Linglib.Data.Examples.Schema

/-!
# `Heim1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1992.Examples`.
-/

@[expose] public section

namespace Heim1992.Examples

def s1 : Datum :=
  { id := "heim1992_s1"
    source := ⟨"heim-1992", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick wants to sell his cello."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("presupposition", "Patrick believes he owns a cello")] }

def s2 : Datum :=
  { id := "heim1992_s2"
    source := ⟨"heim-1992", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick is under the misconception that he owns a cello, and he wants to sell his cello."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("presupposition", "none as a whole")] }

def s10 : Datum :=
  { id := "heim1992_s10"
    source := ⟨"heim-1992", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that it is raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("rule", "(13): true in w iff it rains in every world of Dox_J(w)")] }

def s19 : Datum :=
  { id := "heim1992_s19"
    source := ⟨"heim-1992", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that Mary is here, and he believes that Susan is here too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("lf", "(20): too_i coindexed with Mary_i, Susan focused"), ("presupposition", "none as a whole")] }

def s25 : Datum :=
  { id := "heim1992_s25"
    source := ⟨"heim-1992", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doubts that Mary is here and/but believes that Susan is here too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("presupposition", "guaranteed undefined after the first conjunct"), ("felicity", "infelicitous")] }

def s26 : Datum :=
  { id := "heim1992_s26"
    source := ⟨"heim-1992", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doubts that Mary is here. He believes that if Susan were here too, there would be dancing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("presupposition", "undefined; the conditional inherits its antecedent's presupposition"), ("felicity", "infelicitous")] }

def s28 : Datum :=
  { id := "heim1992_s28"
    source := ⟨"heim-1992", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick and Ann both dream of winning cellos. Ann would like one for her own use. Patrick wants to sell his cello for a profit."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("presupposition", "none as a whole")] }

def s29 : Datum :=
  { id := "heim1992_s29"
    source := ⟨"heim-1992", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants Fred to come, and he wants Jim to come too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("presupposition", "none as a whole")] }

def s30 : Datum :=
  { id := "heim1992_s30"
    source := ⟨"heim-1992", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that Mary is coming, and he wants Susan to come too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("presupposition", "none as a whole")] }

def s32a : Datum :=
  { id := "heim1992_s32a"
    source := ⟨"heim-1992", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas wants a free trip on the Concorde."
    glossedTokens := []
    context := "Nicholas is not willing to pay the $3,000 that he believes it would cost him if he flew to Paris on the Concorde, but he would love to fly on the Concorde if he could get the trip for free."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("source", "Asher 1987")] }

def s32b : Datum :=
  { id := "heim1992_s32b"
    source := ⟨"heim-1992", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nicholas wants a trip on the Concorde."
    glossedTokens := []
    context := "Nicholas is not willing to pay the $3,000 that he believes it would cost him if he flew to Paris on the Concorde, but he would love to fly on the Concorde if he could get the trip for free."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("source", "Asher 1987")] }

def s33 : Datum :=
  { id := "heim1992_s33"
    source := ⟨"heim-1992", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want to teach Tuesdays and Thursdays next semester."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("truth", "true under (31), false under (27)")] }

def s41 : Datum :=
  { id := "heim1992_s41"
    source := ⟨"heim-1992", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(John hired a babysitter because) he wants to go to the movies tonight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.3"), ("status", "no doubt about where John will be")] }

def s42 : Datum :=
  { id := "heim1992_s42"
    source := ⟨"heim-1992", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want this weekend to last forever. (But I know, of course, that it will be over in a few hours.)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.3"), ("status", "wanting what one is convinced will not happen")] }

def s44 : Datum :=
  { id := "heim1992_s44"
    source := ⟨"heim-1992", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick intends to sell his cello (right now)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.3"), ("presupposition", "Patrick believes he has a cello independently of what he does")] }

def s46 : Datum :=
  { id := "heim1992_s46"
    source := ⟨"heim-1992", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick wants me to buy him a cello, although he believes that his cello is going to take up a lot of space."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4"), ("presupposition", "not filtered: want before believe")] }

def s47a : Datum :=
  { id := "heim1992_s47a"
    source := ⟨"heim-1992", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred believes that his wife will buy him a car. He hopes that it will be a Porsche."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4"), ("source", "Asher 1987"), ("anaphora", "it as the car his wife will buy him")] }

def s47b : Datum :=
  { id := "heim1992_s47b"
    source := ⟨"heim-1992", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred hopes that he will get a Porsche. He believes that his wife will buy it for him."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4"), ("source", "Asher 1987")] }

def s47c : Datum :=
  { id := "heim1992_s47c"
    source := ⟨"heim-1992", "(47c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to have a Porsche. He believes his mother will buy it for him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4"), ("source", "Asher 1987")] }

def s48 : Datum :=
  { id := "heim1992_s48"
    source := ⟨"heim-1992", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants a woman to marry him. He believes he can make her happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4"), ("source", "Asher 1987"), ("reading", "the belief as an implicit conditional")] }

def s49 : Datum :=
  { id := "heim1992_s49"
    source := ⟨"heim-1992", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan wants a pet. She believes she will look after it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4"), ("source", "Cresswell 1988"), ("reading", "the belief as an implicit conditional")] }

def s50 : Datum :=
  { id := "heim1992_s50"
    source := ⟨"heim-1992", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want Gabriela to have won."
    glossedTokens := []
    context := "Suppose I had to miss the last set of the Wimbledon women's final because of a hairdresser's appointment, so I don't know who won, though I do know the game is over and decided by now."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4")] }

def s51 : Datum :=
  { id := "heim1992_s51"
    source := ⟨"heim-1992", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "... and I am sure that it made Steffi cry hard."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2.4")] }

def s52 : Datum :=
  { id := "heim1992_s52"
    source := ⟨"heim-1992", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wishes he would teach on Tuesdays."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal base", "not doxastic: John may be certain he will not teach Tuesdays")] }

def s53 : Datum :=
  { id := "heim1992_s53"
    source := ⟨"heim-1992", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes that Mary is the only one here, and he wishes Susan were here too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "none as a whole")] }

def s54 : Datum :=
  { id := "heim1992_s54"
    source := ⟨"heim-1992", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is glad he will teach on Tuesdays."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "John believes he will teach on Tuesdays")] }

def s55 : Datum :=
  { id := "heim1992_s55"
    source := ⟨"heim-1992", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought he was late and was glad that Bill was late too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "satisfied in the belief-worlds")] }

def s56a : Datum :=
  { id := "heim1992_s56a"
    source := ⟨"heim-1992", "(56a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes Mary is coming, and he is glad Susan is coming too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "none as a whole")] }

def s56b : Datum :=
  { id := "heim1992_s56b"
    source := ⟨"heim-1992", "(56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believes Mary is coming, and he wishes Susan were coming too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "none as a whole")] }

def s57a : Datum :=
  { id := "heim1992_s57a"
    source := ⟨"heim-1992", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick is glad he sold his cello."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "accommodated: Patrick believes he sold his cello")] }

def s57b : Datum :=
  { id := "heim1992_s57b"
    source := ⟨"heim-1992", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patrick wishes he had sold his cello."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("presupposition", "accommodated: Patrick believes he did not sell his cello")] }

def s59 : Datum :=
  { id := "heim1992_s59"
    source := ⟨"heim-1992", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John attended too, ..."
    glossedTokens := []
    context := "It is already in the common ground that Mary attended."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3.1"), ("presupposition", "someone else attended, in the common ground")] }

def s60 : Datum :=
  { id := "heim1992_s60"
    source := ⟨"heim-1992", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John had attended too, ..."
    glossedTokens := []
    context := "It is already in the common ground that Mary attended."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3.1"), ("presupposition", "someone else attended, in the common ground")] }

def all : List Datum := [s1, s2, s10, s19, s25, s26, s28, s29, s30, s32a, s32b, s33, s41, s42, s44, s46, s47a, s47b, s47c, s48, s49, s50, s51, s52, s53, s54, s55, s56a, s56b, s57a, s57b, s59, s60]

end Heim1992.Examples
