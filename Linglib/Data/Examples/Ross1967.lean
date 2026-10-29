module

public import Linglib.Data.Examples.Schema

/-!
# `Ross1967` — typed example data

Auto-generated from `Linglib/Data/Examples/Ross1967.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ross1967.Examples`.
-/

@[expose] public section

namespace Ross1967.Examples

def ex4_13a : Datum :=
  { id := "ross1967_ex4_13a"
    source := ⟨"ross-1967", "(4.13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This is a hat which I'm going to see to it that my wife buys."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")] }

def ex4_15a : Datum :=
  { id := "ross1967_ex4_15a"
    source := ⟨"ross-1967", "(4.15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who does Phineas know a girl who is jealous of?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question"), ("constraint", "CNPC")] }

def ex4_18a : Datum :=
  { id := "ross1967_ex4_18a"
    source := ⟨"ross-1967", "(4.18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The hat which I believed the claim that Otto was wearing is red."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "CNPC")] }

def ex4_18b : Datum :=
  { id := "ross1967_ex4_18b"
    source := ⟨"ross-1967", "(4.18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The hat which I believed that Otto was wearing is red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")] }

def ex2_18 : Datum :=
  { id := "ross1967_ex2_18"
    source := ⟨"ross-1967", "(2.18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What sofa will he put the chair between some table and?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question"), ("constraint", "CSC")] }

def ex4_82a : Datum :=
  { id := "ross1967_ex4_82a"
    source := ⟨"ross-1967", "(4.82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The lute which Henry plays and sings madrigals is warped."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "CSC")] }

def ex4_82d : Datum :=
  { id := "ross1967_ex4_82d"
    source := ⟨"ross-1967", "(4.82d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which trombone did the nurse polish and the plumber computed my tax?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question"), ("constraint", "CSC")] }

def ex4_184a : Datum :=
  { id := "ross1967_ex4_184a"
    source := ⟨"ross-1967", "(4.184a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boy whose guardian's employer we elected president ratted on us."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")] }

def ex4_184b : Datum :=
  { id := "ross1967_ex4_184b"
    source := ⟨"ross-1967", "(4.184b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boy whose guardian's we elected employer president ratted on us."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "LBC")] }

def ex4_184c : Datum :=
  { id := "ross1967_ex4_184c"
    source := ⟨"ross-1967", "(4.184c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The boy whose we elected guardian's employer president ratted on us."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "LBC")] }

def ex4_251a : Datum :=
  { id := "ross1967_ex4_251a"
    source := ⟨"ross-1967", "(4.251a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher who the reporters expected that the principal would fire is a crusty old battleax."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")] }

def ex4_251b : Datum :=
  { id := "ross1967_ex4_251b"
    source := ⟨"ross-1967", "(4.251b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher who that the principal would fire was expected by the reporters is a crusty old battleax."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization"), ("constraint", "SSC")] }

def ex4_251c : Datum :=
  { id := "ross1967_ex4_251c"
    source := ⟨"ross-1967", "(4.251c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The teacher who it was expected by the reporters that the principal would fire is a crusty old battleax."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "relativization")] }

def ex4_252 : Datum :=
  { id := "ross1967_ex4_252"
    source := ⟨"ross-1967", "(4.252)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Of which cars were the hoods damaged by the explosion?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "question")] }

def ex6_128b : Datum :=
  { id := "ross1967_ex6_128b"
    source := ⟨"ross-1967", "(6.128b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My father, the man he works with in Boston is going to tell the police that that traffic expert has set that traffic light on the corner of Murk Street far too slow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "CNPC")] }

def ex6_135b : Datum :=
  { id := "ross1967_ex6_135b"
    source := ⟨"ross-1967", "(6.135b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This guitar, I've sung folksongs and accompanied myself on it all my life."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "CSC")] }

def ex6_136 : Datum :=
  { id := "ross1967_ex6_136"
    source := ⟨"ross-1967", "(6.136)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My father, that he's lived here all his life is well-known to the cops."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "SSC")] }

def ex6_137 : Datum :=
  { id := "ross1967_ex6_137"
    source := ⟨"ross-1967", "(6.137)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My wife, somebody stole her handbag last night."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "leftDislocation"), ("constraint", "LBC")] }

def all : List Datum := [ex4_13a, ex4_15a, ex4_18a, ex4_18b, ex2_18, ex4_82a, ex4_82d, ex4_184a, ex4_184b, ex4_184c, ex4_251a, ex4_251b, ex4_251c, ex4_252, ex6_128b, ex6_135b, ex6_136, ex6_137]

end Ross1967.Examples
