module

public import Linglib.Data.Examples.Schema

/-!
# `Sbardolini2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Sbardolini2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sbardolini2026.Examples`.
-/

@[expose] public section

namespace Sbardolini2026.Examples

def table1_episodic : Datum :=
  { id := "sbardolini2026_table1_episodic"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ate any pizza"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "Fx"), ("sum", "true")] }

def table1_negation : Datum :=
  { id := "sbardolini2026_table1_negation"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't eat any pizza"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "¬Fx"), ("sum", "false")] }

def table1_everyScope : Datum :=
  { id := "sbardolini2026_table1_everyScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who left ate any pizza"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Every A)F"), ("sum", "true")] }

def table1_everyRestrictor : Datum :=
  { id := "sbardolini2026_table1_everyRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who ate any pizza left"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Every F)A"), ("sum", "false")] }

def table1_someScope : Datum :=
  { id := "sbardolini2026_table1_someScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone who left ate any pizza"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Some A)F"), ("sum", "true")] }

def table1_someRestrictor : Datum :=
  { id := "sbardolini2026_table1_someRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Someone who ate any pizza left"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Some F)A"), ("sum", "true")] }

def table1_mostScope : Datum :=
  { id := "sbardolini2026_table1_mostScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most professors ate any pizza"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Most As)F"), ("sum", "true")] }

def table1_mostRestrictor : Datum :=
  { id := "sbardolini2026_table1_mostRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most professors who ate any pizza left"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Most Fs)A"), ("sum", "false")] }

def table1_antecedent : Datum :=
  { id := "sbardolini2026_table1_antecedent"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary drank anything, she got sick"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "If F, A"), ("sum", "false")] }

def table1_consequent : Datum :=
  { id := "sbardolini2026_table1_consequent"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary got sick, she drank anything"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "If A, F"), ("sum", "true")] }

def table1_question : Datum :=
  { id := "sbardolini2026_table1_question"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did Mary drink anything?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "Fx?"), ("sum", "false")] }

def table1_imperative : Datum :=
  { id := "sbardolini2026_table1_imperative"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Drink anything!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "F!"), ("sum", "false")] }

def table1_possibility : Datum :=
  { id := "sbardolini2026_table1_possibility"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary might drink anything"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "◇Fx"), ("sum", "false")] }

def table1_necessity : Datum :=
  { id := "sbardolini2026_table1_necessity"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary must drink anything"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "□Fx"), ("sum", "true")] }

def table1_genericScope : Datum :=
  { id := "sbardolini2026_table1_genericScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary eats anything"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "GEN[(A)F]"), ("sum", "false")] }

def table1_genericRestrictor : Datum :=
  { id := "sbardolini2026_table1_genericRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anybody knows the Beatles"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "GEN[(F)A]"), ("sum", "false")] }

def table1_tautology : Datum :=
  { id := "sbardolini2026_table1_tautology"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Zero or more students read anything"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "|A∩F| ≤ 0"), ("sum", "true")] }

def table1_contradiction : Datum :=
  { id := "sbardolini2026_table1_contradiction"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At most 1 and at least 3 students read anything"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "3 ≤ |A∩F| ≥ 1"), ("sum", "true")] }

def table1_theRestrictor : Datum :=
  { id := "sbardolini2026_table1_theRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The student with any books sold them"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(The F)A"), ("sum", "true")] }

def table1_theScope : Datum :=
  { id := "sbardolini2026_table1_theScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The student sold any books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(The A)F"), ("sum", "true")] }

def table1_thePlRestrictor : Datum :=
  { id := "sbardolini2026_table1_thePlRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The students with any books sold them"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(The Fs)A"), ("sum", "false")] }

def table1_thePlScope : Datum :=
  { id := "sbardolini2026_table1_thePlScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The students sold any books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(The As)F"), ("sum", "true")] }

def table1_bothRestrictor : Datum :=
  { id := "sbardolini2026_table1_bothRestrictor"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both students with any books sold them"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Both Fs)A"), ("sum", "true")] }

def table1_bothScope : Datum :=
  { id := "sbardolini2026_table1_bothScope"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both students sold any books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "(Both As)F"), ("sum", "true")] }

def table1_only : Datum :=
  { id := "sbardolini2026_table1_only"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only Mary sold any books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "Only x F"), ("sum", "false")] }

def table1_cleft : Datum :=
  { id := "sbardolini2026_table1_cleft"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is Mary who sold any books"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("environment", "It is x who F"), ("sum", "true")] }

def table1_sorry : Datum :=
  { id := "sbardolini2026_table1_sorry"
    source := ⟨"sbardolini-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is sorry that Mary sold any books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "x is sorry that F"), ("sum", "false")] }

def all : List Datum := [table1_episodic, table1_negation, table1_everyScope, table1_everyRestrictor, table1_someScope, table1_someRestrictor, table1_mostScope, table1_mostRestrictor, table1_antecedent, table1_consequent, table1_question, table1_imperative, table1_possibility, table1_necessity, table1_genericScope, table1_genericRestrictor, table1_tautology, table1_contradiction, table1_theRestrictor, table1_theScope, table1_thePlRestrictor, table1_thePlScope, table1_bothRestrictor, table1_bothScope, table1_only, table1_cleft, table1_sorry]

end Sbardolini2026.Examples
