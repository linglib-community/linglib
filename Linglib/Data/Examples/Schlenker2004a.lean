module

public import Linglib.Data.Examples.Schema

/-!
# `Schlenker2004a` — typed example data

Auto-generated from `Linglib/Data/Examples/Schlenker2004a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schlenker2004a.Examples`.
-/

@[expose] public section

namespace Schlenker2004a.Examples

def ex1 : Datum :=
  { id := "schlenker2004a_ex1"
    source := ⟨"schlenker-2004a", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tomorrow was Monday, Monday, the beginning of another school week!"
    glossedTokens := []
    context := "Free Indirect Discourse. Past tense `was` with future adverbial `tomorrow` — a contradiction if both anchored to the same context, but felicitous when `tomorrow` is evaluated against the character's Context of Thought (CT) and `was` against the narrator's Context of Utterance (CU). The thought is the character's; the tense morphology is the narrator's."
    judgment := .acceptable
    contrasts := []
    readings := [("FID (CT/CU split)", .acceptable), ("literal-contradiction", .ungrammatical)]
    paperFeatures := [] }

def ex2 : Datum :=
  { id := "schlenker2004a_ex2"
    source := ⟨"schlenker-2004a", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fifty eight years ago to this day, on January 22, 1944, just as the Americans are about to invade Europe, the Germans attack Vercors."
    glossedTokens := []
    context := "Historical Present. The present tense `attack` / `are about to invade` is evaluated against the Context of Utterance (CU), whose time is set exactly fifty eight years before that of the Context of Thought (CT); the adverbial `fifty eight years ago` is evaluated against the CT, which is the actual context. Evaluated against the same context the sentence would be contradictory; with the split, it yields the impression that the speaker is directly witnessing the scene."
    judgment := .acceptable
    contrasts := []
    readings := [("HP (CT/CU split, CU shifted back 58y)", .acceptable), ("literal-contradiction", .ungrammatical)]
    paperFeatures := [] }

def all : List Datum := [ex1, ex2]

end Schlenker2004a.Examples
