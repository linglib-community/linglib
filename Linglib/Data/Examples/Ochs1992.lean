module

public import Linglib.Data.Examples.Schema

/-!
# `Ochs1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Ochs1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ochs1992.Examples`.
-/

@[expose] public section

namespace Ochs1992.Examples

def ze : Datum :=
  { id := "ochs1992_ze"
    source := ⟨"ochs-1992", "Figure 14.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1643"
    primaryText := "ze"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directIndex", "coarse intensity"), ("indirectIndex", "male voice")] }

def wa : Datum :=
  { id := "ochs1992_wa"
    source := ⟨"ochs-1992", "Figure 14.1"⟩
    reportedIn := none
    method := some .description
    language := "nucl1643"
    primaryText := "wa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("directIndex", "delicate intensity"), ("indirectIndex", "female voice")] }

def tummy : Datum :=
  { id := "ochs1992_tummy"
    source := ⟨"ochs-1992", "p. 349"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "tummy"
    glossedTokens := []
    context := "Baby Talk register, phonological simplification, against 'stomach'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Extensive simplification"), ("community", "Mainstream American")] }

def what : Datum :=
  { id := "ochs1992_what"
    source := ⟨"ochs-1992", "p. 351"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "What?"
    glossedTokens := []
    context := "Response to a child's unintelligible utterance, indicating unintelligibility."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Display minimal grasp")] }

def dontUnderstand : Datum :=
  { id := "ochs1992_dontUnderstand"
    source := ⟨"ochs-1992", "p. 351"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "I don't understand"
    glossedTokens := []
    context := "Response to a child's unintelligible utterance, indicating unintelligibility."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Display minimal grasp")] }

def huh : Datum :=
  { id := "ochs1992_huh"
    source := ⟨"ochs-1992", "p. 351"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "Huh?"
    glossedTokens := []
    context := "Response to a child's unintelligible utterance, indicating unintelligibility."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Display minimal grasp")] }

def good : Datum :=
  { id := "ochs1992_good"
    source := ⟨"ochs-1992", "p. 353"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "Good!"
    glossedTokens := []
    context := "A praise directed at a child for a jointly accomplished activity, with no mention of the mother's role."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Unidirectional"), ("community", "Mainstream American")] }

def castle : Datum :=
  { id := "ochs1992_castle"
    source := ⟨"ochs-1992", "p. 353"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "Look at the beautiful castle you made!"
    glossedTokens := []
    context := "A praise directed at a child for a jointly accomplished activity, with no mention of the mother's role."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Unidirectional"), ("community", "Mainstream American")] }

def maaloo : Datum :=
  { id := "ochs1992_maaloo"
    source := ⟨"ochs-1992", "p. 354"⟩
    reportedIn := none
    method := some .corpus
    language := "samo1305"
    primaryText := "Maaloo!"
    glossedTokens := []
    context := "A praise, to be answered by a second maaloo directed at its producer."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "Bidirectional"), ("community", "Samoan")] }

def all : List Datum := [ze, wa, tummy, what, dontUnderstand, huh, good, castle, maaloo]

end Ochs1992.Examples
