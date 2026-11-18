module

public import Linglib.Data.Examples.Schema

/-!
# `Khoo2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Khoo2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Khoo2015.Examples`.
-/

@[expose] public section

namespace Khoo2015.Examples

def control : Datum :=
  { id := "khoo2015_control"
    source := ⟨"khoo-2015", "Section II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jim is at home right now."
    glossedTokens := []
    context := "A non-modal assertion in the control vignette; participants rated on a 7-point scale either whether what the speaker said is false or whether they would respond 'No, ...'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def modal : Datum :=
  { id := "khoo2015_modal"
    source := ⟨"khoo-2015", "Section II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fat Tony might be dead."
    glossedTokens := []
    context := "Smith, one of the experts who examined the planted evidence of Fat Tony's murder, asserts the epistemic might-claim; participants, told they are also on the case and know that Fat Tony faked his death, rated on a 7-point scale either whether what Smith said is false or whether they would respond 'No, Fat Tony is alive. He faked his death.'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [control, modal]

end Khoo2015.Examples
