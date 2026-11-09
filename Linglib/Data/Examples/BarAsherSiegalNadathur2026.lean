module

public import Linglib.Data.Examples.Schema

/-!
# `BarAsherSiegalNadathur2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BarAsherSiegalNadathur2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarAsherSiegalNadathur2026.Examples`.
-/

@[expose] public section

namespace BarAsherSiegalNadathur2026.Examples

def basn2026_40_switchedOn : Datum :=
  { id := "basn2026_40_switchedOn"
    source := ⟨"bar-asher-siegal-nadathur-2026", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nur is opening the door."
    glossedTokens := []
    context := "The door is known to be unlocked, and Nur has just flipped the switch in the electrical cabinet, allowing electricity to flow, but has not yet pressed the button that opens the door."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "open the door"), ("aspect", "progressive")] }

def basn2026_40_realistic : Datum :=
  { id := "basn2026_40_realistic"
    source := ⟨"bar-asher-siegal-nadathur-2026", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nur is opening the door."
    glossedTokens := []
    context := "The door is known to be unlocked and the electricity is flowing, and Nur has neither turned the door handle nor pressed the button, so the door is closed."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "open the door"), ("aspect", "progressive")] }

def basn2026_43a_handle : Datum :=
  { id := "basn2026_43a_handle"
    source := ⟨"bar-asher-siegal-nadathur-2026", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nur is opening the door."
    glossedTokens := []
    context := "The status of the lock is unknown, and Nur has turned the door handle."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "open the door"), ("aspect", "progressive")] }

def basn2026_43a_button : Datum :=
  { id := "basn2026_43a_button"
    source := ⟨"bar-asher-siegal-nadathur-2026", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nur is opening the door."
    glossedTokens := []
    context := "The status of the lock is unknown, and Nur has pressed the door-open button."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "open the door"), ("aspect", "progressive")] }

def basn2026_43b : Datum :=
  { id := "basn2026_43b"
    source := ⟨"bar-asher-siegal-nadathur-2026", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nur is trying to open the door."
    glossedTokens := []
    context := "The status of the lock is unknown, and Nur has either turned the door handle or pressed the door-open button."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "try to open the door"), ("aspect", "progressive")] }

def all : List Datum := [basn2026_40_switchedOn, basn2026_40_realistic, basn2026_43a_handle, basn2026_43a_button, basn2026_43b]

end BarAsherSiegalNadathur2026.Examples
