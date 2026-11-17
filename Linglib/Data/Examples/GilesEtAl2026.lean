module

public import Linglib.Data.Examples.Schema

/-!
# `GilesEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/GilesEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GilesEtAl2026.Examples`.
-/

@[expose] public section

namespace GilesEtAl2026.Examples

def exp1_sLowRHigh : Datum :=
  { id := "gilesetal2026_exp1_sLowRHigh"
    source := ⟨"giles-etal-2026", "Table 1 reference"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the green metal bat"
    glossedTokens := []
    context := "Three bats fall in sequence and land with a wooden or metal impact sound; an X then marks the target bat, which the speaker describes to a co-worker by colour and/or material. Material singles out the target but is at the speaker's wood/metal category boundary; colour is shared with a distractor but is consistently categorized."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("predictor", "displayType"), ("level", "sLowRHigh"), ("reference", "sLowRHigh"), ("sufficient", "low"), ("redundant", "high"), ("refSufficient", "low"), ("refRedundant", "high")] }

def exp1_baseline : Datum :=
  { id := "gilesetal2026_exp1_baseline"
    source := ⟨"giles-etal-2026", "Table 1 Baseline"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the green metal bat"
    glossedTokens := []
    context := "Three bats fall in sequence and land with a wooden or metal impact sound; an X then marks the target bat, which the speaker describes to a co-worker by colour and/or material. Both attributes are consistently categorized; material singles out the target."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("predictor", "displayType"), ("level", "baseline"), ("reference", "sLowRHigh"), ("sufficient", "high"), ("redundant", "high"), ("refSufficient", "low"), ("refRedundant", "high"), ("beta", "-94"), ("ciLower", "-120"), ("ciUpper", "-68")] }

def exp1_sHighRLow : Datum :=
  { id := "gilesetal2026_exp1_sHighRLow"
    source := ⟨"giles-etal-2026", "Table 1 S-High/R-Low"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the green metal bat"
    glossedTokens := []
    context := "Three bats fall in sequence and land with a wooden or metal impact sound; an X then marks the target bat, which the speaker describes to a co-worker by colour and/or material. Material singles out the target and is consistently categorized; the shared colour is at the speaker's category boundary."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("predictor", "displayType"), ("level", "sHighRLow"), ("reference", "sLowRHigh"), ("sufficient", "high"), ("redundant", "low"), ("refSufficient", "low"), ("refRedundant", "high"), ("beta", "-109"), ("ciLower", "-135"), ("ciUpper", "-83")] }

def exp1_colour : Datum :=
  { id := "gilesetal2026_exp1_colour"
    source := ⟨"giles-etal-2026", "Table 1 reference"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the green metal bat"
    glossedTokens := []
    context := "Three bats fall in sequence and land with a wooden or metal impact sound; an X then marks the target bat, which the speaker describes to a co-worker by colour and/or material. Material singles out the target; colour, seen, is redundant."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("predictor", "attribute"), ("level", "colour"), ("reference", "colour"), ("modality", "visual"), ("sufficient", "low"), ("redundant", "high"), ("refSufficient", "low"), ("refRedundant", "high")] }

def exp1_material : Datum :=
  { id := "gilesetal2026_exp1_material"
    source := ⟨"giles-etal-2026", "Table 1 Material Redundant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the green metal bat"
    glossedTokens := []
    context := "Three bats fall in sequence and land with a wooden or metal impact sound; an X then marks the target bat, which the speaker describes to a co-worker by colour and/or material. Colour singles out the target; material, heard, is redundant."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("predictor", "attribute"), ("level", "material"), ("reference", "colour"), ("modality", "auditory"), ("sufficient", "low"), ("redundant", "high"), ("refSufficient", "low"), ("refRedundant", "high"), ("beta", "-143"), ("ciLower", "-165"), ("ciUpper", "-120")] }

def exp2_hfColour : Datum :=
  { id := "gilesetal2026_exp2_hfColour"
    source := ⟨"giles-etal-2026", "Table 2 reference"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Click on the blue circle"
    glossedTokens := []
    context := "An array of three to sixteen shapes; the bordered target is the only shape of its kind, and zero to four of the others share its colour or stripe orientation. The speaker builds a description from adjective and noun buttons for a listener who sees the shuffled array. The shapes differ in colour: blue versus green, of matched lightness."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("predictor", "attribute"), ("level", "colour"), ("reference", "colour"), ("frequency", "high"), ("sufficient", "high"), ("redundant", "high"), ("refSufficient", "high"), ("refRedundant", "high")] }

def exp2_orientation : Datum :=
  { id := "gilesetal2026_exp2_orientation"
    source := ⟨"giles-etal-2026", "Table 2 Orientation Redundant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Click on the vertical striped circle"
    glossedTokens := []
    context := "An array of three to sixteen shapes; the bordered target is the only shape of its kind, and zero to four of the others share its colour or stripe orientation. The speaker builds a description from adjective and noun buttons for a listener who sees the shuffled array. The shapes differ in stripe orientation: vertical versus horizontal."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("predictor", "attribute"), ("level", "orientation"), ("reference", "colour"), ("sufficient", "high"), ("redundant", "high"), ("refSufficient", "high"), ("refRedundant", "high"), ("beta", "-97"), ("ciLower", "-120"), ("ciUpper", "-75")] }

def exp2_lfColour : Datum :=
  { id := "gilesetal2026_exp2_lfColour"
    source := ⟨"giles-etal-2026", "Table 2 LF Colour Terms Redundant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Click on the teal circle"
    glossedTokens := []
    context := "An array of three to sixteen shapes; the bordered target is the only shape of its kind, and zero to four of the others share its colour or stripe orientation. The speaker builds a description from adjective and noun buttons for a listener who sees the shuffled array. The shapes differ in colour, named with the low-frequency terms teal and jade."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("predictor", "frequency"), ("level", "colour"), ("reference", "colour"), ("frequency", "low"), ("sufficient", "high"), ("redundant", "high"), ("refSufficient", "high"), ("refRedundant", "high"), ("beta", "-20"), ("ciLower", "-44"), ("ciUpper", "3")] }

def all : List Datum := [exp1_sLowRHigh, exp1_baseline, exp1_sHighRLow, exp1_colour, exp1_material, exp2_hfColour, exp2_orientation, exp2_lfColour]

end GilesEtAl2026.Examples
