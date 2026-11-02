module

public import Linglib.Data.Examples.Schema

/-!
# `Kennedy1999` — typed example data

Auto-generated from `Linglib/Data/Examples/Kennedy1999.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kennedy1999.Examples`.
-/

@[expose] public section

namespace Kennedy1999.Examples

def cpa_long_short : Datum :=
  { id := "kennedy1999_cpa_long_short"
    source := ⟨"kennedy-1999", "(15), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Brothers Karamazov is longer than The Idiot is short"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def cpa_short_long : Datum :=
  { id := "kennedy1999_cpa_short_long"
    source := ⟨"kennedy-1999", "(16), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Idiot is shorter than The Brothers Karamazov is long"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def subdel_pos_pos : Datum :=
  { id := "kennedy1999_subdel_pos_pos"
    source := ⟨"kennedy-1999", "(19), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carmen's Cadillac is wider than Mike's Fiat is long"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def subdel_neg_neg : Datum :=
  { id := "kennedy1999_subdel_neg_neg"
    source := ⟨"kennedy-1999", "(20), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fortunately, the ficus was shorter than the ceiling was low, so we were able to get it into the room"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ficus_tall_high : Datum :=
  { id := "kennedy1999_ficus_tall_high"
    source := ⟨"kennedy-1999", "(61), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the ficus turned out to be taller than the ceiling was high"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ficus_tall_low : Datum :=
  { id := "kennedy1999_ficus_tall_low"
    source := ⟨"kennedy-1999", "(62), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the ficus turned out to be taller than the ceiling was low"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ficus_short_low : Datum :=
  { id := "kennedy1999_ficus_short_low"
    source := ⟨"kennedy-1999", "(63), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Luckily, the ficus turned out to be shorter than the doorway was low"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ficus_short_high : Datum :=
  { id := "kennedy1999_ficus_short_high"
    source := ⟨"kennedy-1999", "(64), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Luckily, the ficus turned out to be shorter than the doorway was high"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def incomm_tall_clever : Datum :=
  { id := "kennedy1999_incomm_tall_clever"
    source := ⟨"kennedy-1999", "(25), §3.1.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mike is taller than Carmen is clever"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def incomm_tragic_heavy : Datum :=
  { id := "kennedy1999_incomm_tragic_heavy"
    source := ⟨"kennedy-1999", "(26), §3.1.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Idiot is more tragic than my copy of The Brothers Karamazov is heavy"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def mp_cadillac : Datum :=
  { id := "kennedy1999_mp_cadillac"
    source := ⟨"kennedy-1999", "(69), §3.1.8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My Cadillac is 8 feet long"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def mp_fiat : Datum :=
  { id := "kennedy1999_mp_fiat"
    source := ⟨"kennedy-1999", "(70), §3.1.8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My Fiat is 5 feet short"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def mp_fiat_comparative : Datum :=
  { id := "kennedy1999_mp_fiat_comparative"
    source := ⟨"kennedy-1999", "(73), §3.1.8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My fiat is shorter than 8 feet"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def mp_reich : Datum :=
  { id := "kennedy1999_mp_reich"
    source := ⟨"kennedy-1999", "(79), §3.1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mr. Reich is 5 feet short"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def mp_slow : Datum :=
  { id := "kennedy1999_mp_slow"
    source := ⟨"kennedy-1999", "(80), §3.1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maureen was driving 14 mph slow"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [cpa_long_short, cpa_short_long, subdel_pos_pos, subdel_neg_neg, ficus_tall_high, ficus_tall_low, ficus_short_low, ficus_short_high, incomm_tall_clever, incomm_tragic_heavy, mp_cadillac, mp_fiat, mp_fiat_comparative, mp_reich, mp_slow]

end Kennedy1999.Examples
