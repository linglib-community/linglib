module

public import Linglib.Data.Statistics.Schema

/-!
# Flemming2021: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Flemming2021.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The observed probabilities of pronouncing schwa in the eight French contexts of (19), from the
experiment of Smith and Pater (2020), with the probabilities fitted by the four stochastic Harmonic
Grammars and their deviances (Table 2). The text gives the deviances of MaxEnt and censored NHG as
12.8 and 14.6 in that order; the table, and the footnote on censored NHG, give 14.6 to MaxEnt and
12.8 to censored NHG.

## References

* [flemming-2021]
-/

@[expose] public section

namespace Flemming2021

open Data.Statistics

/-- Whether the schwa site is clitic-final, with an underlying schwa, or word-final, with none. -/
inductive Underlying where
  /-- /∅/: word-final, no underlying schwa -/
  | zero
  /-- /ə/: clitic-final, an underlying schwa -/
  | schwa
  deriving DecidableEq, Repr, Fintype

/-- How many consonants precede the schwa site. -/
inductive Onset where
  /-- C: one consonant -/
  | c
  /-- CC: two consonants -/
  | cc
  deriving DecidableEq, Repr, Fintype

/-- The following word. -/
inductive Following where
  /-- _σσ́: a disyllable, stressed on its second syllable -/
  | disyllable
  /-- _σ́: a stressed monosyllable -/
  | monosyllable
  deriving DecidableEq, Repr, Fintype

/-- The stochastic Harmonic Grammars compared. -/
inductive Model where
  /-- MaxEnt: Maximum Entropy -/
  | maxEnt
  /-- Normal MaxEnt: MaxEnt with normal noise -/
  | normalMaxEnt
  /-- NHG: Noisy Harmonic Grammar -/
  | nhg
  /-- Censored NHG: Noisy Harmonic Grammar with censored noise -/
  | censoredNhg
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 2, p. 23: the observed probability of pronouncing schwa in a context and the
probabilities the grammars fit. -/
structure SchwaRate where
  /-- The observed probability, Pə. -/
  observed : Decimal
  /-- The probability fitted by MaxEnt. -/
  maxEnt : Decimal
  /-- The probability fitted by normal MaxEnt. -/
  normalMaxEnt : Decimal
  /-- The probability fitted by NHG. -/
  nhg : Decimal
  /-- The probability fitted by censored NHG. -/
  censoredNhg : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 23, by underlying and onset and following; from an experiment;
checked against the page images. -/
def schwaRates : Underlying → Onset → Following → SchwaRate
  | .zero, .c, .disyllable => ⟨⟨9, 2⟩, ⟨11, 2⟩, ⟨12, 2⟩, ⟨10, 2⟩, ⟨10, 2⟩⟩
  | .zero, .c, .monosyllable => ⟨⟨12, 2⟩, ⟨17, 2⟩, ⟨18, 2⟩, ⟨21, 2⟩, ⟨17, 2⟩⟩
  | .zero, .cc, .disyllable => ⟨⟨68, 2⟩, ⟨68, 2⟩, ⟨67, 2⟩, ⟨67, 2⟩, ⟨70, 2⟩⟩
  | .zero, .cc, .monosyllable => ⟨⟨83, 2⟩, ⟨78, 2⟩, ⟨76, 2⟩, ⟨75, 2⟩, ⟨77, 2⟩⟩
  | .schwa, .c, .disyllable => ⟨⟨56, 2⟩, ⟨52, 2⟩, ⟨50, 2⟩, ⟨50, 2⟩, ⟨54, 2⟩⟩
  | .schwa, .c, .monosyllable => ⟨⟨65, 2⟩, ⟨63, 2⟩, ⟨61, 2⟩, ⟨61, 2⟩, ⟨62, 2⟩⟩
  | .schwa, .cc, .disyllable => ⟨⟨91, 2⟩, ⟨95, 2⟩, ⟨95, 2⟩, ⟨96, 2⟩, ⟨95, 2⟩⟩
  | .schwa, .cc, .monosyllable => ⟨⟨94, 2⟩, ⟨97, 2⟩, ⟨97, 2⟩, ⟨96, 2⟩, ⟨96, 2⟩⟩

/-- A row of Table 2, p. 23: the deviance of a grammar's fit, lower for a better fit. -/
structure Fit where
  /-- The deviance. -/
  deviance : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 23, by model; fitted or simulated by a model; checked against the
page images. -/
def deviances : Model → Fit
  | .maxEnt => ⟨⟨146, 1⟩⟩
  | .normalMaxEnt => ⟨⟨217, 1⟩⟩
  | .nhg => ⟨⟨260, 1⟩⟩
  | .censoredNhg => ⟨⟨128, 1⟩⟩

end Flemming2021
