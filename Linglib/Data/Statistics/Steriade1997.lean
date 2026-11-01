module

public import Linglib.Data.Statistics.Schema

/-!
# Steriade1997: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Steriade1997.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The survey S1 of (14): 22 speakers read aloud lists of -able adjectives, among them those on remedy
and parody, treating them as nonce forms. The table counts the responses with each stress pattern
relative to the verb; some speakers gave more than one pronunciation, so the remedy responses number
24.

## References

* [steriade-1997]
-/

@[expose] public section

namespace Steriade1997

open Data.Statistics

/-- The verb the -able adjective is formed on. -/
inductive Base where
  /-- rémedy: remedy, whose paradigm lists the amphibrachic stem of remedial -/
  | remedy
  /-- párody: parody, whose paradigm lists only the dactylic verb -/
  | parody
  deriving DecidableEq, Repr, Fintype

/-- The stress pattern of the stem of the -able form, relative to the verb. -/
inductive Pattern where
  /-- σ́σσ: same as the verb, stress on the first syllable -/
  | sameAsBase
  /-- σσ́σ: stress shifted to the second syllable -/
  | second
  /-- σ̀σσ́: stress on the first and third syllables -/
  | firstThird
  deriving DecidableEq, Repr, Fintype

/-- The number of speakers surveyed in 1996-1997. ((14); checked against the page images.) -/
def speakers : ℕ := 22

/-- A row of (14): the responses with a stress pattern, of all responses to the -able form on a
verb. -/
structure Responses where
  /-- The responses with the pattern. -/
  count : ℕ
  /-- All responses to the verb's -able form. -/
  total : ℕ
  deriving DecidableEq, Repr

/-- The cells of (14), by base and pattern; from an experiment; checked against the page images. -/
def responses : Base → Pattern → Responses
  | .remedy, .sameAsBase =>  -- (23) prints 20/4 for remediable, four responses unchanged against the three here.
    ⟨3,
     24⟩
  | .remedy, .second => ⟨20, 24⟩  -- Also the stress Webster's Third gives.
  | .remedy, .firstThird => ⟨1, 24⟩
  | .parody, .sameAsBase => ⟨21, 22⟩
  | .parody, .second => ⟨0, 22⟩
  | .parody, .firstThird => ⟨1, 22⟩

end Steriade1997
