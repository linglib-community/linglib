module

public import Linglib.Data.Statistics.Schema

/-!
# Cummins2015: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Cummins2015.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The corrections of Cummins's Experiment 2: how often a false or underinformative description of
boxes holding *n* or *n* + 1 items was corrected, and how many corrections took each of the two
forms the constraint model predicts.

## References

* [cummins-2015]
-/

@[expose] public section

namespace Cummins2015

open Data.Statistics

/-- The false and underinformative descriptions of Experiment 2. -/
inductive Prompt where
  /-- more than n: *more than n*, false of the display -/
  | moreThan
  /-- fewer than n + 1: *fewer than n + 1*, false of the display -/
  | fewerThan
  /-- at least n - 1: *at least n − 1*, true and underinformative -/
  | atLeast
  /-- at most n + 2: *at most n + 2*, true and underinformative -/
  | atMost
  deriving DecidableEq, Repr, Fintype

/-- A row of §3.3.2.1, Results, p. 78: the corrections participants issued to a description. -/
structure CorrectionCount where
  /-- The trials presenting the description. -/
  trials : ℕ
  /-- The trials on which it was corrected. -/
  corrected : ℕ
  /-- The corrections with the maximally informative superlative on the same side, *at least n*
  or *at most n + 1*. -/
  superlative : ℕ
  /-- The corrections with the maximally informative comparative on the same side, *more than n −
  1* or *fewer than n + 2*. -/
  comparative : ℕ
  deriving DecidableEq, Repr

/-- The cells of §3.3.2.1, Results, p. 78, by prompt; from an experiment; checked against the
page images. -/
def corrections : Prompt → CorrectionCount
  | .moreThan => ⟨84, 81, 42, 32⟩
  | .fewerThan => ⟨84, 84, 17, 44⟩  -- the superlative corrections are printed as *at most n*
  | .atLeast => ⟨84, 13, 13, 0⟩  -- every correction is reported as *at least n*
  | .atMost => ⟨84, 59, 49, 4⟩

end Cummins2015
