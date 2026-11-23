module

public import Linglib.Data.Statistics.Schema

/-!
# Narrog2012: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Narrog2012.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The totals the book gives for the changes of modal meaning in the sample of [bybee-perkins-
pagliuca-1994], by the sides of volitivity they run between. The changes themselves are tabulated in
`Narrog2010.changes`.

## References

* [narrog-2012]
-/

@[expose] public section

namespace Narrog2012

open Data.Statistics

/-- The changes from non-volitive to volitive meaning. (section 5.2, p. 154; checked against the
page images.) -/
def nonVolitiveToVolitive : ℕ := 27

/-- The changes within non-volitive meaning. (section 5.2, p. 154; checked against the page
images.) -/
def withinNonVolitive : ℕ := 6

/-- The changes from volitive to non-volitive meaning. (section 5.2, p. 154; checked against the
page images.) -/
def volitiveToNonVolitive : ℕ := 5

/-- The changes within volitive meaning. (section 5.2, p. 154; checked against the page images.) -/
def withinVolitive : ℕ := 4

end Narrog2012
