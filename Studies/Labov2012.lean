module

public import Linglib.Data.Experiments.Labov2012
public import Mathlib.Order.Monotone.Defs

/-!
# Labov (2012): Dialect Diversity in America

Labov reads a shared norm for the variable (ING) off its style shifting: in the New York survey
every social class uses less *-in'* as the attention paid to speech rises, and "we are all
constrained by this social consensus, even presidents". President Obama's rate of *-in'* falls
from 72% at a barbecue through 33% answering questions at the ceremony that followed to 3% in a
scripted convention speech, strictly with the formality of the occasion (`ingByStyle_strictAnti`).

## Implementation notes

Figure 4 superimposes Sarah Palin's careful and formal rates on the President's, in agreement
with them, but the text prints no numbers for her, so her rates are not recorded.

## References

* [labov-2012]
-/

@[expose] public section

namespace Labov2012

/-- Styles are ordered by formality, `casual < careful < formal`. -/
instance : LinearOrder Style := LinearOrder.lift' Style.ctorIdx (by decide)

/-- The President's rate of *-in'* falls strictly with the formality of the style. -/
theorem ingByStyle_strictAnti : StrictAnti fun s ↦ (ingByStyle s).percent := by decide

end Labov2012
