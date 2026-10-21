module

public import Linglib.Data.Experiments.Schema

/-!
# Burnett2019: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/Burnett2019.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The (ING) rates Burnett reproduces from Labov's New York City survey: the approximate percentage of
*-in'* in casual style by social class.

## References

* [burnett-2019]
-/

@[expose] public section

namespace Burnett2019

open Data.Experiments

/-- The social classes of Table 7, from the highest to the lowest. -/
inductive SocialClass where
  /-- Upper middle class: the upper middle class -/
  | upperMiddle
  /-- Lower middle class: the lower middle class -/
  | lowerMiddle
  /-- Working class: the working class -/
  | working
  /-- Lower class: the lower class -/
  | lower
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 7, p. 439: the approximate percentage of *-in'* in casual style of a social
class in New York City. -/
structure IngCell where
  /-- The approximate percentage of *-in'*. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 7, p. 439, by socialClass; checked against the page images. -/
def ingByClass : SocialClass → IngCell
  | .upperMiddle => ⟨10⟩
  | .lowerMiddle => ⟨40⟩
  | .working => ⟨50⟩
  | .lower => ⟨80⟩

end Burnett2019
