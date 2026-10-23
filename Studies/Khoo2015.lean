module

public import Linglib.Data.Examples.Khoo2015
public import Linglib.Data.Experiments.Khoo2015
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Khoo (2015): Modal Disagreements

This file records the experiment of [khoo-2015] on disagreements over epistemic modal claims.
Participants read a control vignette with a non-modal assertion and a modal vignette in which
Smith, having examined evidence consistent with Fat Tony's death, says *Fat Tony might be dead*
while Beth knows him to be alive, and rated on a seven-point scale either whether what the
speaker said is false or whether they would respond *No, ...* (section II;
`Data/Examples/Khoo2015`). The Difference Observation is that the modal claim is rejected
readily yet not judged false, a dissociation the control assertion lacks
(`difference_observation`): speakers reject the might-claim without judging it false.

## Implementation notes

The cell means and standard deviations of footnote 13 are `Data/Experiments/Khoo2015`, which
the released survey reproduces; "readily" and "not" are read against the scale's midpoint. The
paper's account of the observation is not formalized.

## References

* [khoo-2015]
-/

@[expose] public section

namespace Khoo2015

/-- The mean rating of a vignette under a question. -/
def mean (s : Sentence) (r : Response) : ℚ := (ratings s r).mean.toRat

theorem difference_observation :
    ((midpoint : ℚ) < mean .modal .rejection ∧ mean .modal .judgedFalse < midpoint) ∧
      mean .control .rejection ≤ mean .control .judgedFalse := by
  decide +kernel

end Khoo2015
