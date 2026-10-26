module

public import Linglib.Data.Experiments.Schema

/-!
# MaldonadoCulbertson2022: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/MaldonadoCulbertson2022.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

Experiment 2: English-speaking participants learned an artificial pronoun system with three plural
forms for four plural person categories, first exclusive, inclusive, second and third, the inclusive
sharing its form with the first exclusive (First-inclusive), the second (Second-inclusive) or the
third person (Third-inclusive), between subjects. Accuracy in the second testing block was analysed
by logistic mixed-effects models with treatment coding, first with First-inclusive and then with
Second-inclusive as the baseline; the intercept compares the baseline's accuracy with chance.

## Raw data

* <https://osf.io/p2c4r/>: materials, data and analysis scripts of the three experiments

## References

* [maldonado-culbertson-2022]
-/

@[expose] public section

namespace MaldonadoCulbertson2022

open Data.Experiments

/-- The person whose plural form the inclusive shares. -/
inductive Condition where
  /-- First-inclusive: the inclusive shares the first person exclusive plural form -/
  | firstInclusive
  /-- Second-inclusive: the inclusive shares the second person plural form -/
  | secondInclusive
  /-- Third-inclusive: the inclusive shares the third person plural form -/
  | thirdInclusive
  deriving DecidableEq, Repr, Fintype

/-- A row of §3.3, p. 318: a coefficient of a treatment-coded model of accuracy in the second
testing block, the intercept or the difference of a condition from the baseline. -/
structure Contrast where
  /-- The baseline condition. -/
  baseline : Condition
  /-- The condition compared with the baseline, none for the intercept. -/
  condition : Option Condition
  /-- The coefficient. -/
  beta : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 5 rows of §3.3, p. 318, in the paper's order; checked against the PDF text layer only. -/
def contrasts : List Contrast :=
  [⟨.firstInclusive, none, ⟨159, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.firstInclusive, some .thirdInclusive, ⟨-183, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.firstInclusive, some .secondInclusive, ⟨-572, 3⟩, ⟨.eq, ⟨55, 3⟩⟩⟩,
   ⟨.secondInclusive, none, ⟨97, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.secondInclusive, some .thirdInclusive, ⟨-12, 1⟩, ⟨.lt, ⟨1, 3⟩⟩⟩]

end MaldonadoCulbertson2022
