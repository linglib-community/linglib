module

public import Linglib.Data.Statistics.Schema

/-!
# VanTielEtAl2021: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/VanTielEtAl2021.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The quantity words of the production study and their monotonicity. In Experiment 1, participants
completed the frame '— of the circles are red' for displays of 432 red or black circles; the
seventeen words modelled are the fifteen produced 50 times or more, together with 'all' and 'none'.
In Experiment 2, 120 participants judged the validity of inferences from 'Q of the people P1' to 'Q
of the people P2' and back, for predicate pairs in which P1 entails P2. A word was coded nonmonotone
if neither inference was accepted more than half the time, and otherwise by whether it clustered
with 'all' (monotone increasing) or with 'none' (monotone decreasing); no word was coded
nonmonotone. The coding fixes whether the generalized-quantifier lexicon gives a word a lower or an
upper threshold.

## Raw data

* <https://osf.io/hsytk/>: the anonymized experimental data and the model code (DOI
  10.17605/OSF.IO/HSYTK)

## References

* [van-tiel-franke-sauerland-2021]
-/

@[expose] public section

namespace VanTielEtAl2021

open Data.Statistics

/-- A quantity word of the production study, in the order of Fig. 1A. -/
inductive Word where
  /-- none: included though rarely produced -/
  | none
  /-- hardly any: produced 50 times or more -/
  | hardlyAny
  /-- very few: produced 50 times or more -/
  | veryFew
  /-- a few: produced 50 times or more -/
  | aFew
  /-- few: produced 50 times or more -/
  | few
  /-- less than half: produced 50 times or more -/
  | lessThanHalf
  /-- some: produced 50 times or more -/
  | some
  /-- several: produced 50 times or more -/
  | several
  /-- half: produced 50 times or more -/
  | half
  /-- about half: produced 50 times or more -/
  | aboutHalf
  /-- many: produced 50 times or more -/
  | many
  /-- more than half: produced 50 times or more -/
  | moreThanHalf
  /-- a lot: produced 50 times or more -/
  | aLot
  /-- majority: produced 50 times or more, 'the majority' in the text -/
  | majority
  /-- most: produced 50 times or more -/
  | most
  /-- almost all: produced 50 times or more -/
  | almostAll
  /-- all: included though rarely produced -/
  | all
  deriving DecidableEq, Repr, Fintype

/-- The monotonicity of a quantity word in its predicate, as Experiment 2 coded it. -/
inductive Monotonicity where
  /-- monotone increasing: clustering with 'all', licensing inferences from sets to supersets -/
  | increasing
  /-- monotone decreasing: clustering with 'none', licensing inferences from sets to subsets -/
  | decreasing
  deriving DecidableEq, Repr, Fintype

/-- A row of the section GQT Semantics, p. 3: the monotonicity Experiment 2 assigned a quantity
word. -/
structure Classification where
  /-- Its monotonicity. -/
  monotonicity : Monotonicity
  deriving DecidableEq, Repr

/-- The cells of the section GQT Semantics, p. 3, by word; from an experiment; checked against
the page images. -/
def classification : Word → Classification
  | .none => ⟨.decreasing⟩
  | .hardlyAny => ⟨.decreasing⟩
  | .veryFew => ⟨.decreasing⟩
  | .aFew => ⟨.increasing⟩
  | .few => ⟨.decreasing⟩
  | .lessThanHalf => ⟨.decreasing⟩
  | .some => ⟨.increasing⟩
  | .several => ⟨.increasing⟩
  | .half => ⟨.increasing⟩
  | .aboutHalf => ⟨.increasing⟩
  | .many => ⟨.increasing⟩
  | .moreThanHalf => ⟨.increasing⟩
  | .aLot => ⟨.increasing⟩
  | .majority => ⟨.increasing⟩
  | .most => ⟨.increasing⟩
  | .almostAll => ⟨.increasing⟩
  | .all => ⟨.increasing⟩

end VanTielEtAl2021
