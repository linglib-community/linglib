module

public import Linglib.Data.Statistics.Schema

/-!
# EngelhardtEtAl2006: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/EngelhardtEtAl2006.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Three experiments on the Gricean maxim of Quantity with displays of an apple on a towel, an empty
towel, an empty box and either a frog or a second apple. In Experiment 1 speakers instruct a
confederate to move the apple, and the first instruction of each trial is coded for a modified
target; in Experiments 2 and 2b listeners rate instructions from 1 (incorrect) to 5 (perfect),
Experiment 2b replacing *put the apple on the towel* by *put the apple on the other towel*;
Experiment 3 records eye movements, not tabled here. Tests are printed by subjects (F1), by items
(F2) and as min F'; their degrees of freedom are in the notes. Pairwise comparisons of condition
means are read against the 95% confidence interval of their difference. The speech files were
offered at a lab address that no longer resolves; no data were released.

## References

* [engelhardt-etal-2006]
-/

@[expose] public section

namespace EngelhardtEtAl2006

open Data.Statistics

/-- The experiment. -/
inductive Experiment where
  /-- Experiment 1: production -/
  | exp1
  /-- Experiment 2: listener judgments of the instructions of Table 1 -/
  | exp2
  /-- Experiment 2b: Experiment 2 with *put the apple on the other towel* for *put the apple on
  the towel* -/
  | exp2b
  deriving DecidableEq, Repr, Fintype

/-- The visual context, by the number of objects of the target's kind. -/
inductive ContextType where
  /-- One-referent: one apple and a frog -/
  | oneReferent
  /-- Two-referent: two apples -/
  | twoReferent
  deriving DecidableEq, Repr, Fintype

/-- Whether the target carries the prepositional-phrase modifier. -/
inductive InstructionType where
  /-- Bare target: *the apple* -/
  | bare
  /-- Modified target: *the apple on the towel* -/
  | modified
  deriving DecidableEq, Repr, Fintype

/-- Whether the destination is of the kind of the target's current location. -/
inductive LocationType where
  /-- Matching location: towel to towel -/
  | matching
  /-- Different location: towel to box -/
  | different
  deriving DecidableEq, Repr, Fintype

/-- The effect a test bears on. -/
inductive Effect where
  /-- Context type: the effect of the context type -/
  | context
  /-- Above zero: a rate above zero, by a one-sample test -/
  | aboveZero
  /-- Instruction type: the main effect of the instruction type -/
  | instruction
  deriving DecidableEq, Repr, Fintype

/-- A row of p. 560: the percentage of first instructions with a modified target, by context
type. -/
structure Production where
  /-- The percentage of first instructions with a modified target. -/
  modifiedTarget : Decimal
  deriving DecidableEq, Repr

/-- The cells of p. 560, by context; from an experiment; checked against the page images. -/
def production : ContextType → Production
  | .oneReferent => ⟨⟨30, 0⟩⟩
  | .twoReferent => ⟨⟨98, 0⟩⟩

/-- A row of pp. 562-563: the mean rating of each instruction of Table 1 in Experiment 2's one-
referent context. -/
structure Exp2Rating where
  /-- The mean rating on the scale from 1 to 5. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of pp. 562-563, by instruction and location; from an experiment; checked against
the page images. -/
def exp2Ratings : InstructionType → LocationType → Exp2Rating
  | .bare, .matching => ⟨⟨312, 2⟩⟩
  | .bare, .different => ⟨⟨491, 2⟩⟩
  | .modified, .matching => ⟨⟨474, 2⟩⟩
  | .modified, .different => ⟨⟨43, 1⟩⟩

/-- A row of p. 564: the mean rating of each instruction in Experiment 2b's one-referent context. -/
structure Exp2bRating where
  /-- The mean rating on the scale from 1 to 5. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of p. 564, by instruction and location; from an experiment; checked against the
page images. -/
def exp2bRatings : InstructionType → LocationType → Exp2bRating
  | .bare, .matching => ⟨⟨469, 2⟩⟩  -- p. 564: put the apple on the other towel
  | .bare, .different => ⟨⟨464, 2⟩⟩
  | .modified, .matching => ⟨⟨441, 2⟩⟩  -- p. 564: 4.41 vs. 4.21; matching is higher in Fig. 4C
  | .modified, .different => ⟨⟨421, 2⟩⟩

/-- A row of p. 563: the mean rating of each instruction type in Experiment 2's two-referent
context, over location types. -/
structure Exp2TwoReferentRating where
  /-- The mean rating on the scale from 1 to 5. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of p. 563, by instruction; from an experiment; checked against the page images. -/
def exp2TwoReferentRatings : InstructionType → Exp2TwoReferentRating
  | .bare => ⟨⟨28, 1⟩⟩
  | .modified => ⟨⟨435, 2⟩⟩

/-- A row of pp. 562-563: a pairwise comparison of instructions in Experiment 2's one-referent
context whose difference the paper reports exceeding the 95% confidence interval, the higher-
rated instruction first. -/
structure Comparison where
  /-- The instruction type of the higher-rated instruction. -/
  higherInstruction : InstructionType
  /-- Its location type. -/
  higherLocation : LocationType
  /-- The instruction type of the lower-rated instruction. -/
  lowerInstruction : InstructionType
  /-- Its location type. -/
  lowerLocation : LocationType
  /-- The 95% confidence interval for the difference between the means. -/
  interval : Decimal
  deriving DecidableEq, Repr

/-- The 4 rows of pp. 562-563, in the paper's order; from an experiment; checked against the page
images. -/
def comparisons : List Comparison :=
  [⟨.bare, .different, .bare, .matching, ⟨31, 2⟩⟩,
   ⟨.modified, .matching, .modified, .different, ⟨30, 2⟩⟩,
   ⟨.modified, .matching, .bare, .matching, ⟨27, 2⟩⟩,
   ⟨.bare, .different, .modified, .different, ⟨38, 2⟩⟩]

/-- A row of pp. 560, 564, Table 4: a test of production in Experiment 1 or of ratings in
Experiments 2 and 2b, by subjects, by items and as min F'. -/
structure Test where
  /-- The experiment. -/
  experiment : Experiment
  /-- The effect tested. -/
  effect : Effect
  /-- The context type the test is restricted to, if any. -/
  context : Option ContextType
  /-- F by subjects, none where the paper prints no test. -/
  f1 : Option Decimal
  /-- Its p-value. -/
  p1 : Option PValue
  /-- F by items. -/
  f2 : Option Decimal
  /-- Its p-value. -/
  p2 : Option PValue
  /-- Min F'. -/
  minF : Option Decimal
  /-- Its p-value. -/
  pMin : Option PValue
  deriving DecidableEq, Repr

/-- The 6 rows of pp. 560, 564, Table 4, in the paper's order; from an experiment; checked
against the page images. -/
def tests : List Test :=
  [⟨.exp1,  -- p. 560: 98% vs. 30%; F1(1, 9), F2(1, 5), min F'(1, 14)
     .context,
     none,
     some ⟨10808, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨25783, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨7615, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp1,  -- p. 560: one-sample t test against 0, as F; F1(1, 9), F2(1, 5), min F'(1, 11)
     .aboveZero,
     some .oneReferent,
     some ⟨110, 1⟩,
     some ⟨.lt, ⟨1, 2⟩⟩,
     some ⟨10296, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨994, 2⟩,
     some ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.exp2,  -- Table 4: F1(1, 21), F2(1, 5), min F'(1, 24)
     .instruction,
     some .oneReferent,
     some ⟨1125, 2⟩,
     some ⟨.lt, ⟨1, 2⟩⟩,
     some ⟨2528, 2⟩,
     some ⟨.lt, ⟨1, 2⟩⟩,
     some ⟨779, 2⟩,
     some ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2,  -- Table 4: F1(1, 21), F2(1, 5), min F'(1, 16)
     .instruction,
     some .twoReferent,
     some ⟨7259, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨7442, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨3674, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2b,  -- p. 564: not statistically significant, no test printed
     .instruction,
     some .oneReferent,
     none,
     none,
     none,
     none,
     none,
     none⟩,
   ⟨.exp2b,  -- p. 564: F1(1, 21), F2(1, 5), min F'(1, 11)
     .instruction,
     some .twoReferent,
     some ⟨2373, 2⟩,
     some ⟨.lt, ⟨1, 2⟩⟩,
     some ⟨1233, 2⟩,
     some ⟨.lt, ⟨5, 2⟩⟩,
     some ⟨811, 2⟩,
     some ⟨.lt, ⟨5, 2⟩⟩⟩]

end EngelhardtEtAl2006
