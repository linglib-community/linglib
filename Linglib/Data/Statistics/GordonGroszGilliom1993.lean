module

public import Linglib.Data.Statistics.Schema

/-!
# GordonGroszGilliom1993: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/GordonGroszGilliom1993.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Five self-paced reading experiments that vary whether an entity of a short passage is realized by a
pronoun or by a repeated name. Experiment 1 measures the total reading time of the passage;
Experiments 2 to 5 measure the reading time of a critical sentence. The tests that bear on the
repeated-name penalty are given as printed, by subjects (F1, t1) and by passages (F2, t2); a
statistic printed only as less than 1 has no value and no p-value.

## References

* [gordon-grosz-gilliom-1993]
-/

@[expose] public section

namespace GordonGroszGilliom1993

open Data.Statistics

/-- The experiment, the two versions of Experiment 2 apart. -/
inductive Experiment where
  /-- Experiment 1: Bruno and Tommy: the subject and an object throughout -/
  | exp1
  /-- Experiment 2A: Lisa and Joe: the established center in a fronted phrase -/
  | exp2A
  /-- Experiment 2B: Elizabeth and Tom: the established center in a fronted phrase -/
  | exp2B
  /-- Experiment 3: Susan and Fred: a fronted entity and the subject -/
  | exp3
  /-- Experiment 4: George and Debbie: continue against shift -/
  | exp4
  /-- Experiment 5: Susan and Fred: continue against shift after a retain -/
  | exp5
  deriving DecidableEq, Repr, Fintype

/-- The reading time a test analyzes. -/
inductive Measure where
  /-- passage: the total reading time of the passage -/
  | passage
  /-- critical sentence: the reading time of the critical sentence -/
  | critical
  deriving DecidableEq, Repr, Fintype

/-- The effect a test assesses, as the paper names it. -/
inductive Effect where
  /-- name-name vs. pro-name and pro-pro: the planned comparison of the name-name condition with
  the average of the other two -/
  | nameNameVsOthers
  /-- pro-name vs. pro-pro: the comparison of the pro-name and pro-pro conditions -/
  | proNameVsProPro
  /-- pronominalizing Entity1: a pronoun or a repeated name for the first-named entity -/
  | entity1
  /-- pronominalizing Entity2: a pronoun or a repeated name for the second-named entity -/
  | entity2
  /-- number of pronouns: the three conditions pro-pro, pro-name and name-name -/
  | numberOfPronouns
  /-- subject: a pronoun or a repeated name for the subject of the critical sentence -/
  | subject
  /-- fronted entity: a pronoun or a repeated name for the entity of the fronted phrase -/
  | fronted
  /-- pronominalization: a pronoun or a repeated name for the subject of the critical sentence -/
  | pronominalization
  /-- continue-shift: whether the subject of the critical sentence continues or shifts the center -/
  | continueShift
  /-- interaction: the interaction of the two manipulations -/
  | interaction
  /-- repeated-name penalty, continue: the repeated-name penalty in the continue condition -/
  | penaltyContinue
  /-- repeated-name penalty, shift: the repeated-name penalty in the shift condition -/
  | penaltyShift
  deriving DecidableEq, Repr, Fintype

/-- The test statistic. -/
inductive Statistic where
  /-- F: an analysis of variance -/
  | fTest
  /-- t: a t test -/
  | tTest
  deriving DecidableEq, Repr, Fintype

/-- A row of pp. 319, 326-327, 331-332, 334-335, 338: a test of reading time that bears on the
repeated-name penalty, by subjects and by passages. -/
structure Test where
  /-- The experiment. -/
  experiment : Experiment
  /-- The reading time analyzed. -/
  measure : Measure
  /-- The effect tested. -/
  effect : Effect
  /-- The test statistic. -/
  statistic : Statistic
  /-- The statistic by subjects, none where printed as less than 1. -/
  bySubjects : Option Decimal
  /-- Its p-value, none where none is printed. -/
  pSubjects : Option PValue
  /-- The statistic by passages, none where printed as less than 1. -/
  byPassages : Option Decimal
  /-- Its p-value, none where none is printed. -/
  pPassages : Option PValue
  deriving DecidableEq, Repr

/-- The 17 rows of pp. 319, 326-327, 331-332, 334-335, 338, in the paper's order; from an
experiment; checked against the page images. -/
def tests : List Test :=
  [⟨.exp1,  -- p. 319: F1(1, 11), F2(1, 11); 24 passages give the by-passages test 23 error degrees of freedom, as in F2(2, 46) for the effect of condition
     .passage,
     .nameNameVsOthers,
     .fTest,
     some ⟨243, 1⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨260, 1⟩,
     some ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp1,  -- p. 319: F1(1, 11) < 1, F2(1, 11) < 1
     .passage,
     .proNameVsProPro,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp2A,  -- p. 326: F1(1, 15) < 1, F2(1, 23) < 1
     .critical,
     .entity1,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp2A,  -- p. 326: F1(1, 15), F2(1, 23)
     .critical,
     .entity2,
     .fTest,
     some ⟨11, 1⟩,
     some ⟨.gt, ⟨20, 2⟩⟩,
     some ⟨14, 1⟩,
     some ⟨.gt, ⟨20, 2⟩⟩⟩,
   ⟨.exp2A,  -- p. 326: F1(1, 15) < 1, F2(1, 23) < 1
     .critical,
     .interaction,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp2B,  -- p. 327: F1(2, 34) < 1, F2(2, 46) < 1
     .critical,
     .numberOfPronouns,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp3,  -- p. 331: F1(1, 15), F2(1, 39)
     .critical,
     .subject,
     .fTest,
     some ⟨52, 1⟩,
     some ⟨.lt, ⟨5, 2⟩⟩,
     some ⟨133, 1⟩,
     some ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp3,  -- pp. 331-332: F1(1, 15) < 1, F2(1, 39) < 1
     .critical,
     .fronted,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp3,  -- p. 332: F1(1, 15) < 1, F2(1, 39) < 1
     .critical,
     .interaction,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp4,  -- p. 334: F1(1, 23), F2(1, 39)
     .critical,
     .pronominalization,
     .fTest,
     some ⟨227, 1⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨93, 1⟩,
     some ⟨.lt, ⟨5, 3⟩⟩⟩,
   ⟨.exp4,  -- p. 334: F1(1, 23) < 1, F2(1, 39) < 1
     .critical,
     .continueShift,
     .fTest,
     none,
     none,
     none,
     none⟩,
   ⟨.exp4,  -- p. 334: F1(1, 23), F2(1, 39)
     .critical,
     .interaction,
     .fTest,
     some ⟨65, 1⟩,
     some ⟨.lt, ⟨25, 3⟩⟩,
     some ⟨57, 1⟩,
     some ⟨.lt, ⟨25, 3⟩⟩⟩,
   ⟨.exp4,  -- p. 335: t1(23), t2(39); a penalty of 183 ms
     .critical,
     .penaltyContinue,
     .tTest,
     some ⟨47, 1⟩,
     some ⟨.lt, ⟨1, 3⟩⟩,
     some ⟨42, 1⟩,
     some ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp4,  -- p. 335: t1(23), t2(39); a penalty of 42 ms
     .critical,
     .penaltyShift,
     .tTest,
     some ⟨11, 1⟩,
     some ⟨.gt, ⟨20, 2⟩⟩,
     some ⟨10, 1⟩,
     some ⟨.gt, ⟨20, 2⟩⟩⟩,
   ⟨.exp5,  -- p. 338: F1(1, 23), F2(1, 39)
     .critical,
     .pronominalization,
     .fTest,
     some ⟨51, 1⟩,
     some ⟨.lt, ⟨5, 2⟩⟩,
     some ⟨43, 1⟩,
     some ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp5,  -- p. 338: F1(1, 23), F2(1, 39)
     .critical,
     .continueShift,
     .fTest,
     some ⟨19, 1⟩,
     some ⟨.gt, ⟨15, 2⟩⟩,
     some ⟨37, 1⟩,
     some ⟨.lt, ⟨10, 2⟩⟩⟩,
   ⟨.exp5,  -- p. 338: F1(1, 23) < 1, F2(1, 39) < 1
     .critical,
     .interaction,
     .fTest,
     none,
     none,
     none,
     none⟩]

end GordonGroszGilliom1993
