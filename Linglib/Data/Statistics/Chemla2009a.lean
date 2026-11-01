module

public import Linglib.Data.Statistics.Schema

/-!
# Chemla2009a: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Chemla2009a.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Two inferential experiments on French sentences with a presupposition trigger (a definite
description, a factive verb or a change-of-state predicate) in the scope or the restrictor of a
quantifier, with the universal inference, that every individual of the domain satisfies the
presupposition, as the conclusion to be judged. Experiment 1 collected binary judgments about the
scope of 'each', 'no', 'less than 3', 'more than 3' and 'exactly 3' over a domain of 10 students;
Experiment 2 collected graded judgments over a domain of 20 students for more quantifiers and for
triggers in the restrictor. Per-quantifier results are printed only as bar charts (Figs. 4 and 7)
and are not recorded; the text prints the pooled acceptance rates recorded here.

## References

* [chemla-2009a]
-/

@[expose] public section

namespace Chemla2009a

open Data.Statistics

/-- A quantifier whose nuclear scope hosts the trigger in Experiment 1. -/
inductive Determiner where
  /-- each: 'each' -/
  | each
  /-- no: 'no' -/
  | no
  /-- less than 3: 'less than 3' -/
  | lessThan3
  /-- more than 3: 'more than 3' -/
  | moreThan3
  /-- exactly 3: 'exactly 3' -/
  | exactly3
  deriving DecidableEq, Repr, Fintype

/-- A group of the quantifiers whose scope hosts the trigger in Experiment 1. -/
inductive QuantifierGroup where
  /-- each, no: 'each' and 'no' -/
  | eachOrNo
  /-- less than 3, more than 3, exactly 3: the numerical quantifiers 'less than 3', 'more than 3'
  and 'exactly 3' -/
  | numeral
  deriving DecidableEq, Repr, Fintype

/-- The students in the domain of the quantifiers of Experiment 1, 'these 10 students'. (§2.1,
Fig. 2, (25)–(29); checked against the PDF text layer only.) -/
def domainSize : ℕ := 10

/-- A row of §2.3.4, p. 311: the group of quantifiers over which the results for a quantifier of
Experiment 1 are pooled. -/
structure Experiment1Group where
  /-- The group that pools its results. -/
  group : QuantifierGroup
  deriving DecidableEq, Repr

/-- The cells of §2.3.4, p. 311, by determiner; from an experiment; checked against the page
images. -/
def experiment1Groups : Determiner → Experiment1Group
  | .each => ⟨.eachOrNo⟩
  | .no => ⟨.eachOrNo⟩
  | .lessThan3 => ⟨.numeral⟩
  | .moreThan3 => ⟨.numeral⟩
  | .exactly3 => ⟨.numeral⟩

/-- A row of §2.3.4, p. 311: the acceptance rate of the universal inference from a trigger in the
scope of the quantifiers of a group in Experiment 1, pooled over the group; the difference
between the groups is significant (F(1, 29) = 53.8, p < .05). -/
structure Experiment1Universal where
  /-- The quantifiers whose scope hosts the trigger. -/
  group : QuantifierGroup
  /-- The acceptance rate of the universal inference, in percent. -/
  acceptance : Decimal
  deriving DecidableEq, Repr

/-- The 2 rows of §2.3.4, p. 311, in the paper's order; from an experiment; checked against the
page images. -/
def experiment1Universal : List Experiment1Universal :=
  [⟨.eachOrNo, ⟨87, 0⟩⟩,
   ⟨.numeral, ⟨53, 0⟩⟩]

end Chemla2009a
