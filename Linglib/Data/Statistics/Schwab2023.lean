module

public import Linglib.Data.Statistics.Schema

/-!
# Schwab2023: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Schwab2023.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Two speeded acceptability experiments on the German NPIs jemals 'ever' and so recht 'really', each
crossing the NPI with the position of a negative quantifier: in the matrix clause, inside a relative
clause, or absent. For each experiment the paper reports Bayes factors, from bridge sampling,
comparing a model with the NPI illusion of each NPI, or with the interaction of the two illusions,
to a model without it, and reads each as evidence of a stated strength. The posterior estimates are
not recorded; Experiment 1 prints the estimate of the so recht illusion with the numbers of the
jemals illusion, although its posterior in Figure 2 is centred near zero.

## Raw data

* <https://osf.io/s9rt8/>: stimulus materials, code and data of both experiments, with supplementary
  materials

## References

* [schwab-2023]
-/

@[expose] public section

namespace Schwab2023

open Data.Statistics

/-- The two experiments. -/
inductive Experiment where
  /-- 1: subject-extracted relative clauses (section 2) -/
  | exp1
  /-- 2: object-extracted relative clauses, faster presentation (section 3) -/
  | exp2
  deriving DecidableEq, Repr, Fintype

/-- The effects the Bayes factors test, labelled as in Figures 2 and 4. -/
inductive Effect where
  /-- NPI illusion: jemals: the illusory licensing of jemals by the relative-clause quantifier -/
  | illusionJemals
  /-- NPI illusion: so recht: the illusory licensing of so recht by the relative-clause
  quantifier -/
  | illusionSoRecht
  /-- Interaction effect: illusory licensing: the difference between the two illusions -/
  | interaction
  deriving DecidableEq, Repr, Fintype

/-- The paper's reading of a Bayes factor. -/
inductive Verdict where
  /-- very strong evidence for the effect: very strong evidence for the effect -/
  | veryStrongForEffect
  /-- moderate evidence for the effect: moderate evidence in favour of the effect -/
  | moderateForEffect
  /-- inconclusive: inconclusive -/
  | inconclusive
  /-- slightly favours the null: slightly favoured the null hypothesis -/
  | slightlyForNull
  /-- moderate evidence for the null: moderate evidence for the null hypothesis -/
  | moderateForNull
  deriving DecidableEq, Repr, Fintype

/-- A row of sections 2.1.5 and 3.1.5, pp. 12-13 and 18: the Bayes factor for an effect and the
paper's reading of it. -/
structure BayesFactor where
  /-- The Bayes factor for the effect over the null, BF10. -/
  bf10 : Decimal
  /-- The paper's reading of it. -/
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The cells of sections 2.1.5 and 3.1.5, pp. 12-13 and 18, by experiment and effect; from an
experiment; checked against the page images. -/
def bayesFactors : Experiment → Effect → BayesFactor
  | .exp1, .illusionJemals => ⟨⟨965, 2⟩, .moderateForEffect⟩
  | .exp1, .illusionSoRecht => ⟨⟨43, 2⟩, .slightlyForNull⟩
  | .exp1, .interaction => ⟨⟨116, 2⟩, .inconclusive⟩
  | .exp2, .illusionJemals => ⟨⟨9874, 1⟩, .veryStrongForEffect⟩
  | .exp2, .illusionSoRecht => ⟨⟨33, 2⟩, .moderateForNull⟩
  | .exp2, .interaction => ⟨⟨654, 2⟩, .moderateForEffect⟩

end Schwab2023
