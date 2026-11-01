module

public import Linglib.Data.Experiments.Schema

/-!
# AlexandropoulouGotzner2024a: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/AlexandropoulouGotzner2024a.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

Two rating experiments on English antonymic adjectives under negation, Experiment 1 on relative
adjectives and Experiment 2 on absolute ones, each with eight items. An item is a context in which a
speaker with full knowledge makes eight statements, crossing the evaluative polarity of the
adjective (positive or negative), its scalar strength (weak or strong) and the presence of negation;
participants saw the eight statements concurrently and rated each individual on a 1-5 scale from the
negative strong adjective to the positive strong one. The ratings were analysed with cumulative link
mixed models with treatment-coded Negation (negated as the reference level) and Scalar Strength, and
sum-coded Evaluative Polarity; a significant effect of Negation indicates an asymmetric
interpretation of the positive and negative adjectives under negation at the reference level of
Scalar Strength. The rating proportions of the figures are not printed and are not recorded.

## References

* [alexandropoulou-gotzner-2024a]
-/

@[expose] public section

namespace AlexandropoulouGotzner2024a

open Data.Experiments

/-- The type of the antonymic adjectives, one per experiment. -/
inductive AdjectiveType where
  /-- relative: Experiment 1, adjectives with a context-dependent standard, as large and small -/
  | relative
  /-- absolute: Experiment 2, adjectives with a scale-endpoint standard, as clean and dirty -/
  | absolute
  deriving DecidableEq, Repr, Fintype

/-- The informational strength of the adjectives, the factor Scalar Strength. -/
inductive Strength where
  /-- weak: the weak adjectives of an item, as large and small -/
  | weak
  /-- strong: the strong adjectives of an item, as gigantic and tiny -/
  | strong
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 4, p. 390; Table 5, p. 392; text, pp. 390-391: the effect of Negation, non-
negated against the negated reference level, in the experiment on an adjective type with a
strength as the reference level of Scalar Strength. -/
structure NegationEffect where
  /-- The estimate, where printed. -/
  estimate : Option Decimal
  /-- The standard error, where printed. -/
  se : Option Decimal
  /-- The z statistic, where printed. -/
  z : Option Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 390; Table 5, p. 392; text, pp. 390-391, by adjectiveType and
strength; checked against the page images. -/
def negationEffect : AdjectiveType → Strength → NegationEffect
  | .relative, .weak =>  -- Table 4; the text rounds it to beta = 0.64, p < 0.01
    ⟨some ⟨64392, 5⟩,
     some ⟨21714, 5⟩,
     some ⟨2965, 3⟩,
     ⟨.eq, ⟨302, 5⟩⟩⟩
  | .relative, .strong =>  -- printed in the text; the full output is in the supplementary materials
    ⟨some ⟨5, 2⟩,
     some ⟨25, 2⟩,
     some ⟨18, 2⟩,
     ⟨.eq, ⟨86, 2⟩⟩⟩
  | .absolute, .weak =>  -- Table 5; the text rounds it to p = 0.17
    ⟨some ⟨17288, 5⟩,
     some ⟨12453, 5⟩,
     some ⟨1388, 3⟩,
     ⟨.eq, ⟨165, 3⟩⟩⟩
  | .absolute, .strong =>  -- printed in the text as a marginal effect, with no estimate
    ⟨none,
     none,
     none,
     ⟨.eq, ⟨7, 2⟩⟩⟩

end AlexandropoulouGotzner2024a
