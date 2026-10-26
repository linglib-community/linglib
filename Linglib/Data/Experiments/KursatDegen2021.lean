module

public import Linglib.Data.Experiments.Schema

/-!
# KursatDegen2021: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/KursatDegen2021.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Three experiments on redundant colour and material adjectives. In Exp. 1 participants judged in a
timed forced choice whether a colour or material adjective held of an image, for 81 images of 12
objects. In Exp. 2, an interactive reference game, a speaker described a target among four objects
of one kind; on a critical trial colour or material was redundant, the competitor sharing the
redundant property with the target and the two distractors sharing the sufficient property with the
competitor. In Exp. 3 participants judged descriptions such as '2 green objects' against the
displays of Exp. 2. The statistics are fixed effects of mixed-effects regressions, printed in the
running text. The proportions of the bar plots are not printed and are not recorded.

## Raw data

* <https://github.com/leylakursat/perceptual_difficulty>: materials, data and analysis files for the
  three experiments, as the paper states; the repository was public when checked (2026-10-11)

## References

* [kursat-degen-2021]
-/

@[expose] public section

namespace KursatDegen2021

open Data.Experiments

/-- The experiments that measure how hard a property is to verify. -/
inductive Norming where
  /-- Exp. 1: an adjective judged against a single image -/
  | exp1
  /-- Exp. 3: a description judged against a four-object display of the production experiment -/
  | exp3
  deriving DecidableEq, Repr, Fintype

/-- The measures of perceptual difficulty. -/
inductive DifficultyMeasure where
  /-- error: the log odds of an incorrect response, in a logistic regression -/
  | error
  /-- response time: the log-transformed response time of a correct response, in a linear
  regression -/
  | responseTime
  deriving DecidableEq, Repr, Fintype

/-- The predictors of redundant adjective use in Exp. 2, in logistic regressions. -/
inductive Predictor where
  /-- redundant property: which property is redundant, in the analysis of Exp. 2 -/
  | redundantProperty
  /-- property type: the property type, mean-centred, in the analysis with the response times of
  Exp. 3 -/
  | propertyType
  /-- perceptual difficulty: the log response time of Exp. 3 residualized on property type, in
  the same analysis -/
  | difficulty
  /-- interaction: property type by perceptual difficulty, in the same analysis -/
  | interaction
  /-- log ratio: the log ratio of the mean response time for the sufficient property to that for
  the redundant property, residualized on property type, in a second analysis -/
  | logRatio
  deriving DecidableEq, Repr, Fintype

/-- A row of §2.3 and §4.3, pp. 679 and 683: the effect of material against colour, the reference
level, on a measure of perceptual difficulty in a norming experiment. -/
structure Verification where
  /-- The coefficient. -/
  beta : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The t statistic, printed for the linear regressions. -/
  t : Option Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of §2.3 and §4.3, pp. 679 and 683, by experiment and measure; checked against the
page images. -/
def verification : Norming → DifficultyMeasure → Verification
  | .exp1, .error => ⟨⟨48, 2⟩, ⟨12, 2⟩, none, ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp1, .responseTime =>  -- the printed standard error and t statistic do not agree
    ⟨⟨544, 2⟩,
     ⟨474, 2⟩,
     some ⟨1149, 2⟩,
     ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp3, .error => ⟨⟨96, 2⟩, ⟨9, 2⟩, none, ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp3, .responseTime =>  -- the t statistic is printed as negative
    ⟨⟨24, 2⟩,
     ⟨18, 3⟩,
     some ⟨-5962, 2⟩,
     ⟨.lt, ⟨1, 4⟩⟩⟩

/-- A row of §3.3 and §4.3, pp. 681–684: the effect of a predictor on the log odds that the
speaker of Exp. 2 mentions the redundant property. -/
structure RedundantUse where
  /-- The coefficient. -/
  beta : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of §3.3 and §4.3, pp. 681–684, by predictor; checked against the page images. -/
def redundantUse : Predictor → RedundantUse
  | .redundantProperty =>  -- the reference level is given as colour, the reading as more colour
    ⟨⟨232, 2⟩,
     ⟨64, 2⟩,
     ⟨.lt, ⟨1, 4⟩⟩⟩
  | .propertyType =>  -- the text calls this an effect on response time
    ⟨⟨743, 2⟩,
     ⟨227, 2⟩,
     ⟨.lt, ⟨1, 3⟩⟩⟩
  | .difficulty => ⟨⟨-113, 1⟩, ⟨1641, 2⟩, ⟨.eq, ⟨49, 2⟩⟩⟩
  | .interaction => ⟨⟨1357, 2⟩, ⟨3187, 2⟩, ⟨.eq, ⟨67, 2⟩⟩⟩
  | .logRatio => ⟨⟨531, 2⟩, ⟨387, 2⟩, ⟨.eq, ⟨17, 2⟩⟩⟩

end KursatDegen2021
