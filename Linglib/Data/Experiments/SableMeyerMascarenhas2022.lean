module

public import Linglib.Data.Experiments.Schema

/-!
# SableMeyerMascarenhas2022: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/SableMeyerMascarenhas2022.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

A norming study and two inference-endorsement experiments on indirect illusory inferences from
disjunction. The norming study rated the strength of the causal link in conditionals of three kinds:
the crucial dependence from the hint d to the conjunct a, and the control dependences a-to-b and
d-to-b; item 0 was removed after the control block showed an effect driven by it. Experiment 1
presented problems of the form (a and b) or c; d, therefore b; Experiment 2 moved the causal step to
the conclusion: (b and d) or c; b, therefore a. Acceptance of the fallacy is regressed on the normed
strength of the d-to-a link; coefficients, control rates and the binomial model are recorded as
printed.

## Raw data

* <https://osf.io/tuc8s/>: complete materials, collected data, and analysis code

## References

* [sable-meyer-mascarenhas-2022]
-/

@[expose] public section

namespace SableMeyerMascarenhas2022

open Data.Experiments

/-- The three studies. -/
inductive Study where
  /-- Norming study: strength ratings of the causal conditionals -/
  | norming
  /-- Experiment 1: indirect illusory inferences, hint step -/
  | experimentOne
  /-- Experiment 2: indirect illusory inferences, conclusion step -/
  | experimentTwo
  deriving DecidableEq, Repr, Fintype

/-- The three normed causal links of the norming study (8). -/
inductive Dependence where
  /-- d to a: the crucial link from the hint to the first conjunct -/
  | hintToConjunct
  /-- a to b: control: from the first to the second conjunct -/
  | conjunctToConjunct
  /-- d to b: control: from the hint to the concluded conjunct -/
  | hintToConclusion
  deriving DecidableEq, Repr, Fintype

/-- The terms of the binomial model of Table 2. -/
inductive Term where
  /-- Intercept: -/
  | intercept
  /-- Normed d to a: the centered normed strength of the crucial link -/
  | normedStrength
  /-- % Error on Controls: the centered error rate on controls -/
  | errorOnControls
  /-- Interaction: their interaction -/
  | interaction
  deriving DecidableEq, Repr, Fintype

/-- The two inference tasks. -/
inductive Experiment where
  /-- Experiment 1: hint step -/
  | experimentOne
  /-- Experiment 2: conclusion step -/
  | experimentTwo
  deriving DecidableEq, Repr, Fintype

/-- The eight d-to-a item sets of (9). -/
inductive Item where
  /-- 0: fertilizer put on the plants, plants grew quickly -/
  | item0
  /-- 1: brake depressed, car slowed down -/
  | item1
  /-- 2: Mary jumped into the pool, Mary got wet -/
  | item2
  /-- 3: trigger pulled, gun fired -/
  | item3
  /-- 4: Larry grasped the glass, fingerprints on the glass -/
  | item4
  /-- 5: gong struck, gong sounded -/
  | item5
  /-- 6: John studied hard, did well on the test -/
  | item6
  /-- 7: apples ripe, fell from the tree -/
  | item7
  deriving DecidableEq, Repr, Fintype

/-- Whether an item set was kept for the inference tasks. -/
inductive ItemStatus where
  /-- kept: -/
  | kept
  /-- removed: removed after the norming analysis -/
  | removed
  deriving DecidableEq, Repr, Fintype

/-- The comparisons the target acceptance was tested against. -/
inductive Comparison where
  /-- chance: -/
  | chance
  /-- valid controls: -/
  | validControls
  /-- invalid controls: -/
  | invalidControls
  deriving DecidableEq, Repr, Fintype

/-- The outcome of the norming ANOVA for a block. -/
inductive AnovaOutcome where
  /-- no effect: no significant effect of the materials at the .05 level -/
  | noEffect
  /-- effect: a significant effect at the .05 level -/
  | effect
  deriving DecidableEq, Repr, Fintype

/-- Whether a model term is reported significant. -/
inductive Significance where
  /-- significant: -/
  | significant
  /-- not significant: -/
  | notSignificant
  deriving DecidableEq, Repr, Fintype

/-- Acceptance of the classical illusory inference from disjunction, about 85% across studies.
(§1, p. 568; checked against the PDF text layer only.) -/
def classicalAcceptancePct : ℕ := 85

/-- Conditional sentences rated in the norming study, three blocks of eight. (§3.1.2, p. 573;
checked against the PDF text layer only.) -/
def normingItems : ℕ := 24

/-- Item sets kept for the inference tasks after item 0 was removed. (§3.2.1, p. 576; checked
against the PDF text layer only.) -/
def itemSetsKept : ℕ := 7

/-- Indirect illusory inference trials, interleaved with three valid and three invalid controls.
(§3.1.2, p. 575; checked against the PDF text layer only.) -/
def targetsPerParticipant : ℕ := 7

/-- Valid modus ponens controls. (§3.1.2, p. 575; checked against the PDF text layer only.) -/
def validControls : ℕ := 3

/-- Invalid controls denying the antecedent. (§3.1.2, p. 575; checked against the PDF text layer
only.) -/
def invalidControls : ℕ := 3

/-- Individuals recruited across the three studies. (§3.1.1, p. 573; checked against the PDF text
layer only.) -/
def recruitedTotal : ℕ := 322

/-- Norming participants in the first batch, halted over a reward-wording error. (§3.1.1, p. 574;
checked against the PDF text layer only.) -/
def normingBatchOne : ℕ := 82

/-- Norming participants reporting back in the second batch of 160. (§3.1.1, p. 574; checked
against the PDF text layer only.) -/
def normingBatchTwoReported : ℕ := 156

/-- Experiment 1 participants excluded for having taken the norming study. (§3.1.1, p. 574;
checked against the PDF text layer only.) -/
def expOneExcludedNormed : ℕ := 14

/-- Experiment 2 participants excluded for an earlier related experiment. (§4.1, p. 579; checked
against the PDF text layer only.) -/
def expTwoExcludedPrior : ℕ := 10

/-- Points of the causal-strength rating scale. (§3.1.2, p. 574; checked against the PDF text
layer only.) -/
def likertPoints : ℕ := 7

/-- Item sets normed, of which seven were kept. (§3.2.1, p. 576; checked against the PDF text
layer only.) -/
def itemSets : ℕ := 8

/-- The acceptance the Experiment 1 model predicts in the matching limit P(a given d) = 1:
intercept plus slope. (§5, p. 581; checked against the PDF text layer only.) -/
def matchingLimitAcceptance : Decimal := ⟨92, 2⟩

/-- A row of Table 1, p. 574: the participant breakdown of Table 1. -/
structure Participants where
  /-- Participants recruited. -/
  recruited : ℕ
  /-- Participants analysed. -/
  analysed : ℕ
  /-- Percent female. -/
  femalePct : Decimal
  /-- Mean age. -/
  ageMean : ℕ
  /-- Standard deviation of age. -/
  ageSD : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 574, by study; checked against the PDF text layer only. -/
def participants : Study → Participants
  | .norming => ⟨242, 238, ⟨563, 1⟩, 32, ⟨131, 1⟩⟩
  | .experimentOne => ⟨80, 64, ⟨421, 1⟩, 34, ⟨100, 1⟩⟩
  | .experimentTwo => ⟨80, 70, ⟨471, 1⟩, 34, ⟨103, 1⟩⟩

/-- A row of §3.2.2, p. 576; §4.2, p. 579: mean acceptance of the valid and invalid controls,
with standard errors. -/
structure ControlRate where
  /-- Acceptance of valid controls, percent. -/
  validPct : Decimal
  /-- Its standard error. -/
  validSE : Decimal
  /-- Acceptance of invalid controls, percent. -/
  invalidPct : Decimal
  /-- Its standard error. -/
  invalidSE : Decimal
  deriving DecidableEq, Repr

/-- The cells of §3.2.2, p. 576; §4.2, p. 579, by experiment; checked against the PDF text layer
only. -/
def controlRates : Experiment → ControlRate
  | .experimentOne => ⟨⟨87, 0⟩, ⟨23, 1⟩, ⟨26, 0⟩, ⟨32, 1⟩⟩
  | .experimentTwo => ⟨⟨90, 0⟩, ⟨21, 1⟩, ⟨20, 0⟩, ⟨28, 1⟩⟩

/-- A row of §3.2.2, p. 577; §4.2, p. 580: the per-item regression of fallacy acceptance on the
normed strength of the d-to-a link. -/
structure Regression where
  /-- The slope. -/
  slope : Decimal
  /-- The intercept, when reported. -/
  intercept : Option Decimal
  /-- Its standard error. -/
  interceptSE : Option Decimal
  /-- Its standard error. -/
  slopeSE : Decimal
  /-- The coefficient of determination. -/
  rSquared : Decimal
  /-- The F statistic on 1 and 5 degrees of freedom. -/
  fStat : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of §3.2.2, p. 577; §4.2, p. 580, by experiment; checked against the PDF text layer
only. -/
def regressions : Experiment → Regression
  | .experimentOne =>  -- the intercept is not significant; the matching limit P(a given d) = 1 predicts an acceptance of 0.92
    ⟨⟨97, 2⟩,
     some ⟨-5, 2⟩,
     some ⟨10, 2⟩,
     ⟨14, 2⟩,
     ⟨9, 1⟩,
     ⟨450, 1⟩,
     ⟨.eq, ⟨1, 3⟩⟩⟩
  | .experimentTwo => ⟨⟨69, 2⟩, none, none, ⟨26, 2⟩, ⟨58, 2⟩, ⟨692, 2⟩, ⟨.eq, ⟨46, 3⟩⟩⟩

/-- A row of Table 2, p. 578: the binomial model of Table 2: acceptance as a function of the
normed d-to-a strength, the error rate on controls, and their interaction (centered
predictors). -/
structure BinomialTerm where
  /-- The coefficient. -/
  beta : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- The z-value. -/
  z : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 578, by term; checked against the PDF text layer only. -/
def binomialModel : Term → BinomialTerm
  | .intercept => ⟨⟨50, 2⟩, ⟨10, 2⟩, ⟨498, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .normedStrength => ⟨⟨414, 2⟩, ⟨93, 2⟩, ⟨442, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .errorOnControls => ⟨⟨-37, 2⟩, ⟨41, 2⟩, ⟨-91, 2⟩, ⟨.eq, ⟨36, 2⟩⟩⟩
  | .interaction => ⟨⟨130, 1⟩, ⟨389, 2⟩, ⟨335, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩

/-- A row of (9) and §3.2.1, pp. 575-576: the eight item sets and whether they survived the
norming analysis. -/
structure ItemRow where
  /-- Kept or removed. -/
  status : ItemStatus
  deriving DecidableEq, Repr

/-- The cells of (9) and §3.2.1, pp. 575-576, by item; checked against the page images. -/
def items : Item → ItemRow
  | .item0 => ⟨.removed⟩  -- the d-to-b control block showed an effect driven by this item
  | .item1 => ⟨.kept⟩
  | .item2 => ⟨.kept⟩
  | .item3 => ⟨.kept⟩
  | .item4 => ⟨.kept⟩
  | .item5 => ⟨.kept⟩
  | .item6 => ⟨.kept⟩
  | .item7 => ⟨.kept⟩

/-- A row of §3.2.1, p. 576: the norming ANOVA outcome per control block; the crucial block was
not tested. -/
structure NormingBlock where
  /-- The ANOVA outcome, when one was run. -/
  anova : Option AnovaOutcome
  deriving DecidableEq, Repr

/-- The cells of §3.2.1, p. 576, by block; checked against the PDF text layer only. -/
def normingBlocks : Dependence → NormingBlock
  | .hintToConjunct => ⟨none⟩
  | .conjunctToConjunct => ⟨some .noEffect⟩
  | .hintToConclusion => ⟨some .effect⟩  -- Tukey HSD: driven by item 0, which was removed

/-- A row of §3.2.2, p. 577; §4.2, p. 580: the t-tests of target acceptance against chance and
the controls. -/
structure TargetContrast where
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of §3.2.2, p. 577; §4.2, p. 580, by experiment and comparison; checked against the
PDF text layer only. -/
def targetContrasts : Experiment → Comparison → TargetContrast
  | .experimentOne, .chance => ⟨⟨.lt, ⟨1, 3⟩⟩⟩
  | .experimentOne, .validControls => ⟨⟨.lt, ⟨1, 3⟩⟩⟩
  | .experimentOne, .invalidControls => ⟨⟨.lt, ⟨1, 3⟩⟩⟩
  | .experimentTwo, .chance => ⟨⟨.eq, ⟨66, 4⟩⟩⟩
  | .experimentTwo, .validControls => ⟨⟨.lt, ⟨1, 3⟩⟩⟩
  | .experimentTwo, .invalidControls => ⟨⟨.lt, ⟨1, 3⟩⟩⟩

/-- A row of §4.2, p. 580: the Experiment 2 binomial model, reported qualitatively: only the
crucial rating is significant. -/
structure BinomialTermTwo where
  /-- As reported; the intercept is not discussed. -/
  significance : Option Significance
  deriving DecidableEq, Repr

/-- The cells of §4.2, p. 580, by term; checked against the PDF text layer only. -/
def binomialModelExpTwo : Term → BinomialTermTwo
  | .intercept => ⟨none⟩
  | .normedStrength => ⟨some .significant⟩  -- at the p < .001 level
  | .errorOnControls => ⟨some .notSignificant⟩
  | .interaction => ⟨some .notSignificant⟩

end SableMeyerMascarenhas2022
