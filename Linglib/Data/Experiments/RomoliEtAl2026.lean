module

public import Linglib.Data.Experiments.Schema

/-!
# RomoliEtAl2026: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/RomoliEtAl2026.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Three web-based truth-value judgment experiments with a plural definite bound by a quantifier:
'Every boy opened his presents' against 'No boy opened his presents' (Experiment 1) and against 'Not
every boy opened his presents' (Experiment 2), and 'Exactly two boys opened their presents'
(Experiment 3). Experiments 1 and 2 are those of Augurzky et al. (2023), reanalysed. Each picture
shows four children with nine presents each, opened ones coloured and closed ones grey. CONTEXT, a
family rule that opening the presents is prohibited (PROHIBITED) or required (REQUIRED) before the
guests arrive, is between participants and is reinforced by a first task asking whether the rule was
obeyed; PICTURE (control or target) and POLARITY (the positive or negative quantifier, or the
positive or negative part of exactly two) are within participants. Participants rated how well the
sentence describes the picture on a five-point scale from 'completely true' to 'completely false'.
The target conditions are analysed by proportional-odds cumulative logit mixed-effects models with
CONTEXT sum-coded (STRICT -0.5, LAX 0.5, LAX being PROHIBITED for the positive condition and
REQUIRED for the negative) and POLARITY treatment-coded with the negative condition as reference
level. The random-effect estimates of Tables 5, 8 and 11 are not transcribed.

## References

* [romoli-etal-2026]
-/

@[expose] public section

namespace RomoliEtAl2026

open Data.Experiments

/-- The experiment. -/
inductive Experiment where
  /-- Experiment 1: every against no -/
  | one
  /-- Experiment 2: every against not every -/
  | two
  /-- Experiment 3: exactly two -/
  | three
  deriving DecidableEq, Repr, Fintype

/-- The quantifier binding the plural definite, (23). -/
inductive Quantifier where
  /-- every: 'Every boy opened his presents' -/
  | every
  /-- no: 'No boy opened his presents' -/
  | no
  /-- not every: 'Not every boy opened his presents' -/
  | notEvery
  /-- exactly two: 'Exactly two boys opened their presents' -/
  | exactlyTwo
  deriving DecidableEq, Repr, Fintype

/-- The factor POLARITY: the positive or negative quantifier, or the positive or negative part of
the meaning of exactly two. -/
inductive Polarity where
  /-- POSITIVE: every, or the positive part of exactly two -/
  | positive
  /-- NEGATIVE: no or not every, or the negative part of exactly two -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The factor CONTEXT: the family rule. -/
inductive Context where
  /-- PROHIBITED: opening the presents is prohibited before the grandparents arrive, which raises
  whether any boy opened any of his presents -/
  | prohibited
  /-- REQUIRED: opening the presents is required before the aunt and uncle arrive, which raises
  whether every boy opened all of his presents -/
  | required
  deriving DecidableEq, Repr, Fintype

/-- CONTEXT as Figures 4 and 6 recode it. -/
inductive Recoding where
  /-- LAX: the context favouring non-maximality, PROHIBITED for the positive condition and
  REQUIRED for the negative -/
  | lax
  /-- STRICT: the context favouring maximality -/
  | strict
  deriving DecidableEq, Repr, Fintype

/-- The factor PICTURE, as the captions of Figures 3, 5 and 7 name its levels. -/
inductive Picture where
  /-- CONTROL: a control picture, true for one sentence and false for the other -/
  | control
  /-- TRUE CONTROL: a control picture on which the sentence is true -/
  | trueControl
  /-- FALSE CONTROL: a control picture on which the sentence is false -/
  | falseControl
  /-- TARGET: a picture on which the sentence is true on a non-maximal reading only -/
  | target
  deriving DecidableEq, Repr, Fintype

/-- A picture in the legends of Figures 4, 6 and 8. -/
inductive Truth where
  /-- True: the true control -/
  | trueControl
  /-- Target: the target -/
  | target
  /-- False: the false control -/
  | falseControl
  deriving DecidableEq, Repr, Fintype

/-- The term of a model that a test is of. -/
inductive Effect where
  /-- CONTEXT: the simple effect of CONTEXT on the negative condition, the reference level of
  POLARITY -/
  | context
  /-- POLARITY: the main effect of POLARITY -/
  | polarity
  /-- CONTEXT × POLARITY: the interaction of CONTEXT and POLARITY -/
  | interaction
  deriving DecidableEq, Repr, Fintype

/-- A fixed effect of a model. -/
inductive Term where
  /-- θ1: the first threshold -/
  | theta1
  /-- θ2: the second threshold -/
  | theta2
  /-- θ3: the third threshold -/
  | theta3
  /-- θ4: the fourth threshold -/
  | theta4
  /-- CONTEXT: CONTEXT -/
  | context
  /-- POLARITY: POLARITY -/
  | polarity
  /-- CONTEXT × POLARITY: their interaction -/
  | interaction
  deriving DecidableEq, Repr, Fintype

/-- How a p-value is printed. -/
inductive Bound where
  /-- <: as an upper bound -/
  | below
  /-- =: as a value -/
  | exact
  deriving DecidableEq, Repr, Fintype

/-- The children in a picture. (§3.3.1; checked against the PDF text layer only.) -/
def boys : ℕ := 4

/-- The presents of each child. (§3.3.1; checked against the PDF text layer only.) -/
def presents : ℕ := 9

/-- The points of the rating scale. (§3.1; checked against the PDF text layer only.) -/
def scalePoints : ℕ := 5

/-- The lists the items of each experiment were spread over, 2 contexts × 2 genders × 2 ways of
labelling the response buttons. (§3.3.1, §3.4.1, §3.5.1; checked against the page images.) -/
def lists : ℕ := 8

/-- A row of §3.3.1, §3.4.1, §3.5.1: the native speakers of English recruited on Prolific for an
experiment, those excluded for 75% or less accuracy on the control items or those retained,
as the paper prints them, and the mean accuracy of the retained on the control items. -/
structure Participants where
  /-- The participants recruited. -/
  recruited : ℕ
  /-- The participants excluded, where printed. -/
  excluded : Option ℕ
  /-- The participants retained, where printed. -/
  retained : Option ℕ
  /-- The mean accuracy on the control items, in percent. -/
  accuracy : Decimal
  deriving DecidableEq, Repr

/-- The cells of §3.3.1, §3.4.1, §3.5.1, by experiment; checked against the page images. -/
def participants : Experiment → Participants
  | .one => ⟨192, some 4, none, ⟨981, 1⟩⟩
  | .two => ⟨192, some 6, none, ⟨974, 1⟩⟩
  | .three => ⟨192, none, some 180, ⟨983, 1⟩⟩

/-- A row of (31), (32), (34): the quantifier of the sentence each level of POLARITY tests in an
experiment. -/
structure Sentence where
  /-- The quantifier of the sentence. -/
  quantifier : Quantifier
  deriving DecidableEq, Repr

/-- The cells of (31), (32), (34), by experiment and polarity; checked against the PDF text layer
only. -/
def sentences : Experiment → Polarity → Sentence
  | .one, .positive => ⟨.every⟩
  | .one, .negative => ⟨.no⟩
  | .two, .positive => ⟨.every⟩
  | .two, .negative => ⟨.notEvery⟩
  | .three, .positive => ⟨.exactlyTwo⟩
  | .three, .negative => ⟨.exactlyTwo⟩

/-- A row of Figures 3, 5 and 7: an example picture of an experiment: its level of PICTURE, the
levels of POLARITY a target picture is for, and how many of his nine presents each child
opened, in the figure's order of the children. -/
structure Item where
  /-- The experiment. -/
  experiment : Experiment
  /-- The level of PICTURE. -/
  picture : Picture
  /-- The levels of POLARITY a target picture is for. -/
  targetFor : List Polarity
  /-- The presents each child opened. -/
  opened : List ℕ
  deriving DecidableEq, Repr

/-- The 11 rows of Figures 3, 5 and 7, in the paper's order; checked against the page images. -/
def pictures : List Item :=
  [⟨.one, .control, [], [9, 9, 9, 9]⟩,
   ⟨.one, .control, [], [0, 0, 0, 0]⟩,
   ⟨.one, .target, [.positive], [5, 9, 3, 9]⟩,
   ⟨.one, .target, [.negative], [0, 4, 0, 3]⟩,  -- Nathan, Leo, Frank, Mike
   ⟨.two, .control, [], [9, 9, 9, 9]⟩,
   ⟨.two, .control, [], [0, 9, 0, 9]⟩,
   ⟨.two, .target, [.positive, .negative], [5, 9, 3, 9]⟩,
   ⟨.three, .trueControl, [], [0, 9, 0, 9]⟩,
   ⟨.three, .falseControl, [], [9, 9, 9, 9]⟩,
   ⟨.three, .target, [.positive], [0, 4, 0, 3]⟩,  -- Nathan, Leo, Frank, Mike
   ⟨.three, .target, [.negative], [5, 9, 3, 9]⟩]

/-- A row of Figures 4 and 6: the mean rating of a picture for the sentence of a level of
POLARITY in a recoded context. -/
structure Mean where
  /-- The experiment. -/
  experiment : Experiment
  /-- The level of POLARITY. -/
  polarity : Polarity
  /-- The recoded context. -/
  recoding : Recoding
  /-- The picture. -/
  truth : Truth
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 24 rows of Figures 4 and 6, in the paper's order; checked against the page images. -/
def means : List Mean :=
  [⟨.one, .positive, .lax, .trueControl, ⟨498, 2⟩⟩,
   ⟨.one, .positive, .lax, .target, ⟨376, 2⟩⟩,
   ⟨.one, .positive, .lax, .falseControl, ⟨113, 2⟩⟩,
   ⟨.one, .positive, .strict, .trueControl, ⟨496, 2⟩⟩,
   ⟨.one, .positive, .strict, .target, ⟨263, 2⟩⟩,
   ⟨.one, .positive, .strict, .falseControl, ⟨104, 2⟩⟩,
   ⟨.one, .negative, .lax, .trueControl, ⟨491, 2⟩⟩,
   ⟨.one, .negative, .lax, .target, ⟨230, 2⟩⟩,
   ⟨.one, .negative, .lax, .falseControl, ⟨110, 2⟩⟩,
   ⟨.one, .negative, .strict, .trueControl, ⟨487, 2⟩⟩,
   ⟨.one, .negative, .strict, .target, ⟨180, 2⟩⟩,
   ⟨.one, .negative, .strict, .falseControl, ⟨108, 2⟩⟩,
   ⟨.two, .positive, .lax, .trueControl, ⟨489, 2⟩⟩,
   ⟨.two, .positive, .lax, .target, ⟨394, 2⟩⟩,
   ⟨.two, .positive, .lax, .falseControl, ⟨133, 2⟩⟩,
   ⟨.two, .positive, .strict, .trueControl, ⟨497, 2⟩⟩,
   ⟨.two, .positive, .strict, .target, ⟨234, 2⟩⟩,
   ⟨.two, .positive, .strict, .falseControl, ⟨127, 2⟩⟩,
   ⟨.two, .negative, .lax, .trueControl, ⟨466, 2⟩⟩,
   ⟨.two, .negative, .lax, .target, ⟨396, 2⟩⟩,
   ⟨.two, .negative, .lax, .falseControl, ⟨110, 2⟩⟩,
   ⟨.two, .negative, .strict, .trueControl, ⟨452, 2⟩⟩,
   ⟨.two, .negative, .strict, .target, ⟨205, 2⟩⟩,
   ⟨.two, .negative, .strict, .falseControl, ⟨113, 2⟩⟩]

/-- A row of Figure 8: the mean rating of a picture in Experiment 3 in a context, not recoded, a
target picture with the level of POLARITY it is for. -/
structure MeanExactlyTwo where
  /-- The context. -/
  context : Context
  /-- The picture. -/
  truth : Truth
  /-- The level of POLARITY of a target. -/
  polarity : Option Polarity
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 8 rows of Figure 8, in the paper's order; checked against the page images. -/
def meansExactlyTwo : List MeanExactlyTwo :=
  [⟨.prohibited, .trueControl, none, ⟨495, 2⟩⟩,
   ⟨.prohibited, .target, some .positive, ⟨400, 2⟩⟩,
   ⟨.prohibited, .target, some .negative, ⟨203, 2⟩⟩,
   ⟨.prohibited, .falseControl, none, ⟨132, 2⟩⟩,
   ⟨.required, .trueControl, none, ⟨492, 2⟩⟩,
   ⟨.required, .target, some .positive, ⟨374, 2⟩⟩,
   ⟨.required, .target, some .negative, ⟨236, 2⟩⟩,
   ⟨.required, .falseControl, none, ⟨134, 2⟩⟩]

/-- A row of §3.3.3, §3.4.3, §3.5.3: a likelihood-ratio χ² test of a term of the cumulative logit
mixed-effects model fitted to an experiment's target conditions. -/
structure Test where
  /-- The degrees of freedom of the chi-square statistic. -/
  df : ℕ
  /-- The chi-square statistic. -/
  chiSq : Decimal
  /-- How the p-value is printed. -/
  bound : Bound
  /-- The p-value. -/
  p : Decimal
  deriving DecidableEq, Repr

/-- The cells of §3.3.3, §3.4.3, §3.5.3, by experiment and effect; checked against the page
images. -/
def tests : Experiment → Effect → Test
  | .one, .context => ⟨1, ⟨127, 1⟩, .below, ⟨1, 3⟩⟩
  | .one, .polarity => ⟨1, ⟨522, 1⟩, .below, ⟨1, 3⟩⟩
  | .one, .interaction => ⟨1, ⟨109, 1⟩, .below, ⟨1, 3⟩⟩
  | .two, .context => ⟨1, ⟨973, 1⟩, .below, ⟨1, 3⟩⟩
  | .two, .polarity => ⟨1, ⟨53, 2⟩, .exact, ⟨469, 3⟩⟩
  | .two, .interaction => ⟨1, ⟨24, 2⟩, .exact, ⟨624, 3⟩⟩
  | .three, .context => ⟨1, ⟨158, 1⟩, .below, ⟨1, 3⟩⟩
  | .three, .polarity => ⟨1, ⟨342, 1⟩, .below, ⟨1, 3⟩⟩
  | .three, .interaction => ⟨1, ⟨19, 3⟩, .exact, ⟨892, 3⟩⟩

/-- A row of Tables 5, 8 and 11: a fixed-effect estimate of the cumulative logit mixed-effects
model fitted to an experiment's target conditions, with the p-value of its likelihood-ratio
test where printed. -/
structure Estimate where
  /-- The estimate. -/
  beta : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- How the p-value is printed, where it is. -/
  bound : Option Bound
  /-- The p-value, where printed. -/
  p : Option Decimal
  deriving DecidableEq, Repr

/-- The cells of Tables 5, 8 and 11, by experiment and term; checked against the page images. -/
def estimates : Experiment → Term → Estimate
  | .one, .theta1 => ⟨⟨-49, 2⟩, ⟨21, 2⟩, none, none⟩
  | .one, .theta2 => ⟨⟨134, 2⟩, ⟨23, 2⟩, none, none⟩
  | .one, .theta3 => ⟨⟨307, 2⟩, ⟨28, 2⟩, none, none⟩
  | .one, .theta4 => ⟨⟨723, 2⟩, ⟨51, 2⟩, none, none⟩
  | .one, .context => ⟨⟨141, 2⟩, ⟨40, 2⟩, some .below, some ⟨1, 3⟩⟩
  | .one, .polarity => ⟨⟨336, 2⟩, ⟨37, 2⟩, some .below, some ⟨1, 3⟩⟩
  | .one, .interaction => ⟨⟨243, 2⟩, ⟨74, 2⟩, some .below, some ⟨1, 3⟩⟩
  | .two, .theta1 => ⟨⟨-188, 2⟩, ⟨10, 2⟩, none, none⟩
  | .two, .theta2 => ⟨⟨-60, 2⟩, ⟨9, 2⟩, none, none⟩
  | .two, .theta3 => ⟨⟨20, 2⟩, ⟨9, 2⟩, none, none⟩
  | .two, .theta4 => ⟨⟨215, 2⟩, ⟨10, 2⟩, none, none⟩
  | .two, .context => ⟨⟨326, 2⟩, ⟨17, 2⟩, some .below, some ⟨1, 3⟩⟩
  | .two, .polarity => ⟨⟨13, 2⟩, ⟨17, 2⟩, some .exact, some ⟨47, 2⟩⟩
  | .two, .interaction => ⟨⟨-17, 2⟩, ⟨35, 2⟩, some .exact, some ⟨62, 2⟩⟩
  | .three, .theta1 => ⟨⟨-11, 2⟩, ⟨26, 2⟩, none, none⟩
  | .three, .theta2 => ⟨⟨73, 2⟩, ⟨26, 2⟩, none, none⟩
  | .three, .theta3 => ⟨⟨150, 2⟩, ⟨27, 2⟩, none, none⟩
  | .three, .theta4 => ⟨⟨293, 2⟩, ⟨28, 2⟩, none, none⟩
  | .three, .context => ⟨⟨61, 2⟩, ⟨15, 2⟩, some .below, some ⟨1, 3⟩⟩
  | .three, .polarity => ⟨⟨315, 2⟩, ⟨41, 2⟩, some .below, some ⟨1, 3⟩⟩
  | .three, .interaction => ⟨⟨6, 2⟩, ⟨41, 2⟩, some .exact, some ⟨89, 2⟩⟩

/-- A row of Table 12: the effect size of the context manipulation on the target condition of a
level of POLARITY in an experiment: the difference of the mean ratings in the lax and the
strict context, and in log-odds from the model's fixed-effect estimates. -/
structure EffectSize where
  /-- The difference of the mean ratings. -/
  likert : Decimal
  /-- The effect in log-odds. -/
  logOdds : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 12, by experiment and polarity; checked against the page images. -/
def effectSizes : Experiment → Polarity → EffectSize
  | .one, .positive => ⟨⟨113, 2⟩, ⟨384, 2⟩⟩
  | .two, .positive => ⟨⟨160, 2⟩, ⟨309, 2⟩⟩
  | .two, .negative => ⟨⟨191, 2⟩, ⟨326, 2⟩⟩
  | .one, .negative => ⟨⟨50, 2⟩, ⟨141, 2⟩⟩
  | .three, .positive => ⟨⟨26, 2⟩, ⟨66, 2⟩⟩
  | .three, .negative => ⟨⟨33, 2⟩, ⟨61, 2⟩⟩

end RomoliEtAl2026
