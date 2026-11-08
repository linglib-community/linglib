module

public import Linglib.Data.Statistics.Schema

/-!
# MartyEtAl2026: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/MartyEtAl2026.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Two picture-verification experiments on presupposition projection from the scope of 'each', 'none'
and 'exactly one' (the last with a positive and a negated scope), over a domain of four children
named and pictured. Experiment 1 tests the existence presupposition of 'the present in front of him'
(74 participants after exclusions), Experiment 2 the gender presupposition of 'her' (71). Each
target sentence was paired with four picture types, each instantiated four times with the children's
positions varied, and judged 'Good' or 'Bad'. Figure 1 plots the proportion of 'Good' responses per
sentence and picture type, recorded here as counts recomputed from the released trials; the text
reports some of them as rounded percentages.

## Raw data

* <https://osf.io/46vef>: trial-level data, condition means and analysis output of both experiments
  (§3.4); the pictures and counts are recomputed from processed_data_existence.csv and
  processed_data_gender.csv, which already apply the exclusions of §3.5

## References

* [marty-etal-2026]
-/

@[expose] public section

namespace MartyEtAl2026

open Data.Statistics

/-- An experiment: the presupposition it tests. -/
inductive Experiment where
  /-- Exp.1: Experiment 1, the existence presupposition of *the present in front of him* -/
  | existence
  /-- Exp.2: Experiment 2, the gender presupposition of *her* -/
  | gender
  deriving DecidableEq, Repr, Fintype

/-- A target sentence (3a-d): its quantifier and the polarity of its scope. -/
inductive Sentence where
  /-- m-pos: *each of the four ... opened the present in front of him/her* -/
  | mPos
  /-- m-neg: *none of the four ... opened the present in front of him/her* -/
  | mNeg
  /-- nm-pos: *exactly one of the four ... opened the present in front of him/her* -/
  | nmPos
  /-- nm-neg: *exactly one of the four ... didn't open the present in front of him/her* -/
  | nmNeg
  deriving DecidableEq, Repr, Fintype

/-- A picture type paired with a target sentence. -/
inductive Picture where
  /-- False: the presupposition holds of every child and the assertion is false -/
  | false
  /-- Target-1: the presupposition fails of some child, the first such picture -/
  | target1
  /-- Target-2: the presupposition fails of some child, the second such picture -/
  | target2
  /-- True: the presupposition holds of every child and the assertion is true -/
  | true
  deriving DecidableEq, Repr, Fintype

/-- What lies in front of a child in a picture of Experiment 1. -/
inductive Gift where
  /-- no present: no present -/
  | noPresent
  /-- closed present: a present the child has not opened -/
  | closedPresent
  /-- open present: a present the child has opened -/
  | openPresent
  deriving DecidableEq, Repr, Fintype

/-- A child in a picture of Experiment 2, who always has a present: a girl or a boy, the present
open or closed. -/
inductive Recipient where
  /-- girl, open present: a girl with an open present -/
  | girlOpen
  /-- girl, closed present: a girl with a closed present -/
  | girlClosed
  /-- boy, open present: a boy, drawn with glasses, with an open present -/
  | boyOpen
  /-- boy, closed present: a boy, drawn with glasses, with a closed present -/
  | boyClosed
  deriving DecidableEq, Repr, Fintype

/-- An interpretive option of §2, coded as a binary predictor of the models of Table 3. -/
inductive Reading where
  /-- ∀: universal projection, ∀-proj -/
  | univ
  /-- ∃: existential projection, ∃-proj -/
  | exist
  /-- Λ: intermediate projection, Λ-proj -/
  | intermediate
  /-- LocA: local accommodation at the scope -/
  | locA
  deriving DecidableEq, Repr, Fintype

/-- A model of Table 3, named by its predictors. -/
inductive Model where
  /-- ∀+LocA: ∀-proj with local accommodation -/
  | univLocA
  /-- ∃+LocA: ∃-proj with local accommodation -/
  | existLocA
  /-- Λ+LocA: Λ-proj with local accommodation -/
  | intermediateLocA
  /-- ∀+∃+LocA: ∀-proj and ∃-proj with local accommodation -/
  | univExistLocA
  /-- ∀+Λ+LocA: ∀-proj and Λ-proj with local accommodation -/
  | univIntermediateLocA
  deriving DecidableEq, Repr, Fintype

/-- The children in every picture and in the domain of every target sentence, 'the four children'
('recipients' in Exp. 2). (§3.2, p. 752; checked against the page images.) -/
def children : ℕ := 4

/-- A row of Table 2, p. 754: the children of a picture of Experiment 1, what lies in front of
each, as a multiset listed in the order of the levels. -/
structure ExistencePicture where
  /-- What lies in front of each child. -/
  children : List Gift
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 754, by sentence and picture; from an experiment; recomputed from
the authors' released data by `scripts/check_statistics.py`. -/
def existencePictures : Sentence → Picture → ExistencePicture
  | .mPos, .false => ⟨[.closedPresent, .openPresent, .openPresent, .openPresent]⟩
  | .mPos, .target1 => ⟨[.noPresent, .noPresent, .noPresent, .noPresent]⟩
  | .mPos, .target2 => ⟨[.noPresent, .openPresent, .openPresent, .openPresent]⟩
  | .mPos, .true => ⟨[.openPresent, .openPresent, .openPresent, .openPresent]⟩
  | .mNeg, .false => ⟨[.closedPresent, .closedPresent, .closedPresent, .openPresent]⟩
  | .mNeg, .target1 => ⟨[.noPresent, .noPresent, .noPresent, .noPresent]⟩
  | .mNeg, .target2 => ⟨[.noPresent, .closedPresent, .closedPresent, .closedPresent]⟩
  | .mNeg, .true => ⟨[.closedPresent, .closedPresent, .closedPresent, .closedPresent]⟩
  | .nmPos, .false => ⟨[.closedPresent, .closedPresent, .openPresent, .openPresent]⟩
  | .nmPos, .target1 => ⟨[.noPresent, .noPresent, .noPresent, .openPresent]⟩
  | .nmPos, .target2 => ⟨[.noPresent, .closedPresent, .closedPresent, .openPresent]⟩
  | .nmPos, .true => ⟨[.closedPresent, .closedPresent, .closedPresent, .openPresent]⟩
  | .nmNeg, .false => ⟨[.closedPresent, .closedPresent, .openPresent, .openPresent]⟩
  | .nmNeg, .target1 => ⟨[.noPresent, .openPresent, .openPresent, .openPresent]⟩
  | .nmNeg, .target2 => ⟨[.noPresent, .closedPresent, .openPresent, .openPresent]⟩
  | .nmNeg, .true => ⟨[.closedPresent, .openPresent, .openPresent, .openPresent]⟩

/-- A row of Table 2, p. 754: the children of a picture of Experiment 2, each a girl or a boy
with an open or a closed present, as a multiset listed in the order of the levels. -/
structure GenderPicture where
  /-- The children. -/
  children : List Recipient
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 754, by sentence and picture; from an experiment; recomputed from
the authors' released data by `scripts/check_statistics.py`. -/
def genderPictures : Sentence → Picture → GenderPicture
  | .mPos, .false => ⟨[.girlOpen, .girlOpen, .girlOpen, .girlClosed]⟩
  | .mPos, .target1 => ⟨[.boyOpen, .boyOpen, .boyOpen, .boyOpen]⟩
  | .mPos, .target2 => ⟨[.girlOpen, .girlOpen, .girlOpen, .boyOpen]⟩
  | .mPos, .true => ⟨[.girlOpen, .girlOpen, .girlOpen, .girlOpen]⟩
  | .mNeg, .false => ⟨[.girlOpen, .girlClosed, .girlClosed, .girlClosed]⟩
  | .mNeg, .target1 => ⟨[.boyClosed, .boyClosed, .boyClosed, .boyClosed]⟩
  | .mNeg, .target2 => ⟨[.girlClosed, .girlClosed, .girlClosed, .boyClosed]⟩
  | .mNeg, .true => ⟨[.girlClosed, .girlClosed, .girlClosed, .girlClosed]⟩
  | .nmPos, .false => ⟨[.girlOpen, .girlOpen, .girlClosed, .girlClosed]⟩
  | .nmPos, .target1 => ⟨[.girlOpen, .boyClosed, .boyClosed, .boyClosed]⟩
  | .nmPos, .target2 => ⟨[.girlOpen, .girlClosed, .girlClosed, .boyClosed]⟩
  | .nmPos, .true => ⟨[.girlOpen, .girlClosed, .girlClosed, .girlClosed]⟩
  | .nmNeg, .false => ⟨[.girlOpen, .girlOpen, .girlClosed, .girlClosed]⟩
  | .nmNeg, .target1 => ⟨[.girlOpen, .girlOpen, .girlOpen, .boyClosed]⟩
  | .nmNeg, .target2 => ⟨[.girlOpen, .girlOpen, .girlClosed, .boyOpen]⟩
  | .nmNeg, .true => ⟨[.girlOpen, .girlOpen, .girlOpen, .girlClosed]⟩

/-- A row of Table 2, p. 754: the interpretive options under which Table 2 prints a picture as
accepting its sentence, the coding of the binary predictors of the models of Table 3. -/
structure Prediction where
  /-- The options printed with 1. -/
  accepting : List Reading
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 754, by experiment and sentence and picture; from an experiment;
checked against the page images. -/
def predictions : Experiment → Sentence → Picture → Prediction
  | .existence, .mPos, .false => ⟨[]⟩
  | .existence, .mPos, .target1 => ⟨[]⟩
  | .existence, .mPos, .target2 => ⟨[]⟩
  | .existence, .mPos, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .existence, .mNeg, .false => ⟨[]⟩
  | .existence, .mNeg, .target1 => ⟨[.locA]⟩
  | .existence, .mNeg, .target2 => ⟨[.exist, .locA]⟩
  | .existence, .mNeg, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .existence, .nmPos, .false => ⟨[]⟩
  | .existence, .nmPos, .target1 => ⟨[.exist, .intermediate, .locA]⟩
  | .existence, .nmPos, .target2 => ⟨[.exist, .intermediate, .locA]⟩
  | .existence, .nmPos, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .existence, .nmNeg, .false => ⟨[]⟩
  | .existence, .nmNeg, .target1 => ⟨[.exist, .locA]⟩
  | .existence, .nmNeg, .target2 => ⟨[.exist, .intermediate, .locA]⟩
  | .existence, .nmNeg, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .gender, .mPos, .false => ⟨[]⟩
  | .gender, .mPos, .target1 => ⟨[]⟩
  | .gender, .mPos, .target2 => ⟨[]⟩
  | .gender, .mPos, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .gender, .mNeg, .false => ⟨[]⟩
  | .gender, .mNeg, .target1 => ⟨[.locA]⟩
  | .gender, .mNeg, .target2 => ⟨[.exist, .locA]⟩
  | .gender, .mNeg, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .gender, .nmPos, .false => ⟨[]⟩
  | .gender, .nmPos, .target1 => ⟨[.exist, .intermediate, .locA]⟩
  | .gender, .nmPos, .target2 => ⟨[.exist, .intermediate, .locA]⟩
  | .gender, .nmPos, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩
  | .gender, .nmNeg, .false => ⟨[]⟩
  | .gender, .nmNeg, .target1 => ⟨[.exist, .locA]⟩
  | .gender, .nmNeg, .target2 => ⟨[.exist, .intermediate, .locA]⟩
  | .gender, .nmNeg, .true => ⟨[.univ, .exist, .intermediate, .locA]⟩

/-- A row of Fig. 1, p. 757: the 'Good' responses to a target sentence with a picture type, over
the trials of the participants retained; Figure 1 plots their proportion. -/
structure Responses where
  /-- The 'Good' responses. -/
  good : ℕ
  /-- The trials. -/
  trials : ℕ
  deriving DecidableEq, Repr

/-- The cells of Fig. 1, p. 757, by experiment and sentence and picture; from an experiment;
recomputed from the authors' released data by `scripts/check_statistics.py`. -/
def responses : Experiment → Sentence → Picture → Responses
  | .existence, .mPos, .false => ⟨3, 296⟩
  | .existence, .mPos, .target1 => ⟨4, 296⟩
  | .existence, .mPos, .target2 => ⟨37, 296⟩
  | .existence, .mPos, .true => ⟨292, 296⟩
  | .existence, .mNeg, .false => ⟨4, 296⟩
  | .existence, .mNeg, .target1 => ⟨89, 296⟩
  | .existence, .mNeg, .target2 => ⟨175, 296⟩
  | .existence, .mNeg, .true => ⟨290, 296⟩
  | .existence, .nmPos, .false => ⟨8, 296⟩
  | .existence, .nmPos, .target1 => ⟨251, 296⟩
  | .existence, .nmPos, .target2 => ⟨204, 296⟩
  | .existence, .nmPos, .true => ⟨290, 296⟩
  | .existence, .nmNeg, .false => ⟨2, 296⟩
  | .existence, .nmNeg, .target1 => ⟨39, 296⟩
  | .existence, .nmNeg, .target2 => ⟨148, 296⟩
  | .existence, .nmNeg, .true => ⟨276, 296⟩
  | .gender, .mPos, .false => ⟨17, 284⟩
  | .gender, .mPos, .target1 => ⟨34, 284⟩
  | .gender, .mPos, .target2 => ⟨55, 284⟩
  | .gender, .mPos, .true => ⟨277, 284⟩
  | .gender, .mNeg, .false => ⟨11, 284⟩
  | .gender, .mNeg, .target1 => ⟨54, 284⟩
  | .gender, .mNeg, .target2 => ⟨69, 284⟩
  | .gender, .mNeg, .true => ⟨278, 284⟩
  | .gender, .nmPos, .false => ⟨12, 284⟩
  | .gender, .nmPos, .target1 => ⟨234, 284⟩
  | .gender, .nmPos, .target2 => ⟨227, 284⟩
  | .gender, .nmPos, .true => ⟨269, 284⟩
  | .gender, .nmNeg, .false => ⟨19, 284⟩
  | .gender, .nmNeg, .target1 => ⟨37, 284⟩
  | .gender, .nmNeg, .target2 => ⟨214, 284⟩
  | .gender, .nmNeg, .true => ⟨265, 284⟩

/-- A row of §3.6, pp. 756-757: an acceptance rate the text reports, in the order it reports
them. -/
structure ReportedRate where
  /-- The experiment. -/
  experiment : Experiment
  /-- The target sentence. -/
  sentence : Sentence
  /-- The picture type. -/
  picture : Picture
  /-- The rate, in percent. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The 22 rows of §3.6, pp. 756-757, in the paper's order; from an experiment; checked against
the page images. -/
def reportedRates : List ReportedRate :=
  [⟨.existence, .mNeg, .target1, ⟨30, 0⟩⟩,
   ⟨.gender, .mNeg, .target1, ⟨20, 0⟩⟩,
   ⟨.existence, .mNeg, .false, ⟨1, 0⟩⟩,
   ⟨.gender, .mNeg, .false, ⟨4, 0⟩⟩,
   ⟨.existence, .mPos, .target1, ⟨13, 0⟩⟩,
   ⟨.gender, .mPos, .target1, ⟨12, 0⟩⟩,
   ⟨.existence, .nmNeg, .target1, ⟨13, 0⟩⟩,
   ⟨.existence, .nmNeg, .target2, ⟨50, 0⟩⟩,
   ⟨.gender, .nmNeg, .target1, ⟨13, 0⟩⟩,
   ⟨.gender, .nmNeg, .target2, ⟨73, 0⟩⟩,
   ⟨.existence, .mNeg, .target2, ⟨59, 0⟩⟩,
   ⟨.existence, .mNeg, .target1, ⟨30, 0⟩⟩,
   ⟨.gender, .mNeg, .target2, ⟨24, 0⟩⟩,
   ⟨.gender, .mNeg, .target1, ⟨19, 0⟩⟩,
   ⟨.existence, .nmPos, .target2, ⟨69, 0⟩⟩,
   ⟨.existence, .nmPos, .target1, ⟨85, 0⟩⟩,
   ⟨.gender, .nmPos, .target2, ⟨80, 0⟩⟩,
   ⟨.gender, .nmPos, .target1, ⟨82, 0⟩⟩,
   ⟨.existence, .nmNeg, .target2, ⟨50, 0⟩⟩,
   ⟨.existence, .nmPos, .target2, ⟨69, 0⟩⟩,
   ⟨.gender, .nmNeg, .target2, ⟨75, 0⟩⟩,
   ⟨.gender, .nmPos, .target2, ⟨80, 0⟩⟩]

/-- A row of Table 3 and note 5, pp. 756-757: the predictors of a model, the interpretive options
of the theory it stands for (note 5). -/
structure ModelPredictors where
  /-- Its predictors. -/
  readings : List Reading
  deriving DecidableEq, Repr

/-- The cells of Table 3 and note 5, pp. 756-757, by model; fitted or simulated by a model;
checked against the page images. -/
def models : Model → ModelPredictors
  | .univLocA => ⟨[.univ, .locA]⟩
  | .existLocA => ⟨[.exist, .locA]⟩
  | .intermediateLocA => ⟨[.intermediate, .locA]⟩
  | .univExistLocA => ⟨[.univ, .exist, .locA]⟩
  | .univIntermediateLocA => ⟨[.univ, .intermediate, .locA]⟩

/-- A row of Table 3, p. 757: the fit of a model, a binomial GLMM with by-subject random
intercepts and slopes, to the responses to the target sentences. -/
structure ModelFit where
  /-- The number of parameters. -/
  npar : ℕ
  /-- The AIC. -/
  aic : ℕ
  /-- The BIC. -/
  bic : ℕ
  /-- The conditional R². -/
  r2 : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 3, p. 757, by experiment and model; fitted or simulated by a model;
checked against the page images. -/
def modelFits : Experiment → Model → ModelFit
  | .existence, .univLocA => ⟨7, 3061, 3106, ⟨74, 2⟩⟩
  | .existence, .existLocA => ⟨7, 3744, 3789, ⟨62, 2⟩⟩
  | .existence, .intermediateLocA => ⟨7, 3195, 3241, ⟨68, 2⟩⟩
  | .existence, .univExistLocA => ⟨11, 2951, 3022, ⟨75, 2⟩⟩
  | .existence, .univIntermediateLocA => ⟨11, 2783, 2854, ⟨76, 2⟩⟩
  | .gender, .univLocA => ⟨7, 3526, 3571, ⟨73, 2⟩⟩
  | .gender, .existLocA => ⟨7, 4075, 4120, ⟨56, 2⟩⟩
  | .gender, .intermediateLocA => ⟨7, 2671, 2716, ⟨75, 2⟩⟩
  | .gender, .univExistLocA => ⟨11, 3338, 3409, ⟨73, 2⟩⟩
  | .gender, .univIntermediateLocA => ⟨11, 2471, 2542, ⟨80, 2⟩⟩

end MartyEtAl2026
