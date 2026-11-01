module

public import Linglib.Data.Statistics.Schema

/-!
# BeltramaSoltBurnett2023: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/BeltramaSoltBurnett2023.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Two social perception experiments on American English numerals. Precision (approximate *about fifty
minutes*, underspecified *fifty minutes*, precise *forty-nine minutes*) was crossed with Scenario
(For-the-record, Persuasive, Stranger, Bonding). Participants rated the speaker on ten seven-point
scales, which a principal component analysis reduced to Status, Solidarity and anti-Solidarity
composite scores. Experiment 1 recruited on Amazon Mechanical Turk with six written items per
participant; Experiment 2 showed one illustrated item per participant.

## References

* [beltrama-solt-burnett-2023]
-/

@[expose] public section

namespace BeltramaSoltBurnett2023

open Data.Statistics

/-- The two experiments. -/
inductive Experiment where
  /-- Experiment 1: six items per participant in a partial Latin square, written scenarios -/
  | exp1
  /-- Experiment 2: one illustrated item per participant, fully between subjects -/
  | exp2
  deriving DecidableEq, Repr, Fintype

/-- A level of the Precision manipulation. -/
inductive Variant where
  /-- Approximate: a round number under an approximator, *about fifty minutes* -/
  | approximate
  /-- Underspecified: a bare round number, *fifty minutes* -/
  | underspecified
  /-- Precise: a bare sharp number, *forty-nine minutes* -/
  | precise
  deriving DecidableEq, Repr, Fintype

/-- A level of the Scenario manipulation. -/
inductive Scenario where
  /-- For-the-record: testifying for the official record -/
  | forTheRecord
  /-- Persuasive: persuading an interlocutor to act -/
  | persuasive
  /-- Stranger: small talk with a stranger -/
  | stranger
  /-- Bonding: getting to know new colleagues -/
  | bonding
  deriving DecidableEq, Repr, Fintype

/-- A principal component of the ten scales, named for the dimension of social evaluation the
paper takes it to be. -/
inductive Factor where
  /-- Status: factor 1 -/
  | status
  /-- Solidarity: factor 2 -/
  | solidarity
  /-- anti-Solidarity: factor 3 -/
  | antiSolidarity
  deriving DecidableEq, Repr, Fintype

/-- A seven-point evaluation scale. -/
inductive Scale where
  /-- Articulate: the speaker rated articulate -/
  | articulate
  /-- Intelligent: the speaker rated intelligent -/
  | intelligent
  /-- Confident: the speaker rated confident -/
  | confident
  /-- Trustworthy: the speaker rated trustworthy -/
  | trustworthy
  /-- Likable: the speaker rated likable -/
  | likable
  /-- Friendly: the speaker rated friendly -/
  | friendly
  /-- Cool: the speaker rated cool -/
  | cool
  /-- Laid-back: the speaker rated laid-back -/
  | laidBack
  /-- Pedantic: the speaker rated pedantic -/
  | pedantic
  /-- Uptight: the speaker rated uptight -/
  | uptight
  deriving DecidableEq, Repr, Fintype

/-- The approximator of an approximate numeral. -/
inductive Approximator where
  /-- about: *about* -/
  | about
  /-- around: *around* -/
  | around
  deriving DecidableEq, Repr, Fintype

/-- A pair of Precision conditions the paper compares. -/
inductive Comparison where
  /-- Precise vs. Approximate: the precise condition against the approximate one (model row 3) -/
  | preciseApproximate
  /-- Underspecified vs. Approximate: the underspecified condition against the approximate one
  (model row 2) -/
  | underspecifiedApproximate
  /-- Precise vs. Underspecified: the precise condition against the underspecified one (post-hoc) -/
  | preciseUnderspecified
  deriving DecidableEq, Repr, Fintype

/-- The paper's reading of a comparison of the first condition with the second. -/
inductive Verdict where
  /-- rated higher: rated higher -/
  | higher
  /-- rated lower: rated lower -/
  | lower
  /-- trended higher: trended towards being rated higher -/
  | trendHigher
  /-- did not differ: did not differ -/
  | noDifference
  deriving DecidableEq, Repr, Fintype

/-- Participants recruited for Experiment 1, eighteen per list. (p. 812; checked against the page
images.) -/
def exp1Recruited : ℕ := 216

/-- Experiment 1 participants excluded for failing a comprehension check. (pp. 812–813; checked
against the page images.) -/
def exp1Excluded : ℕ := 61

/-- Experimental items of Experiment 1, each in twelve versions. (p. 812; checked against the
page images.) -/
def exp1Items : ℕ := 6

/-- Fillers per list in Experiment 1. (p. 812; checked against the page images.) -/
def exp1Fillers : ℕ := 6

/-- Participants recruited for Experiment 2, eighty per condition. (p. 821; checked against the
page images.) -/
def exp2Recruited : ℕ := 960

/-- Experiment 2 participants excluded for failing the comprehension check. (p. 821; checked
against the page images.) -/
def exp2Excluded : ℕ := 150

/-- Points on each evaluation scale. (p. 812; checked against the page images.) -/
def scalePoints : ℕ := 7

/-- A row of p. 812, (2) (Experiment 1); p. 820, (3) (Experiment 2): the two durations of the
target utterance in each Precision condition, the usual one and the one since the storm. -/
structure Stimulus where
  /-- The usual duration, in minutes. -/
  before : ℕ
  /-- Its approximator, if any. -/
  beforeApproximator : Option Approximator
  /-- The duration since the storm, in minutes. -/
  after : ℕ
  /-- Its approximator, if any. -/
  afterApproximator : Option Approximator
  deriving DecidableEq, Repr

/-- The cells of p. 812, (2) (Experiment 1); p. 820, (3) (Experiment 2), by experiment and
variant; from an experiment; checked against the page images. -/
def stimuli : Experiment → Variant → Stimulus
  | .exp1, .approximate => ⟨20, some .around, 50, some .about⟩
  | .exp1, .underspecified => ⟨20, none, 50, none⟩
  | .exp1, .precise => ⟨21, none, 49, none⟩
  | .exp2, .approximate => ⟨20, some .around, 50, some .about⟩
  | .exp2, .underspecified => ⟨20, none, 50, none⟩
  | .exp2, .precise => ⟨21, none, 49, none⟩

/-- A row of p. 812: the dimension each evaluation scale was included to measure, before the PCA. -/
structure ScaleGroup where
  /-- The dimension it was included to measure. -/
  dimension : Factor
  deriving DecidableEq, Repr

/-- The cells of p. 812, by scale; from an experiment; checked against the page images. -/
def scales : Scale → ScaleGroup
  | .articulate => ⟨.status⟩
  | .intelligent => ⟨.status⟩
  | .confident => ⟨.status⟩
  | .trustworthy => ⟨.status⟩
  | .likable => ⟨.solidarity⟩
  | .friendly => ⟨.solidarity⟩
  | .cool => ⟨.solidarity⟩
  | .laidBack => ⟨.solidarity⟩
  | .pedantic => ⟨.antiSolidarity⟩
  | .uptight => ⟨.antiSolidarity⟩

/-- A row of Table 1, p. 814 (Experiment 1); Table 3, p. 822 (Experiment 2): the varimax-rotated
loading of a scale on a principal component, the paper taking factors 1, 2 and 3 to be
Status, Solidarity and anti-Solidarity. -/
structure Loading where
  /-- The loading. -/
  loading : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 814 (Experiment 1); Table 3, p. 822 (Experiment 2), by experiment
and scale and factor; from an experiment; checked against the page images. -/
def loadings : Experiment → Scale → Factor → Loading
  | .exp1, .articulate, .status => ⟨⟨81, 2⟩⟩
  | .exp1, .articulate, .solidarity => ⟨⟨9, 2⟩⟩
  | .exp1, .articulate, .antiSolidarity => ⟨⟨12, 2⟩⟩
  | .exp1, .intelligent, .status => ⟨⟨79, 2⟩⟩
  | .exp1, .intelligent, .solidarity => ⟨⟨16, 2⟩⟩
  | .exp1, .intelligent, .antiSolidarity => ⟨⟨5, 2⟩⟩
  | .exp1, .confident, .status => ⟨⟨81, 2⟩⟩
  | .exp1, .confident, .solidarity => ⟨⟨15, 2⟩⟩
  | .exp1, .confident, .antiSolidarity => ⟨⟨7, 2⟩⟩
  | .exp1, .trustworthy, .status => ⟨⟨71, 2⟩⟩
  | .exp1, .trustworthy, .solidarity => ⟨⟨33, 2⟩⟩
  | .exp1, .trustworthy, .antiSolidarity => ⟨⟨9, 2⟩⟩
  | .exp1, .likable, .status => ⟨⟨41, 2⟩⟩
  | .exp1, .likable, .solidarity => ⟨⟨74, 2⟩⟩
  | .exp1, .likable, .antiSolidarity => ⟨⟨2, 2⟩⟩
  | .exp1, .friendly, .status => ⟨⟨39, 2⟩⟩
  | .exp1, .friendly, .solidarity => ⟨⟨66, 2⟩⟩
  | .exp1, .friendly, .antiSolidarity => ⟨⟨2, 2⟩⟩
  | .exp1, .cool, .status => ⟨⟨24, 2⟩⟩
  | .exp1, .cool, .solidarity => ⟨⟨80, 2⟩⟩
  | .exp1, .cool, .antiSolidarity => ⟨⟨9, 2⟩⟩
  | .exp1, .laidBack, .status => ⟨⟨9, 2⟩⟩
  | .exp1, .laidBack, .solidarity => ⟨⟨84, 2⟩⟩
  | .exp1, .laidBack, .antiSolidarity => ⟨⟨10, 2⟩⟩
  | .exp1, .pedantic, .status => ⟨⟨8, 2⟩⟩
  | .exp1, .pedantic, .solidarity => ⟨⟨10, 2⟩⟩
  | .exp1, .pedantic, .antiSolidarity => ⟨⟨85, 2⟩⟩
  | .exp1, .uptight, .status => ⟨⟨11, 2⟩⟩
  | .exp1, .uptight, .solidarity => ⟨⟨0, 2⟩⟩
  | .exp1, .uptight, .antiSolidarity => ⟨⟨86, 2⟩⟩
  | .exp2, .articulate, .status => ⟨⟨84, 2⟩⟩
  | .exp2, .articulate, .solidarity => ⟨⟨14, 2⟩⟩
  | .exp2, .articulate, .antiSolidarity => ⟨⟨4, 2⟩⟩
  | .exp2, .intelligent, .status => ⟨⟨81, 2⟩⟩
  | .exp2, .intelligent, .solidarity => ⟨⟨9, 2⟩⟩
  | .exp2, .intelligent, .antiSolidarity => ⟨⟨1, 2⟩⟩
  | .exp2, .confident, .status => ⟨⟨80, 2⟩⟩
  | .exp2, .confident, .solidarity => ⟨⟨3, 2⟩⟩
  | .exp2, .confident, .antiSolidarity => ⟨⟨6, 2⟩⟩
  | .exp2, .trustworthy, .status => ⟨⟨77, 2⟩⟩
  | .exp2, .trustworthy, .solidarity => ⟨⟨28, 2⟩⟩
  | .exp2, .trustworthy, .antiSolidarity => ⟨⟨5, 2⟩⟩
  | .exp2, .likable, .status => ⟨⟨59, 2⟩⟩
  | .exp2, .likable, .solidarity => ⟨⟨66, 2⟩⟩
  | .exp2, .likable, .antiSolidarity => ⟨⟨4, 2⟩⟩
  | .exp2, .friendly, .status => ⟨⟨58, 2⟩⟩
  | .exp2, .friendly, .solidarity => ⟨⟨56, 2⟩⟩
  | .exp2, .friendly, .antiSolidarity => ⟨⟨2, 2⟩⟩
  | .exp2, .cool, .status => ⟨⟨44, 2⟩⟩
  | .exp2, .cool, .solidarity => ⟨⟨67, 2⟩⟩
  | .exp2, .cool, .antiSolidarity => ⟨⟨16, 3⟩⟩
  | .exp2, .laidBack, .status => ⟨⟨10, 2⟩⟩
  | .exp2, .laidBack, .solidarity => ⟨⟨84, 2⟩⟩
  | .exp2, .laidBack, .antiSolidarity => ⟨⟨20, 2⟩⟩
  | .exp2, .pedantic, .status => ⟨⟨3, 2⟩⟩
  | .exp2, .pedantic, .solidarity => ⟨⟨13, 2⟩⟩
  | .exp2, .pedantic, .antiSolidarity => ⟨⟨87, 2⟩⟩
  | .exp2, .uptight, .status => ⟨⟨3, 1⟩⟩
  | .exp2, .uptight, .solidarity => ⟨⟨28, 2⟩⟩
  | .exp2, .uptight, .antiSolidarity => ⟨⟨80, 2⟩⟩

/-- A row of Table 1, p. 814 (Experiment 1); Table 3, p. 822 (Experiment 2): the last column of
the PCA tables, headed Commonalities. -/
structure Commonality where
  /-- The printed value. -/
  commonality : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 814 (Experiment 1); Table 3, p. 822 (Experiment 2), by experiment
and scale; from an experiment; checked against the page images. -/
def commonalities : Experiment → Scale → Commonality
  | .exp1, .articulate => ⟨⟨11, 1⟩⟩
  | .exp1, .intelligent => ⟨⟨11, 1⟩⟩
  | .exp1, .confident => ⟨⟨11, 1⟩⟩
  | .exp1, .trustworthy => ⟨⟨14, 1⟩⟩
  | .exp1, .likable => ⟨⟨16, 1⟩⟩
  | .exp1, .friendly => ⟨⟨16, 1⟩⟩
  | .exp1, .cool => ⟨⟨12, 1⟩⟩
  | .exp1, .laidBack => ⟨⟨11, 1⟩⟩
  | .exp1, .pedantic => ⟨⟨11, 1⟩⟩
  | .exp1, .uptight => ⟨⟨10, 1⟩⟩
  | .exp2, .articulate => ⟨⟨11, 1⟩⟩
  | .exp2, .intelligent => ⟨⟨11, 1⟩⟩
  | .exp2, .confident => ⟨⟨11, 1⟩⟩
  | .exp2, .trustworthy => ⟨⟨14, 1⟩⟩
  | .exp2, .likable => ⟨⟨16, 1⟩⟩
  | .exp2, .friendly => ⟨⟨16, 1⟩⟩
  | .exp2, .cool => ⟨⟨12, 1⟩⟩
  | .exp2, .laidBack => ⟨⟨11, 1⟩⟩
  | .exp2, .pedantic => ⟨⟨11, 1⟩⟩
  | .exp2, .uptight => ⟨⟨10, 1⟩⟩

/-- A row of Table 1, p. 814 (Experiment 1); Table 3, p. 822 (Experiment 2): the variance a
principal component accounts for. -/
structure Variance where
  /-- The sum of squared loadings. -/
  ssLoadings : Decimal
  /-- The proportion of variance. -/
  proportion : Decimal
  /-- The cumulative proportion of variance. -/
  cumulative : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 814 (Experiment 1); Table 3, p. 822 (Experiment 2), by experiment
and factor; from an experiment; checked against the page images. -/
def variance : Experiment → Factor → Variance
  | .exp1, .status => ⟨⟨284, 2⟩, ⟨28, 2⟩, ⟨28, 2⟩⟩
  | .exp1, .solidarity => ⟨⟨251, 2⟩, ⟨25, 2⟩, ⟨53, 2⟩⟩
  | .exp1, .antiSolidarity => ⟨⟨150, 2⟩, ⟨15, 2⟩, ⟨68, 2⟩⟩
  | .exp2, .status => ⟨⟨352, 2⟩, ⟨35, 2⟩, ⟨35, 2⟩⟩
  | .exp2, .solidarity => ⟨⟨211, 2⟩, ⟨21, 2⟩, ⟨56, 2⟩⟩
  | .exp2, .antiSolidarity => ⟨⟨148, 2⟩, ⟨15, 2⟩, ⟨71, 2⟩⟩

/-- A row of pp. 816–817 (Experiment 1); p. 823 (Experiment 2): the mean and standard deviation
of a composite score by Precision condition, across scenarios. -/
structure Rating where
  /-- The mean. -/
  mean : Decimal
  /-- The standard deviation. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The cells of pp. 816–817 (Experiment 1); p. 823 (Experiment 2), by experiment and variant and
factor; from an experiment; checked against the page images. -/
def ratings : Experiment → Variant → Factor → Rating
  | .exp1, .precise, .status => ⟨⟨501, 2⟩, ⟨95, 2⟩⟩
  | .exp1, .approximate, .status => ⟨⟨484, 2⟩, ⟨99, 2⟩⟩
  | .exp1, .underspecified, .status => ⟨⟨496, 2⟩, ⟨99, 2⟩⟩
  | .exp1, .precise, .solidarity => ⟨⟨437, 2⟩, ⟨108, 2⟩⟩
  | .exp1, .approximate, .solidarity => ⟨⟨458, 2⟩, ⟨99, 2⟩⟩
  | .exp1, .underspecified, .solidarity => ⟨⟨449, 2⟩, ⟨100, 2⟩⟩
  | .exp1, .precise, .antiSolidarity => ⟨⟨437, 2⟩, ⟨122, 2⟩⟩
  | .exp1, .approximate, .antiSolidarity => ⟨⟨410, 2⟩, ⟨124, 2⟩⟩
  | .exp1, .underspecified, .antiSolidarity => ⟨⟨419, 2⟩, ⟨124, 2⟩⟩
  | .exp2, .precise, .status => ⟨⟨516, 2⟩, ⟨82, 2⟩⟩
  | .exp2, .approximate, .status => ⟨⟨490, 2⟩, ⟨85, 2⟩⟩
  | .exp2, .underspecified, .status => ⟨⟨506, 2⟩, ⟨73, 2⟩⟩
  | .exp2, .precise, .solidarity => ⟨⟨415, 2⟩, ⟨97, 2⟩⟩
  | .exp2, .approximate, .solidarity => ⟨⟨484, 2⟩, ⟨85, 2⟩⟩
  | .exp2, .underspecified, .solidarity => ⟨⟨460, 2⟩, ⟨90, 2⟩⟩
  | .exp2, .precise, .antiSolidarity => ⟨⟨385, 2⟩, ⟨105, 2⟩⟩
  | .exp2, .approximate, .antiSolidarity => ⟨⟨349, 2⟩, ⟨113, 2⟩⟩
  | .exp2, .underspecified, .antiSolidarity => ⟨⟨359, 2⟩, ⟨114, 2⟩⟩

/-- A row of pp. 816–817 (Experiment 1); p. 823 (Experiment 2): the mean and standard deviation
of a composite score in a Precision × Scenario cell, for the cells the text reports with an
interaction. -/
structure ScenarioRating where
  /-- The experiment. -/
  experiment : Experiment
  /-- The composite score. -/
  factor : Factor
  /-- The scenario. -/
  scenario : Scenario
  /-- The Precision condition. -/
  variant : Variant
  /-- The mean. -/
  mean : Decimal
  /-- The standard deviation. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The 16 rows of pp. 816–817 (Experiment 1); p. 823 (Experiment 2), in the paper's order; from
an experiment; checked against the page images. -/
def scenarioRatings : List ScenarioRating :=
  [⟨.exp1, .status, .forTheRecord, .precise, ⟨513, 2⟩, ⟨102, 2⟩⟩,
   ⟨.exp1, .status, .forTheRecord, .approximate, ⟨474, 2⟩, ⟨97, 2⟩⟩,
   ⟨.exp1, .status, .bonding, .precise, ⟨493, 2⟩, ⟨96, 2⟩⟩,
   ⟨.exp1, .status, .bonding, .approximate, ⟨495, 2⟩, ⟨96, 2⟩⟩,
   ⟨.exp1, .antiSolidarity, .forTheRecord, .approximate, ⟨421, 2⟩, ⟨109, 2⟩⟩,
   ⟨.exp1, .antiSolidarity, .forTheRecord, .underspecified, ⟨420, 2⟩, ⟨115, 2⟩⟩,
   ⟨.exp1, .antiSolidarity, .bonding, .underspecified, ⟨437, 2⟩, ⟨124, 2⟩⟩,
   ⟨.exp1, .antiSolidarity, .bonding, .approximate, ⟨398, 2⟩, ⟨133, 2⟩⟩,
   ⟨.exp2, .status, .forTheRecord, .underspecified, ⟨484, 2⟩, ⟨74, 2⟩⟩,
   ⟨.exp2, .status, .forTheRecord, .precise, ⟨490, 2⟩, ⟨84, 2⟩⟩,
   ⟨.exp2, .status, .persuasive, .precise, ⟨523, 2⟩, ⟨74, 2⟩⟩,
   ⟨.exp2, .status, .persuasive, .underspecified, ⟨498, 2⟩, ⟨81, 2⟩⟩,
   ⟨.exp2, .solidarity, .stranger, .precise, ⟨434, 2⟩, ⟨101, 2⟩⟩,
   ⟨.exp2, .solidarity, .stranger, .underspecified, ⟨478, 2⟩, ⟨77, 2⟩⟩,
   ⟨.exp2, .solidarity, .forTheRecord, .precise, ⟨388, 2⟩, ⟨95, 2⟩⟩,
   ⟨.exp2, .solidarity, .forTheRecord, .underspecified, ⟨389, 2⟩, ⟨71, 2⟩⟩]

/-- A row of Table 2, p. 815 (Experiment 1, mixed effects); Table 4, p. 824 (Experiment 2,
linear): a coefficient of the model of a composite score, simple coded with Approximate and
For-the-record as reference levels and the grand mean as intercept; a row with neither level
is the intercept, with both an interaction. -/
structure Coefficient where
  /-- The experiment. -/
  experiment : Experiment
  /-- The composite score. -/
  factor : Factor
  /-- The Precision level compared with Approximate, if any. -/
  variant : Option Variant
  /-- The Scenario level compared with For-the-record, if any. -/
  scenario : Option Scenario
  /-- The coefficient. -/
  beta : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 72 rows of Table 2, p. 815 (Experiment 1, mixed effects); Table 4, p. 824 (Experiment 2,
linear), in the paper's order; from an experiment; checked against the page images. -/
def coefficients : List Coefficient :=
  [⟨.exp1, .status, none, none, ⟨494, 2⟩, ⟨9, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp1, .status, some .underspecified, none, ⟨10, 2⟩, ⟨5, 2⟩, ⟨.eq, ⟨5, 2⟩⟩⟩,
   ⟨.exp1, .status, some .precise, none, ⟨15, 2⟩, ⟨5, 2⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.exp1, .status, none, some .persuasive, ⟨9, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨15, 2⟩⟩⟩,
   ⟨.exp1, .status, none, some .stranger, ⟨-4, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨52, 2⟩⟩⟩,
   ⟨.exp1, .status, none, some .bonding, ⟨4, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨52, 2⟩⟩⟩,
   ⟨.exp1, .status, some .underspecified, some .persuasive, ⟨-5, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨73, 2⟩⟩⟩,
   ⟨.exp1, .status, some .precise, some .persuasive, ⟨-24, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨15, 2⟩⟩⟩,
   ⟨.exp1, .status, some .underspecified, some .stranger, ⟨-8, 2⟩, ⟨16, 2⟩, ⟨.eq, ⟨60, 2⟩⟩⟩,
   ⟨.exp1, .status, some .precise, some .stranger, ⟨-24, 2⟩, ⟨16, 2⟩, ⟨.eq, ⟨13, 2⟩⟩⟩,
   ⟨.exp1, .status, some .underspecified, some .bonding, ⟨-3, 2⟩, ⟨16, 2⟩, ⟨.eq, ⟨83, 2⟩⟩⟩,
   ⟨.exp1, .status, some .precise, some .bonding, ⟨-38, 2⟩, ⟨15, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, none, none, ⟨447, 2⟩, ⟨9, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp1, .solidarity, some .underspecified, none, ⟨-8, 2⟩, ⟨5, 2⟩, ⟨.eq, ⟨13, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .precise, none, ⟨-19, 2⟩, ⟨5, 2⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, none, some .persuasive, ⟨-6, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨31, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, none, some .stranger, ⟨20, 2⟩, ⟨6, 2⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, none, some .bonding, ⟨3, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨55, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .underspecified, some .persuasive, ⟨4, 2⟩, ⟨18, 2⟩, ⟨.eq, ⟨81, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .precise, some .persuasive, ⟨6, 2⟩, ⟨18, 2⟩, ⟨.eq, ⟨71, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .underspecified, some .stranger, ⟨19, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨25, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .precise, some .stranger, ⟨17, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨32, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .underspecified, some .bonding, ⟨-11, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨52, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, some .precise, some .bonding, ⟨3, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨85, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, none, none, ⟨421, 2⟩, ⟨9, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .underspecified, none, ⟨8, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨17, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .precise, none, ⟨27, 2⟩, ⟨6, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, none, some .persuasive, ⟨-5, 2⟩, ⟨17, 2⟩, ⟨.eq, ⟨45, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, none, some .stranger, ⟨-16, 2⟩, ⟨7, 2⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, none, some .bonding, ⟨-8, 2⟩, ⟨7, 2⟩, ⟨.eq, ⟨28, 2⟩⟩⟩,
   ⟨.exp1,
     .antiSolidarity,
     some .underspecified,
     some .persuasive,
     ⟨22, 2⟩,
     ⟨21, 2⟩,
     ⟨.eq, ⟨28, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .precise, some .persuasive, ⟨0, 2⟩, ⟨21, 2⟩, ⟨.eq, ⟨97, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .underspecified, some .stranger, ⟨27, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨16, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .precise, some .stranger, ⟨17, 2⟩, ⟨20, 2⟩, ⟨.eq, ⟨38, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .underspecified, some .bonding, ⟨47, 2⟩, ⟨20, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, some .precise, some .bonding, ⟨30, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨11, 2⟩⟩⟩,
   ⟨.exp2, .status, none, none, ⟨503, 2⟩, ⟨2, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .status, some .underspecified, none, ⟨16, 2⟩, ⟨6, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .status, some .precise, none, ⟨25, 2⟩, ⟨6, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .status, none, some .persuasive, ⟨37, 2⟩, ⟨7, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .status, none, some .stranger, ⟨50, 2⟩, ⟨7, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .status, none, some .bonding, ⟨36, 2⟩, ⟨7, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .status, some .underspecified, some .persuasive, ⟨-50, 2⟩, ⟨19, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .status, some .precise, some .persuasive, ⟨-31, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨10, 2⟩⟩⟩,
   ⟨.exp2, .status, some .underspecified, some .stranger, ⟨-16, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨40, 2⟩⟩⟩,
   ⟨.exp2, .status, some .precise, some .stranger, ⟨-26, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨18, 2⟩⟩⟩,
   ⟨.exp2, .status, some .underspecified, some .bonding, ⟨-26, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨15, 2⟩⟩⟩,
   ⟨.exp2, .status, some .precise, some .bonding, ⟨-22, 2⟩, ⟨19, 2⟩, ⟨.eq, ⟨23, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, none, none, ⟨446, 2⟩, ⟨3, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .solidarity, some .underspecified, none, ⟨-27, 2⟩, ⟨7, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .solidarity, some .precise, none, ⟨-46, 2⟩, ⟨7, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .solidarity, none, some .persuasive, ⟨21, 2⟩, ⟨8, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, none, some .stranger, ⟨65, 2⟩, ⟨8, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .solidarity, none, some .bonding, ⟨39, 2⟩, ⟨8, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, some .underspecified, some .persuasive, ⟨22, 2⟩, ⟨21, 2⟩, ⟨.eq, ⟨29, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, some .precise, some .persuasive, ⟨14, 2⟩, ⟨21, 2⟩, ⟨.eq, ⟨49, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, some .underspecified, some .stranger, ⟨17, 2⟩, ⟨21, 2⟩, ⟨.eq, ⟨25, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, some .precise, some .stranger, ⟨-17, 2⟩, ⟨22, 2⟩, ⟨.eq, ⟨41, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, some .underspecified, some .bonding, ⟨37, 2⟩, ⟨21, 2⟩, ⟨.eq, ⟨8, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, some .precise, some .bonding, ⟨14, 2⟩, ⟨21, 2⟩, ⟨.eq, ⟨48, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, none, none, ⟨336, 2⟩, ⟨3, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .underspecified, none, ⟨10, 2⟩, ⟨0, 2⟩, ⟨.eq, ⟨28, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .precise, none, ⟨36, 2⟩, ⟨9, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, none, some .persuasive, ⟨-5, 2⟩, ⟨11, 2⟩, ⟨.eq, ⟨7, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, none, some .stranger, ⟨-16, 2⟩, ⟨11, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, none, some .bonding, ⟨-8, 2⟩, ⟨10, 2⟩, ⟨.eq, ⟨38, 2⟩⟩⟩,
   ⟨.exp2,
     .antiSolidarity,
     some .underspecified,
     some .persuasive,
     ⟨22, 2⟩,
     ⟨27, 2⟩,
     ⟨.eq, ⟨65, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .precise, some .persuasive, ⟨0, 2⟩, ⟨27, 2⟩, ⟨.eq, ⟨99, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .underspecified, some .stranger, ⟨27, 2⟩, ⟨27, 2⟩, ⟨.eq, ⟨70, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .precise, some .stranger, ⟨17, 2⟩, ⟨27, 2⟩, ⟨.eq, ⟨34, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .underspecified, some .bonding, ⟨47, 2⟩, ⟨26, 2⟩, ⟨.eq, ⟨95, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, some .precise, some .bonding, ⟨30, 2⟩, ⟨26, 2⟩, ⟨.eq, ⟨26, 2⟩⟩⟩]

/-- A row of pp. 816–817 (Experiment 1); p. 823 (Experiment 2): the paper's reading of a
comparison of two Precision conditions on a composite score, across scenarios. -/
structure VerdictRow where
  /-- The paper's reading of it. -/
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The cells of pp. 816–817 (Experiment 1); p. 823 (Experiment 2), by experiment and factor and
comparison; from an experiment; checked against the page images. -/
def verdicts : Experiment → Factor → Comparison → VerdictRow
  | .exp1, .status, .preciseApproximate => ⟨.higher⟩
  | .exp1, .status, .underspecifiedApproximate => ⟨.trendHigher⟩
  | .exp1, .status, .preciseUnderspecified => ⟨.noDifference⟩
  | .exp1, .solidarity, .preciseApproximate => ⟨.lower⟩
  | .exp1, .solidarity, .underspecifiedApproximate => ⟨.noDifference⟩
  | .exp1, .solidarity, .preciseUnderspecified => ⟨.noDifference⟩
  | .exp1, .antiSolidarity, .preciseApproximate => ⟨.higher⟩
  | .exp1, .antiSolidarity, .underspecifiedApproximate => ⟨.noDifference⟩
  | .exp1, .antiSolidarity, .preciseUnderspecified => ⟨.higher⟩
  | .exp2, .status, .preciseApproximate => ⟨.higher⟩
  | .exp2, .status, .underspecifiedApproximate => ⟨.higher⟩
  | .exp2, .status, .preciseUnderspecified => ⟨.noDifference⟩
  | .exp2, .solidarity, .preciseApproximate => ⟨.lower⟩
  | .exp2, .solidarity, .underspecifiedApproximate => ⟨.lower⟩
  | .exp2, .solidarity, .preciseUnderspecified => ⟨.lower⟩
  | .exp2, .antiSolidarity, .preciseApproximate => ⟨.higher⟩
  | .exp2, .antiSolidarity, .underspecifiedApproximate => ⟨.noDifference⟩
  | .exp2, .antiSolidarity, .preciseUnderspecified => ⟨.higher⟩

/-- A row of pp. 816–817 (Experiment 1); p. 823 (Experiment 2): the post-hoc comparison of the
precise with the underspecified condition. -/
structure PostHoc where
  /-- The experiment. -/
  experiment : Experiment
  /-- The composite score. -/
  factor : Factor
  /-- The t statistic. -/
  t : Decimal
  /-- Its degrees of freedom. -/
  df : ℕ
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 6 rows of pp. 816–817 (Experiment 1); p. 823 (Experiment 2), in the paper's order; from
an experiment; checked against the page images. -/
def preciseVsUnderspecified : List PostHoc :=
  [⟨.exp1, .status, ⟨100, 2⟩, 759, ⟨.eq, ⟨57, 2⟩⟩⟩,
   ⟨.exp1, .solidarity, ⟨189, 2⟩, 759, ⟨.eq, ⟨14, 2⟩⟩⟩,
   ⟨.exp1, .antiSolidarity, ⟨276, 2⟩, 759, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .status, ⟨131, 2⟩, 798, ⟨.eq, ⟨34, 2⟩⟩⟩,
   ⟨.exp2, .solidarity, ⟨254, 2⟩, 798, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .antiSolidarity, ⟨-279, 2⟩, 798, ⟨.lt, ⟨5, 2⟩⟩⟩]

end BeltramaSoltBurnett2023
