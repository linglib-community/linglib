module

public import Linglib.Data.Statistics.Schema

/-!
# DenicEtAl2021: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/DenicEtAl2021.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Four inference-rating experiments on Amazon Mechanical Turk. A premise and a conclusion differ in a
superset and a subset verb phrase (see birds, see doves) inside one of ten environments, and
participants rated on a continuous bar how far the conclusion follows. The premise carried a
negative polarity item, the positive polarity item some, or none. A directional rating keeps a
subset to superset rating and reverses a superset to subset one (100 minus the rating). Effects are
Bayesian mixed-model coefficients with 95% credible intervals and the posterior probability of the
reported sign.

## Raw data

* <https://github.com/milicaden/polarity-items-monotonicity-inferences>: The material, data,
  analysis script and model output, as linked in §2.

## References

* [denic-homer-rothschild-chemla-2021]
-/

@[expose] public section

namespace DenicEtAl2021

open Data.Statistics

/-- An experiment of the paper. -/
inductive Experiment where
  /-- Experiment 1: polarity items in the premise only -/
  | exp1
  /-- Experiment 2: a polarity item in the premise repeated in the conclusion -/
  | exp2
  /-- Experiment 3: Experiment 1 with the doubly negative environments added -/
  | exp3
  /-- Experiment 4: Experiment 3 with the polarity item condition of an environment between
  participants -/
  | exp4
  deriving DecidableEq, Repr, Fintype

/-- The class of an environment. -/
inductive Monotonicity where
  /-- UE: upward entailing -/
  | ue
  /-- DE: downward entailing -/
  | de
  /-- NM: non-monotone -/
  | nm
  /-- DN: doubly negative, a downward-entailing operator inside another -/
  | dn
  deriving DecidableEq, Repr, Fintype

/-- An environment the verb phrase of a premise and its conclusion occurs in. -/
inductive Environment where
  /-- positive: The purple alien saw birds. -/
  | positive
  /-- Every: Every alien saw birds. -/
  | every
  /-- Many: Many aliens saw birds. -/
  | many
  /-- negative: The purple alien didn't see birds. -/
  | negative
  /-- No: No alien saw birds. -/
  | no
  /-- Few: Few aliens saw birds. -/
  | few
  /-- Exactly 12: Exactly 12 aliens saw birds. -/
  | exactly12
  /-- Only 12: Only 12 aliens saw birds. -/
  | only12
  /-- Every-not: Every alien who did not see birds is hairy. -/
  | everyNot
  /-- No-without: No alien spent a year without seeing birds. -/
  | noWithout
  deriving DecidableEq, Repr, Fintype

/-- The order of the verb phrases of the premise and the conclusion. -/
inductive Direction where
  /-- superset/subset: the superset verb phrase in the premise, the subset one in the conclusion -/
  | supersetToSubset
  /-- subset/superset: the subset verb phrase in the premise, the superset one in the conclusion -/
  | subsetToSuperset
  deriving DecidableEq, Repr, Fintype

/-- The polarity item condition of a premise. -/
inductive PI where
  /-- NPI: a negative polarity item, any or at all -/
  | npi
  /-- PPI: the positive polarity item some -/
  | ppi
  /-- no PI: no polarity item -/
  | noPI
  deriving DecidableEq, Repr, Fintype

/-- A rating of one inference direction. -/
inductive Rating where
  /-- UE-rating: the rating of a subset to superset inference -/
  | ueRating
  /-- DE-rating: the rating of a superset to subset inference -/
  | deRating
  deriving DecidableEq, Repr, Fintype

/-- The side of zero whose posterior probability is reported. -/
inductive Tail where
  /-- P(β < 0): the probability that the coefficient is negative -/
  | belowZero
  /-- P(β > 0): the probability that the coefficient is positive -/
  | aboveZero
  deriving DecidableEq, Repr, Fintype

/-- Superset and subset verb phrase pairs, Experiments 1 to 3. (§3.1.2, p. 3; checked against the
page images.) -/
def verbPhrasePairs : ℕ := 12

/-- Superset and subset verb phrase pairs, Experiment 4. (§7.1.2, p. 7; checked against the page
images.) -/
def verbPhrasePairsExp4 : ℕ := 10

/-- Responses faster than this many seconds were removed. (§3.2, p. 4; checked against the page
images.) -/
def minResponseTime : Decimal := ⟨14, 1⟩

/-- Responses slower than this many seconds were removed. (§3.2, p. 4; checked against the page
images.) -/
def maxResponseTime : Decimal := ⟨10, 0⟩

/-- A row of §3.1.2 and (14)–(21), pp. 3–4; (23)–(24), p. 6: the class of each environment. -/
structure EnvironmentRow where
  /-- Its class. -/
  monotonicity : Monotonicity
  deriving DecidableEq, Repr

/-- The cells of §3.1.2 and (14)–(21), pp. 3–4; (23)–(24), p. 6, by environment; from an
experiment; checked against the page images. -/
def environments : Environment → EnvironmentRow
  | .positive => ⟨.ue⟩
  | .every => ⟨.ue⟩
  | .many => ⟨.ue⟩
  | .negative => ⟨.de⟩
  | .no => ⟨.de⟩
  | .few => ⟨.de⟩
  | .exactly12 => ⟨.nm⟩
  | .only12 => ⟨.nm⟩
  | .everyNot => ⟨.dn⟩
  | .noWithout => ⟨.dn⟩

/-- A row of §3.1.3, p. 4; §4.1.3, p. 5; §6.1.3, pp. 6–7; §7.1.3, p. 7: the participants of an
experiment, recruited on Amazon Mechanical Turk. -/
structure Participants where
  /-- Recruited. -/
  recruited : ℕ
  /-- Recruited and female. -/
  female : ℕ
  /-- Excluded as not native speakers of English. -/
  nonNative : ℕ
  /-- Further excluded for not rating the upward and downward inferences higher in the upward and
  downward entailing environments respectively. -/
  monotonicityCheck : ℕ
  /-- Kept for the analysis. -/
  kept : ℕ
  /-- Kept and female. -/
  keptFemale : ℕ
  deriving DecidableEq, Repr

/-- The cells of §3.1.3, p. 4; §4.1.3, p. 5; §6.1.3, pp. 6–7; §7.1.3, p. 7, by experiment; from
an experiment; checked against the page images. -/
def participants : Experiment → Participants
  | .exp1 => ⟨75, 38, 1, 8, 66, 32⟩
  | .exp2 => ⟨72, 35, 1, 7, 64, 28⟩
  | .exp3 => ⟨112, 69, 7, 13, 92, 53⟩
  | .exp4 => ⟨81, 43, 4, 6, 71, 36⟩

/-- A row of §3.2, p. 4; §4.2, p. 5; §6.2, p. 7; §7.2, p. 7: the responses removed for their
response time, in percent of the data. -/
structure ResponseExclusion where
  /-- Faster than the minimum response time. -/
  fast : Decimal
  /-- Slower than the maximum response time. -/
  slow : Decimal
  deriving DecidableEq, Repr

/-- The cells of §3.2, p. 4; §4.2, p. 5; §6.2, p. 7; §7.2, p. 7, by experiment; from an
experiment; checked against the page images. -/
def responseExclusions : Experiment → ResponseExclusion
  | .exp1 => ⟨⟨1, 0⟩, ⟨9, 0⟩⟩
  | .exp2 => ⟨⟨6, 0⟩, ⟨7, 0⟩⟩
  | .exp3 => ⟨⟨4, 0⟩, ⟨13, 0⟩⟩
  | .exp4 => ⟨⟨8, 0⟩, ⟨10, 0⟩⟩

/-- A row of §3.2, p. 4; §4.2, p. 5; §6.2, p. 7; §7.2, p. 7: the mean ratings of the three
training items (11)–(13), in percent. -/
structure Training where
  /-- The clearly valid inference (11). -/
  valid : Decimal
  /-- The clearly invalid inference (12). -/
  invalid : Decimal
  /-- The intermediate inference (13). -/
  intermediate : Decimal
  deriving DecidableEq, Repr

/-- The cells of §3.2, p. 4; §4.2, p. 5; §6.2, p. 7; §7.2, p. 7, by experiment; from an
experiment; checked against the page images. -/
def training : Experiment → Training
  | .exp1 => ⟨⟨93, 0⟩, ⟨9, 0⟩, ⟨68, 0⟩⟩
  | .exp2 => ⟨⟨93, 0⟩, ⟨9, 0⟩, ⟨62, 0⟩⟩
  | .exp3 => ⟨⟨92, 0⟩, ⟨83, 1⟩, ⟨67, 0⟩⟩
  | .exp4 => ⟨⟨895, 1⟩, ⟨82, 1⟩, ⟨607, 1⟩⟩

/-- A row of §3.2, p. 4: the mean ratings of Experiment 1 by environment class, whatever the
polarity item, in percent. -/
structure ClassRating where
  /-- The class. -/
  monotonicity : Monotonicity
  /-- The rated direction. -/
  rating : Rating
  /-- The mean. -/
  mean : Decimal
  /-- The standard deviation. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The 6 rows of §3.2, p. 4, in the paper's order; from an experiment; checked against the page
images. -/
def classRatings : List ClassRating :=
  [⟨.ue, .ueRating, ⟨897, 1⟩, ⟨1303, 2⟩⟩,
   ⟨.ue, .deRating, ⟨296, 1⟩, ⟨162, 1⟩⟩,
   ⟨.de, .deRating, ⟨812, 1⟩, ⟨152, 1⟩⟩,
   ⟨.de, .ueRating, ⟨319, 1⟩, ⟨199, 1⟩⟩,
   ⟨.nm, .deRating, ⟨277, 1⟩, ⟨175, 1⟩⟩,
   ⟨.nm, .ueRating, ⟨447, 1⟩, ⟨263, 1⟩⟩]

/-- A row of §3.2, p. 4; §4.2, p. 6; §6.2, p. 7; §7.2, p. 8: the mean directional ratings by
polarity item condition, in percent. -/
structure DirectionalMean where
  /-- The experiment. -/
  experiment : Experiment
  /-- The class. -/
  monotonicity : Monotonicity
  /-- The polarity item condition. -/
  pi : PI
  /-- The mean. -/
  mean : Decimal
  /-- The standard deviation. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The 18 rows of §3.2, p. 4; §4.2, p. 6; §6.2, p. 7; §7.2, p. 8, in the paper's order; from an
experiment; checked against the page images. -/
def directionalMeans : List DirectionalMean :=
  [⟨.exp1, .nm, .noPI, ⟨60, 0⟩, ⟨117, 1⟩⟩,
   ⟨.exp1, .nm, .ppi, ⟨597, 1⟩, ⟨122, 1⟩⟩,
   ⟨.exp1, .nm, .npi, ⟨553, 1⟩, ⟨112, 1⟩⟩,
   ⟨.exp2, .nm, .noPI, ⟨592, 1⟩, ⟨149, 1⟩⟩,
   ⟨.exp2, .nm, .ppi, ⟨601, 1⟩, ⟨141, 1⟩⟩,
   ⟨.exp2, .nm, .npi, ⟨547, 1⟩, ⟨125, 1⟩⟩,
   ⟨.exp3, .nm, .npi, ⟨559, 1⟩, ⟨134, 1⟩⟩,
   ⟨.exp3, .nm, .ppi, ⟨579, 1⟩, ⟨14, 0⟩⟩,
   ⟨.exp3, .nm, .noPI, ⟨571, 1⟩, ⟨133, 1⟩⟩,
   ⟨.exp3, .dn, .npi, ⟨537, 1⟩, ⟨168, 1⟩⟩,
   ⟨.exp3, .dn, .ppi, ⟨618, 1⟩, ⟨144, 1⟩⟩,
   ⟨.exp3, .dn, .noPI, ⟨569, 1⟩, ⟨147, 1⟩⟩,
   ⟨.exp4, .nm, .npi, ⟨563, 1⟩, ⟨116, 1⟩⟩,
   ⟨.exp4, .nm, .ppi, ⟨564, 1⟩, ⟨111, 1⟩⟩,
   ⟨.exp4, .nm, .noPI, ⟨593, 1⟩, ⟨153, 1⟩⟩,
   ⟨.exp4, .dn, .npi, ⟨526, 1⟩, ⟨252, 1⟩⟩,
   ⟨.exp4, .dn, .ppi, ⟨616, 1⟩, ⟨174, 1⟩⟩,
   ⟨.exp4, .dn, .noPI, ⟨563, 1⟩, ⟨224, 1⟩⟩]

/-- A row of §3.4, p. 5; §4.3, p. 6; §6.3, p. 7; §7.3, p. 8; §8.1, p. 8: the effect of a polarity
item against none on the directional ratings of a class, by experiment and in the meta-
analysis over all four. -/
structure PIEffect where
  /-- The experiment, none for the meta-analysis. -/
  experiment : Option Experiment
  /-- The class. -/
  monotonicity : Monotonicity
  /-- The polarity item. -/
  pi : PI
  /-- The posterior estimate E(μ). -/
  estimate : Decimal
  /-- The lower end of the 95% credible interval. -/
  ciLow : Decimal
  /-- The upper end of the 95% credible interval. -/
  ciHigh : Decimal
  /-- The side of zero whose posterior probability is reported. -/
  tail : Tail
  /-- That posterior probability. -/
  posterior : Decimal
  deriving DecidableEq, Repr

/-- The 16 rows of §3.4, p. 5; §4.3, p. 6; §6.3, p. 7; §7.3, p. 8; §8.1, p. 8, in the paper's
order; from an experiment; checked against the page images. -/
def piEffects : List PIEffect :=
  [⟨some .exp1, .nm, .npi, ⟨-218, 2⟩, ⟨-337, 2⟩, ⟨-1, 0⟩, .belowZero, ⟨999, 3⟩⟩,
   ⟨some .exp1, .nm, .ppi, ⟨9, 2⟩, ⟨-123, 2⟩, ⟨140, 2⟩, .aboveZero, ⟨552, 3⟩⟩,
   ⟨some .exp2, .nm, .npi, ⟨-225, 2⟩, ⟨-348, 2⟩, ⟨-102, 2⟩, .belowZero, ⟨999, 3⟩⟩,
   ⟨some .exp2, .nm, .ppi, ⟨63, 2⟩, ⟨-64, 2⟩, ⟨192, 2⟩, .aboveZero, ⟨84, 2⟩⟩,
   ⟨some .exp3, .nm, .npi, ⟨-111, 2⟩, ⟨-235, 2⟩, ⟨11, 2⟩, .belowZero, ⟨965, 3⟩⟩,
   ⟨some .exp3, .nm, .ppi, ⟨59, 2⟩, ⟨-42, 2⟩, ⟨159, 2⟩, .aboveZero, ⟨88, 2⟩⟩,
   ⟨some .exp3, .dn, .npi, ⟨-85, 2⟩, ⟨-227, 2⟩, ⟨59, 2⟩, .belowZero, ⟨887, 3⟩⟩,
   ⟨some .exp3, .dn, .ppi, ⟨206, 2⟩, ⟨77, 2⟩, ⟨338, 2⟩, .aboveZero, ⟨998, 3⟩⟩,
   ⟨some .exp4, .nm, .npi, ⟨-164, 2⟩, ⟨-308, 2⟩, ⟨-19, 2⟩, .belowZero, ⟨984, 3⟩⟩,
   ⟨some .exp4, .nm, .ppi, ⟨-1, 0⟩, ⟨-254, 2⟩, ⟨55, 2⟩, .aboveZero, ⟨104, 3⟩⟩,
   ⟨some .exp4, .dn, .npi, ⟨-272, 2⟩, ⟨-645, 2⟩, ⟨109, 2⟩, .belowZero, ⟨924, 3⟩⟩,
   ⟨some .exp4, .dn, .ppi, ⟨192, 2⟩, ⟨-190, 2⟩, ⟨566, 2⟩, .aboveZero, ⟨838, 3⟩⟩,
   ⟨none, .nm, .npi, ⟨-173, 2⟩, ⟨-234, 2⟩, ⟨-113, 2⟩, .belowZero, ⟨999, 3⟩⟩,
   ⟨none, .nm, .ppi, ⟨26, 2⟩, ⟨-32, 2⟩, ⟨86, 2⟩, .aboveZero, ⟨817, 3⟩⟩,
   ⟨none, .dn, .npi, ⟨-113, 2⟩, ⟨-242, 2⟩, ⟨15, 2⟩, .belowZero, ⟨96, 2⟩⟩,
   ⟨none, .dn, .ppi, ⟨202, 2⟩, ⟨88, 2⟩, ⟨316, 2⟩, .aboveZero, ⟨999, 3⟩⟩]

/-- A row of Table 1, p. 9: the effect of a polarity item against none on one rating of a class,
pooled over the four experiments, in Table 1. -/
structure RatingEffect where
  /-- The class. -/
  monotonicity : Monotonicity
  /-- The polarity item. -/
  pi : PI
  /-- The rating. -/
  rating : Rating
  /-- The mean rating with the item, in percent. -/
  meanPI : Decimal
  /-- Its standard deviation. -/
  sdPI : Decimal
  /-- The mean rating without a polarity item, in percent. -/
  meanNoPI : Decimal
  /-- Its standard deviation. -/
  sdNoPI : Decimal
  /-- The posterior estimate E(μ). -/
  estimate : Decimal
  /-- The lower end of the 95% credible interval. -/
  ciLow : Decimal
  /-- The upper end of the 95% credible interval. -/
  ciHigh : Decimal
  /-- The side of zero whose posterior probability is reported. -/
  tail : Tail
  /-- That posterior probability. -/
  posterior : Decimal
  deriving DecidableEq, Repr

/-- The 8 rows of Table 1, p. 9, in the paper's order; from an experiment; checked against the
page images. -/
def ratingEffects : List RatingEffect :=
  [⟨.nm,
     .npi,
     .ueRating,
     ⟨397, 1⟩,
     ⟨263, 1⟩,
     ⟨454, 1⟩,
     ⟨286, 1⟩,
     ⟨-254, 2⟩,
     ⟨-351, 2⟩,
     ⟨-159, 2⟩,
     .belowZero,
     ⟨1, 0⟩⟩,
   ⟨.nm,
     .npi,
     .deRating,
     ⟨292, 1⟩,
     ⟨207, 1⟩,
     ⟨278, 1⟩,
     ⟨199, 1⟩,
     ⟨93, 2⟩,
     ⟨7, 2⟩,
     ⟨181, 2⟩,
     .aboveZero,
     ⟨982, 3⟩⟩,
   ⟨.dn,
     .npi,
     .ueRating,
     ⟨527, 1⟩,
     ⟨241, 1⟩,
     ⟨549, 1⟩,
     ⟨24, 0⟩,
     ⟨-115, 2⟩,
     ⟨-298, 2⟩,
     ⟨63, 2⟩,
     .belowZero,
     ⟨903, 3⟩⟩,
   ⟨.dn,
     .npi,
     .deRating,
     ⟨4439, 2⟩,
     ⟨255, 1⟩,
     ⟨414, 1⟩,
     ⟨237, 1⟩,
     ⟨139, 2⟩,
     ⟨-22, 2⟩,
     ⟨3, 0⟩,
     .aboveZero,
     ⟨956, 3⟩⟩,
   ⟨.nm,
     .ppi,
     .ueRating,
     ⟨462, 1⟩,
     ⟨279, 1⟩,
     ⟨454, 1⟩,
     ⟨286, 1⟩,
     ⟨92, 2⟩,
     ⟨-5, 2⟩,
     ⟨189, 2⟩,
     .aboveZero,
     ⟨97, 2⟩⟩,
   ⟨.nm,
     .ppi,
     .deRating,
     ⟨286, 1⟩,
     ⟨206, 1⟩,
     ⟨278, 1⟩,
     ⟨199, 1⟩,
     ⟨24, 2⟩,
     ⟨-40, 2⟩,
     ⟨88, 2⟩,
     .belowZero,
     ⟨227, 3⟩⟩,
   ⟨.dn,
     .ppi,
     .ueRating,
     ⟨596, 1⟩,
     ⟨226, 1⟩,
     ⟨549, 1⟩,
     ⟨24, 0⟩,
     ⟨203, 2⟩,
     ⟨45, 2⟩,
     ⟨359, 2⟩,
     .aboveZero,
     ⟨993, 3⟩⟩,
   ⟨.dn,
     .ppi,
     .deRating,
     ⟨367, 1⟩,
     ⟨21, 0⟩,
     ⟨414, 1⟩,
     ⟨237, 1⟩,
     ⟨-21, 1⟩,
     ⟨-374, 2⟩,
     ⟨-45, 2⟩,
     .belowZero,
     ⟨993, 3⟩⟩]

/-- A row of §8.3, p. 9: the difference between two classes in the effect of a polarity item on
directional ratings, the first class against the second. -/
structure Interaction where
  /-- The polarity item. -/
  pi : PI
  /-- The class whose effect is compared. -/
  first : Monotonicity
  /-- The class it is compared with. -/
  second : Monotonicity
  /-- The posterior estimate E(μ). -/
  estimate : Decimal
  /-- The lower end of the 95% credible interval. -/
  ciLow : Decimal
  /-- The upper end of the 95% credible interval. -/
  ciHigh : Decimal
  /-- The side of zero whose posterior probability is reported. -/
  tail : Tail
  /-- That posterior probability. -/
  posterior : Decimal
  deriving DecidableEq, Repr

/-- The 6 rows of §8.3, p. 9, in the paper's order; from an experiment; checked against the page
images. -/
def interactions : List Interaction :=
  [⟨.npi, .nm, .de, ⟨-56, 2⟩, ⟨-106, 2⟩, ⟨-2, 2⟩, .belowZero, ⟨977, 3⟩⟩,
   ⟨.npi, .dn, .de, ⟨-79, 2⟩, ⟨-149, 2⟩, ⟨-8, 2⟩, .belowZero, ⟨987, 3⟩⟩,
   ⟨.ppi, .nm, .ue, ⟨-1, 2⟩, ⟨-47, 2⟩, ⟨43, 2⟩, .aboveZero, ⟨475, 3⟩⟩,
   ⟨.ppi, .dn, .ue, ⟨115, 2⟩, ⟨69, 2⟩, ⟨162, 2⟩, .aboveZero, ⟨999, 3⟩⟩,
   ⟨.npi, .nm, .dn, ⟨14, 2⟩, ⟨-48, 2⟩, ⟨76, 2⟩, .belowZero, ⟨329, 3⟩⟩,
   ⟨.ppi, .dn, .nm, ⟨115, 2⟩, ⟨52, 2⟩, ⟨177, 2⟩, .aboveZero, ⟨999, 3⟩⟩]

/-- A row of Appendix A, Table A1, p. 13: the mean ratings of each class over the four
experiments, whatever the polarity item, in percent, Table A1. -/
structure ClassMean where
  /-- The mean DE-rating. -/
  meanDE : Decimal
  /-- Its standard deviation. -/
  sdDE : Decimal
  /-- The mean UE-rating. -/
  meanUE : Decimal
  /-- Its standard deviation. -/
  sdUE : Decimal
  deriving DecidableEq, Repr

/-- The cells of Appendix A, Table A1, p. 13, by monotonicity; from an experiment; checked
against the page images. -/
def classMeans : Monotonicity → ClassMean
  | .ue => ⟨⟨304, 1⟩, ⟨189, 1⟩, ⟨872, 1⟩, ⟨15, 0⟩⟩
  | .de => ⟨⟨784, 1⟩, ⟨182, 1⟩, ⟨338, 1⟩, ⟨212, 1⟩⟩
  | .nm => ⟨⟨285, 1⟩, ⟨204, 1⟩, ⟨438, 1⟩, ⟨278, 1⟩⟩
  | .dn => ⟨⟨409, 1⟩, ⟨237, 1⟩, ⟨556, 1⟩, ⟨237, 1⟩⟩

/-- A row of Appendix A, p. 13: the difference in one rating between two classes, the first
against the second, pooled over the four experiments. -/
structure ClassContrast where
  /-- The rating. -/
  rating : Rating
  /-- The class rated lower by the estimate's sign. -/
  first : Monotonicity
  /-- The class it is compared with. -/
  second : Monotonicity
  /-- The posterior estimate E(μ). -/
  estimate : Decimal
  /-- The lower end of the 95% credible interval. -/
  ciLow : Decimal
  /-- The upper end of the 95% credible interval. -/
  ciHigh : Decimal
  /-- The side of zero whose posterior probability is reported. -/
  tail : Tail
  /-- That posterior probability. -/
  posterior : Decimal
  deriving DecidableEq, Repr

/-- The 6 rows of Appendix A, p. 13, in the paper's order; from an experiment; checked against
the page images. -/
def classContrasts : List ClassContrast :=
  [⟨.deRating, .nm, .ue, ⟨-96, 2⟩, ⟨-156, 2⟩, ⟨-38, 2⟩, .belowZero, ⟨999, 3⟩⟩,
   ⟨.deRating, .ue, .dn, ⟨-558, 2⟩, ⟨-668, 2⟩, ⟨-447, 2⟩, .belowZero, ⟨1, 0⟩⟩,
   ⟨.deRating, .dn, .de, ⟨-19, 0⟩, ⟨-2075, 2⟩, ⟨-1731, 2⟩, .belowZero, ⟨1, 0⟩⟩,
   ⟨.ueRating, .de, .nm, ⟨-511, 2⟩, ⟨-621, 2⟩, ⟨-405, 2⟩, .belowZero, ⟨1, 0⟩⟩,
   ⟨.ueRating, .nm, .dn, ⟨-630, 2⟩, ⟨-819, 2⟩, ⟨-440, 2⟩, .belowZero, ⟨1, 0⟩⟩,
   ⟨.ueRating, .dn, .ue, ⟨-1528, 2⟩, ⟨-1655, 2⟩, ⟨-1399, 2⟩, .belowZero, ⟨1, 0⟩⟩]

/-- A row of Appendix B, p. 13: the difference between the two environments of a class in the
effect of a polarity item on directional ratings, pooled over the four experiments. -/
structure InstanceInteraction where
  /-- The polarity item. -/
  pi : PI
  /-- The environment whose effect is compared. -/
  first : Environment
  /-- The environment it is compared with. -/
  second : Environment
  /-- The posterior estimate E(μ). -/
  estimate : Decimal
  /-- The lower end of the 95% credible interval. -/
  ciLow : Decimal
  /-- The upper end of the 95% credible interval. -/
  ciHigh : Decimal
  /-- The side of zero whose posterior probability is reported. -/
  tail : Tail
  /-- That posterior probability. -/
  posterior : Decimal
  deriving DecidableEq, Repr

/-- The 4 rows of Appendix B, p. 13, in the paper's order; from an experiment; checked against
the page images. -/
def instanceInteractions : List InstanceInteraction :=
  [⟨.npi,  -- The paragraph headed NPIs in NM speaks of the presence of PPIs.
     .exactly12,
     .only12,
     ⟨-51, 2⟩,
     ⟨-110, 2⟩,
     ⟨9, 2⟩,
     .belowZero,
     ⟨954, 3⟩⟩,
   ⟨.ppi,  -- The paragraph headed PPIs in NM speaks of the presence of NPIs.
     .exactly12,
     .only12,
     ⟨-6, 2⟩,
     ⟨-67, 2⟩,
     ⟨53, 2⟩,
     .aboveZero,
     ⟨419, 3⟩⟩,
   ⟨.npi, .everyNot, .noWithout, ⟨71, 2⟩, ⟨-55, 2⟩, ⟨196, 2⟩, .belowZero, ⟨131, 3⟩⟩,
   ⟨.ppi, .everyNot, .noWithout, ⟨86, 2⟩, ⟨-56, 2⟩, ⟨223, 2⟩, .aboveZero, ⟨896, 3⟩⟩]

/-- A row of Appendix B, p. 14: the effect of a polarity item against none on the directional
ratings of one environment, pooled over the four experiments. -/
structure InstanceEffect where
  /-- The polarity item. -/
  pi : PI
  /-- The environment. -/
  environment : Environment
  /-- The posterior estimate E(μ). -/
  estimate : Decimal
  /-- The lower end of the 95% credible interval. -/
  ciLow : Decimal
  /-- The upper end of the 95% credible interval. -/
  ciHigh : Decimal
  /-- The side of zero whose posterior probability is reported. -/
  tail : Tail
  /-- That posterior probability. -/
  posterior : Decimal
  deriving DecidableEq, Repr

/-- The 4 rows of Appendix B, p. 14, in the paper's order; from an experiment; checked against
the page images. -/
def instanceEffects : List InstanceEffect :=
  [⟨.npi, .exactly12, ⟨-215, 2⟩, ⟨-297, 2⟩, ⟨-132, 2⟩, .belowZero, ⟨1, 0⟩⟩,
   ⟨.npi, .only12, ⟨-126, 2⟩, ⟨-214, 2⟩, ⟨-38, 2⟩, .belowZero, ⟨996, 3⟩⟩,
   ⟨.ppi, .everyNot, ⟨292, 2⟩, ⟨112, 2⟩, ⟨472, 2⟩, .aboveZero, ⟨998, 3⟩⟩,
   ⟨.ppi, .noWithout, ⟨119, 2⟩, ⟨-46, 2⟩, ⟨284, 2⟩, .aboveZero, ⟨924, 3⟩⟩]

end DenicEtAl2021
