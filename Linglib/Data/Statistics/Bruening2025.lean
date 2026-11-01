module

public import Linglib.Data.Statistics.Schema

/-!
# Bruening2025: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Bruening2025.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Three acceptability surveys on Amazon Mechanical Turk, rated on a scale from 1 (extremely unnatural)
to 5 (extremely natural). Experiment 1a compared non-ly adverbs and adjectives before a noun,
Experiment 1b a clause alone and a clause coordinated with a noun phrase where only noun phrases are
selected, the two serving as each other's fillers; Experiment 2 repeated 1a with one-replacement,
which rules out a compound parse.

## References

* [bruening-2025]
-/

@[expose] public section

namespace Bruening2025

open Data.Statistics

/-- The scale a statistic is reported on. -/
inductive Scale where
  /-- raw: the ratings on the 1-to-5 scale -/
  | raw
  /-- z: the ratings z-scored per participant -/
  | z
  deriving DecidableEq, Repr, Fintype

/-- The conditions of Experiment 1a. -/
inductive Exp1aCondition where
  /-- Control: the grammatical fillers -/
  | control
  /-- Ungrammatical: the ungrammatical fillers -/
  | ungrammatical
  /-- Adjective: an adjective before the noun, the current vice president -/
  | adjective
  /-- Adverb: a non-ly adverb before the noun, the now vice president -/
  | adverb
  deriving DecidableEq, Repr, Fintype

/-- The conditions of Experiment 2. -/
inductive Exp2Condition where
  /-- Filler: Grammatical: the grammatical fillers -/
  | grammaticalFiller
  /-- Filler: Ungrammatical: the ungrammatical fillers -/
  | ungrammaticalFiller
  /-- Adjective: an adjective before the noun with one-replacement, the current Caliph and the
  old one -/
  | adjective
  /-- Adverb: a non-ly adverb before the noun with one-replacement, the now Caliph and the old
  one -/
  | adverb
  deriving DecidableEq, Repr, Fintype

/-- The conditions of Experiment 1b. -/
inductive Exp1bCondition where
  /-- Control: the grammatical fillers -/
  | control
  /-- Ungrammatical: the ungrammatical fillers -/
  | ungrammatical
  /-- Coordination: a noun phrase coordinated with a clause where only noun phrases are selected -/
  | coordination
  /-- Simple: a clause alone where only noun phrases are selected -/
  | simple
  deriving DecidableEq, Repr, Fintype

/-- The three experiments. -/
inductive Experiment where
  /-- 1a: prenominal adverbs and adjectives -/
  | exp1a
  /-- 1b: clauses in noun-phrase positions -/
  | exp1b
  /-- 2: prenominal adverbs and adjectives with one-replacement -/
  | exp2
  deriving DecidableEq, Repr, Fintype

/-- A band of a participant's mean rating of a condition. -/
inductive Band where
  /-- 4 or higher: rated 4 or higher, taken as acceptable -/
  | atLeastFour
  /-- below 3: rated below 3, taken as unacceptable -/
  | belowThree
  deriving DecidableEq, Repr, Fintype

/-- The participants of Experiments 1a and 1b whose data entered the analysis. (p. 448; checked
against the page images.) -/
def participants1 : ℕ := 65

/-- The participants of Experiment 2 whose data entered the analysis. (p. 450; checked against
the page images.) -/
def participants2 : ℕ := 77

/-- A row of Table 2, p. 448: the mean ratings and standard deviations of the conditions of
Experiment 1a. -/
structure Exp1aStatistic where
  /-- The mean rating. -/
  mean : Decimal
  /-- The standard deviation of the ratings. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 448, by scale and condition; from an experiment; checked against the
page images. -/
def table2 : Scale → Exp1aCondition → Exp1aStatistic
  | .raw, .control => ⟨⟨445, 2⟩, ⟨91, 2⟩⟩
  | .raw, .ungrammatical => ⟨⟨227, 2⟩, ⟨136, 2⟩⟩
  | .raw, .adjective => ⟨⟨475, 2⟩, ⟨55, 2⟩⟩
  | .raw, .adverb => ⟨⟨316, 2⟩, ⟨127, 2⟩⟩
  | .z, .control => ⟨⟨63, 2⟩, ⟨71, 2⟩⟩
  | .z, .ungrammatical => ⟨⟨-97, 2⟩, ⟨94, 2⟩⟩
  | .z, .adjective => ⟨⟨87, 2⟩, ⟨40, 2⟩⟩
  | .z, .adverb => ⟨⟨-31, 2⟩, ⟨83, 2⟩⟩

/-- A row of Table 4, p. 450: the mean ratings and standard deviations of the conditions of
Experiment 2. -/
structure Exp2Statistic where
  /-- The mean rating. -/
  mean : Decimal
  /-- The standard deviation of the ratings. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 450, by scale and condition; from an experiment; checked against the
page images. -/
def table4 : Scale → Exp2Condition → Exp2Statistic
  | .raw, .grammaticalFiller => ⟨⟨439, 2⟩, ⟨95, 2⟩⟩
  | .raw, .ungrammaticalFiller => ⟨⟨220, 2⟩, ⟨127, 2⟩⟩
  | .raw, .adjective => ⟨⟨382, 2⟩, ⟨108, 2⟩⟩
  | .raw, .adverb => ⟨⟨260, 2⟩, ⟨117, 2⟩⟩
  | .z, .grammaticalFiller => ⟨⟨75, 2⟩, ⟨67, 2⟩⟩
  | .z, .ungrammaticalFiller => ⟨⟨-78, 2⟩, ⟨87, 2⟩⟩
  | .z, .adjective => ⟨⟨36, 2⟩, ⟨63, 2⟩⟩
  | .z, .adverb => ⟨⟨-49, 2⟩, ⟨72, 2⟩⟩

/-- A row of Table 6, p. 456: the mean ratings and standard deviations of the conditions of
Experiment 1b; the fillers repeat those of Table 2. -/
structure Exp1bStatistic where
  /-- The mean rating. -/
  mean : Decimal
  /-- The standard deviation of the ratings. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 6, p. 456, by scale and condition; from an experiment; checked against the
page images. -/
def table6 : Scale → Exp1bCondition → Exp1bStatistic
  | .raw, .control => ⟨⟨445, 2⟩, ⟨91, 2⟩⟩
  | .raw, .ungrammatical => ⟨⟨227, 2⟩, ⟨136, 2⟩⟩
  | .raw, .coordination => ⟨⟨395, 2⟩, ⟨106, 2⟩⟩
  | .raw, .simple => ⟨⟨287, 2⟩, ⟨120, 2⟩⟩
  | .z, .control => ⟨⟨63, 2⟩, ⟨71, 2⟩⟩
  | .z, .ungrammatical => ⟨⟨-97, 2⟩, ⟨94, 2⟩⟩
  | .z, .coordination => ⟨⟨28, 2⟩, ⟨67, 2⟩⟩
  | .z, .simple => ⟨⟨-50, 2⟩, ⟨74, 2⟩⟩

/-- A row of Table 7, p. 457: the mean raw rating of each item of Experiment 1b in each
condition. -/
structure Exp1bItem where
  /-- The item, numbered as in Table 5. -/
  item : ℕ
  /-- The mean rating of the item's clause alone. -/
  simple : Decimal
  /-- The mean rating of the item's coordination. -/
  coordination : Decimal
  deriving DecidableEq, Repr

/-- The 8 rows of Table 7, p. 457, in the paper's order; from an experiment; checked against the
page images. -/
def table7 : List Exp1bItem :=
  [⟨1, ⟨279, 2⟩, ⟨390, 2⟩⟩,
   ⟨2, ⟨310, 2⟩, ⟨352, 2⟩⟩,  -- despite, set in bold in the table
   ⟨3, ⟨279, 2⟩, ⟨352, 2⟩⟩,  -- in spite of
   ⟨4, ⟨268, 2⟩, ⟨406, 2⟩⟩,
   ⟨5, ⟨226, 2⟩, ⟨403, 2⟩⟩,
   ⟨6, ⟨274, 2⟩, ⟨429, 2⟩⟩,
   ⟨7, ⟨371, 2⟩, ⟨403, 2⟩⟩,  -- despite, set in bold in the table
   ⟨8, ⟨290, 2⟩, ⟨421, 2⟩⟩]

/-- A row of p. 449: how many of the participants of Experiment 1a rate a condition in a band. -/
structure Exp1aBand where
  /-- The condition. -/
  condition : Exp1aCondition
  /-- The band of the participant's mean rating. -/
  band : Band
  /-- How many participants fall in the band. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The 6 rows of p. 449, in the paper's order; from an experiment; checked against the page
images. -/
def bands1a : List Exp1aBand :=
  [⟨.adjective, .atLeastFour, 63⟩,
   ⟨.adjective, .belowThree, 0⟩,
   ⟨.adverb, .atLeastFour, 14⟩,
   ⟨.adverb, .belowThree, 28⟩,
   ⟨.control, .belowThree, 1⟩,
   ⟨.ungrammatical, .atLeastFour, 1⟩]

/-- A row of p. 451: how many of the participants of Experiment 2 rate a condition in a band. -/
structure Exp2Band where
  /-- The condition. -/
  condition : Exp2Condition
  /-- The band of the participant's mean rating. -/
  band : Band
  /-- How many participants fall in the band. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The 2 rows of p. 451, in the paper's order; from an experiment; checked against the page
images. -/
def bands2 : List Exp2Band :=
  [⟨.adverb, .atLeastFour, 6⟩,
   ⟨.adverb, .belowThree, 50⟩]

/-- A row of p. 457: how many of the participants of Experiment 1b rate a condition in a band. -/
structure Exp1bBand where
  /-- The condition. -/
  condition : Exp1bCondition
  /-- The band of the participant's mean rating. -/
  band : Band
  /-- How many participants fall in the band. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The 4 rows of p. 457, in the paper's order; from an experiment; checked against the page
images. -/
def bands1b : List Exp1bBand :=
  [⟨.coordination, .atLeastFour, 36⟩,
   ⟨.coordination, .belowThree, 7⟩,
   ⟨.simple, .atLeastFour, 13⟩,
   ⟨.simple, .belowThree, 38⟩]

/-- A row of pp. 449, 451, 456: the mixed-effects comparison of the two critical conditions of
each experiment, with the Satterthwaite degrees of freedom and the t-value. -/
structure Test where
  /-- The degrees of freedom. -/
  df : Decimal
  /-- The t-value. -/
  t : Decimal
  deriving DecidableEq, Repr

/-- The cells of pp. 449, 451, 456, by experiment; from an experiment; checked against the page
images. -/
def tests : Experiment → Test
  | .exp1a => ⟨⟨835, 2⟩, ⟨728, 2⟩⟩  -- Adv differs from Adj, p < .001
  | .exp2 => ⟨⟨767, 2⟩, ⟨6895, 3⟩⟩  -- Adv differs from Adj, p < .001
  | .exp1b => ⟨⟨7984, 3⟩, ⟨5575, 3⟩⟩  -- Coord differs from Simple, p < .001

end Bruening2025
