module

public import Linglib.Data.Statistics.Schema

/-!
# BillEtAl2025: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/BillEtAl2025.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

An act-out comprehension study of the three conjunctive expressions of Georgian and of Hungarian, J,
MU and J-MU, with children and adults. Each trial showed three objects and a sentence saying that
two of them are on the table; the two measures were accuracy, whether the end state matched the
exhaustified sentence, and sentence-played-n, how often the sentence was replayed. Tables 1, 2, 4
and 5 print the likelihood-ratio tests of the fixed effects, Table 3 the Tukey follow-up contrasts
among the Georgian sentence types, and footnote 12 the kinds of error the Georgian children made.

## Raw data

* <https://doi.org/10.5281/zenodo.15225998>: materials, trial-level data and analysis scripts of
  both experiments
* <https://doi.org/10.17605/OSF.IO/VE9N8>: preregistration of the Georgian experiment
* <https://doi.org/10.17605/OSF.IO/29UFG>: preregistration of the Hungarian experiment

## References

* [bill-etal-2025]
-/

@[expose] public section

namespace BillEtAl2025

open Data.Statistics

/-- The language of an experiment. -/
inductive Language where
  /-- Georgian: Georgian, §3.1 -/
  | georgian
  /-- Hungarian: Hungarian, §3.2 -/
  | hungarian
  deriving DecidableEq, Repr, Fintype

/-- The participant group, the fixed effect group. -/
inductive Group where
  /-- Adult: adults -/
  | adult
  /-- Child: children -/
  | child
  deriving DecidableEq, Repr, Fintype

/-- The sentence type, the fixed effect sentence-type. -/
inductive Sentence where
  /-- j: only a J particle, (5a) and (6a) -/
  | j
  /-- mu: only MU particles, (5b) and (6b) -/
  | mu
  /-- j-mu: a J particle and two MU particles, (5c) and (6c) -/
  | jMu
  deriving DecidableEq, Repr, Fintype

/-- The response variable. -/
inductive Measure where
  /-- accuracy: whether the end state matched the exhaustified sentence -/
  | accuracy
  /-- sentence-played-n: how many times the sentence was played, log-transformed, over the
  responses satisfying the basic truth conditions -/
  | playedN
  deriving DecidableEq, Repr, Fintype

/-- A fixed effect of the mixed-effects models. -/
inductive Effect where
  /-- group: adult or child -/
  | group
  /-- sentence: the sentence type -/
  | sentence
  /-- group:sentence: the interaction of group and sentence type -/
  | interaction
  deriving DecidableEq, Repr, Fintype

/-- A pairwise contrast between sentence types, in the paper's order and orientation. -/
inductive Contrast where
  /-- j vs. j-mu: J against J-MU -/
  | jVsJMu
  /-- j vs. mu: J against MU -/
  | jVsMu
  /-- j-mu vs. mu: J-MU against MU -/
  | jMuVsMu
  deriving DecidableEq, Repr, Fintype

/-- Whether the authors star the p-value. -/
inductive Mark where
  /-- *: starred -/
  | starred
  /-- none: not starred -/
  | plain
  deriving DecidableEq, Repr, Fintype

/-- The kinds of inaccurate end state among the Georgian children's responses, footnote 12. -/
inductive ErrorKind where
  /-- unmentioned objects: an unmentioned object was placed on the table -/
  | unmentioned
  /-- only one of the mentioned objects: only one of the two mentioned objects was placed on the
  table -/
  | oneMentioned
  /-- neither of the mentioned objects: neither mentioned object was placed on the table -/
  | neitherMentioned
  deriving DecidableEq, Repr, Fintype

/-- The objects shown in a trial, of which the sentence mentions two. (§2.2, 5:5; checked against
the page images.) -/
def objectsPerTrial : ℕ := 3

/-- The starting pictures: none, one or both mentioned objects already on the table. (§2.3, Fig.
3, 5:6; checked against the PDF text layer only.) -/
def startingPictures : ℕ := 3

/-- The versions of each starting picture for each sentence type. (§2.3, 5:7; checked against the
page images.) -/
def versionsPerPicture : ℕ := 2

/-- The experimental items, six per sentence type. (§2.3, 5:7; checked against the page images.) -/
def items : ℕ := 18

/-- Item 2, removed from both datasets because two objects of its picture looked like cakes.
(§3.1, 5:8; §3.2, 5:12; checked against the PDF text layer only.) -/
def removedItems : ℕ := 1

/-- The inaccurate responses of the Georgian children. (fn. 12, 5:14; checked against the page
images.) -/
def childErrors : ℕ := 103

/-- A row of §2.1, 5:5: the participants of each experiment by group. -/
structure Participants where
  /-- The number of participants. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of §2.1, 5:5, by language and group; from an experiment; checked against the page
images. -/
def participants : Language → Group → Participants
  | .georgian, .child => ⟨31⟩  -- 3;9–5;10, mean 4;9, daycare centers in Ozurgeti
  | .georgian, .adult => ⟨41⟩  -- Ilia State University, Tbilisi
  | .hungarian, .child => ⟨25⟩  -- 3;0–5;0, mean 4;2, daycare centers in Budapest
  | .hungarian, .adult => ⟨30⟩  -- Prolific

/-- A row of §3.1.2, 5:10: the Georgian data points entering the sentence-played-n analysis, the
responses satisfying the basic truth conditions of the sentence. -/
structure PlayedPoints where
  /-- The number of data points. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of §3.1.2, 5:10, by group; from an experiment; checked against the page images. -/
def playedPoints : Group → PlayedPoints
  | .adult => ⟨689⟩
  | .child => ⟨499⟩

/-- A row of Tables 1 and 2, 5:9 and 5:11 (Georgian); Tables 4 and 5, 5:13 (Hungarian): a
likelihood-ratio test of a fixed effect of the model of a response measure, against the model
without it. -/
structure Lrt where
  /-- The degrees of freedom. -/
  df : ℕ
  /-- The chi-square statistic. -/
  chiSq : Decimal
  /-- The p-value. -/
  p : PValue
  /-- Whether the authors star the p-value. -/
  mark : Mark
  deriving DecidableEq, Repr

/-- The cells of Tables 1 and 2, 5:9 and 5:11 (Georgian); Tables 4 and 5, 5:13 (Hungarian), by
language and measure and effect; from an experiment; checked against the page images. -/
def lrt : Language → Measure → Effect → Lrt
  | .georgian, .accuracy, .group => ⟨1, ⟨1227, 2⟩, ⟨.lt, ⟨1, 3⟩⟩, .starred⟩
  | .georgian, .accuracy, .sentence => ⟨2, ⟨224, 2⟩, ⟨.eq, ⟨327, 3⟩⟩, .plain⟩
  | .georgian, .accuracy, .interaction => ⟨2, ⟨195, 2⟩, ⟨.eq, ⟨377, 3⟩⟩, .plain⟩
  | .georgian, .playedN, .group => ⟨1, ⟨3588, 2⟩, ⟨.lt, ⟨1, 3⟩⟩, .starred⟩
  | .georgian, .playedN, .sentence => ⟨2, ⟨1495, 2⟩, ⟨.lt, ⟨1, 3⟩⟩, .starred⟩
  | .georgian, .playedN, .interaction => ⟨2, ⟨2389, 2⟩, ⟨.lt, ⟨1, 3⟩⟩, .starred⟩
  | .hungarian, .accuracy, .group => ⟨1, ⟨75, 2⟩, ⟨.eq, ⟨385, 3⟩⟩, .plain⟩
  | .hungarian, .accuracy, .sentence => ⟨2, ⟨293, 2⟩, ⟨.eq, ⟨231, 3⟩⟩, .plain⟩
  | .hungarian, .accuracy, .interaction => ⟨2, ⟨182, 2⟩, ⟨.eq, ⟨402, 3⟩⟩, .plain⟩
  | .hungarian, .playedN, .group =>  -- printed `< .05` without a star
    ⟨1,
     ⟨654, 2⟩,
     ⟨.lt, ⟨5, 2⟩⟩,
     .plain⟩
  | .hungarian, .playedN, .sentence => ⟨2, ⟨219, 2⟩, ⟨.eq, ⟨334, 3⟩⟩, .plain⟩
  | .hungarian, .playedN, .interaction => ⟨2, ⟨55, 2⟩, ⟨.eq, ⟨761, 3⟩⟩, .plain⟩

/-- A row of Table 3, 5:11: a Tukey-adjusted follow-up contrast between two sentence types in the
Georgian sentence-played-n model, on the log scale: a negative estimate means the first
sentence type was played less. -/
structure ContrastTest where
  /-- The estimated difference, first minus second, on the log scale. -/
  estimate : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The degrees of freedom. -/
  df : ℕ
  /-- The t ratio. -/
  t : Decimal
  /-- The Tukey-adjusted p-value. -/
  p : PValue
  /-- Whether the authors star the p-value. -/
  mark : Mark
  deriving DecidableEq, Repr

/-- The cells of Table 3, 5:11, by group and contrast; from an experiment; checked against the
page images. -/
def contrasts : Group → Contrast → ContrastTest
  | .adult, .jVsJMu => ⟨⟨19, 3⟩, ⟨26, 3⟩, 1120, ⟨708, 3⟩, ⟨.eq, ⟨759, 3⟩⟩, .plain⟩
  | .adult, .jVsMu => ⟨⟨-3, 3⟩, ⟨27, 3⟩, 1120, ⟨-102, 3⟩, ⟨.eq, ⟨994, 3⟩⟩, .plain⟩
  | .adult, .jMuVsMu => ⟨⟨-21, 3⟩, ⟨25, 3⟩, 1120, ⟨-850, 3⟩, ⟨.eq, ⟨672, 3⟩⟩, .plain⟩
  | .child, .jVsJMu => ⟨⟨-176, 3⟩, ⟨31, 3⟩, 1121, ⟨-5681, 3⟩, ⟨.lt, ⟨1, 4⟩⟩, .starred⟩
  | .child, .jVsMu => ⟨⟨-69, 3⟩, ⟨31, 3⟩, 1121, ⟨-2230, 3⟩, ⟨.eq, ⟨67, 3⟩⟩, .plain⟩
  | .child, .jMuVsMu => ⟨⟨106, 3⟩, ⟨3, 2⟩, 1121, ⟨3555, 3⟩, ⟨.lt, ⟨1, 2⟩⟩, .starred⟩

/-- A row of fn. 12, 5:14: the Georgian children's inaccurate responses by kind, with the
percentage of all 103 errors as printed. -/
structure ErrorCount where
  /-- The number of errors of the kind. -/
  count : ℕ
  /-- The printed percentage of all errors. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of fn. 12, 5:14, by kind; from an experiment; checked against the page images. -/
def childErrorKinds : ErrorKind → ErrorCount
  | .unmentioned => ⟨75, ⟨73, 0⟩⟩
  | .oneMentioned => ⟨21, ⟨20, 0⟩⟩
  | .neitherMentioned => ⟨7, ⟨7, 0⟩⟩

end BillEtAl2025
