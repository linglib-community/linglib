module

public import Linglib.Data.Statistics.Schema

/-!
# Schwarzer2026: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Schwarzer2026.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Two experiments on German DP-CP coordination. Experiment 1 rated bare dass-clauses and DP-CP
coordinations after verbs that do and do not select a clause, on a five-point scale z-scored per
participant; table (14) prints the descriptive statistics of the four conditions. Experiment 2 was a
forced choice between the DP-first and the CP-first order of a coordination in preverbal and in
postverbal position.

## Raw data

* <https://osf.io/kznyt/>: materials, scripts, plots and trial-level data of both experiments; table
  (14) is recomputed from data/accept.csv and the choices from data/2afc.csv

## References

* [schwarzer-2026]
-/

@[expose] public section

namespace Schwarzer2026

open Data.Statistics

/-- The complement of Experiment 1. -/
inductive Complement where
  /-- coord.: a DP-CP coordination -/
  | coord
  /-- dass: a bare dass-clause -/
  | dass
  deriving DecidableEq, Repr, Fintype

/-- Whether the verb selects a clausal complement. -/
inductive Selection where
  /-- no: the verb does not select a clause (beenden) -/
  | no
  /-- yes: the verb selects a clause (veranlassen) -/
  | yes
  deriving DecidableEq, Repr, Fintype

/-- The position of the coordination relative to the verb in Experiment 2. -/
inductive Position where
  /-- preverbal: before the clause-final verb of an embedded clause, (16) -/
  | preverbal
  /-- postverbal: after the verb-second verb of a root clause, (17) -/
  | postverbal
  deriving DecidableEq, Repr, Fintype

/-- The order of the conjuncts in Experiment 2. -/
inductive Order where
  /-- DP-first: the noun phrase first -/
  | dpFirst
  /-- CP-first: the clause first -/
  | cpFirst
  deriving DecidableEq, Repr, Fintype

/-- A row of table (14), p. 9: the ratings of a complement after a verb that does or does not
select a clause. -/
structure Rating where
  /-- The number of observations. -/
  observations : ℕ
  /-- The mean z-score. -/
  meanZ : Decimal
  /-- The standard deviation of the z-scores. -/
  sd : Decimal
  /-- The median z-score. -/
  medianZ : Decimal
  deriving DecidableEq, Repr

/-- The cells of table (14), p. 9, by complement and selection; from an experiment; recomputed
from the authors' released data by `scripts/check_statistics.py`. -/
def ratings : Complement → Selection → Rating
  | .coord, .no => ⟨44, ⟨-253, 3⟩, ⟨735, 3⟩, ⟨-244, 3⟩⟩
  | .coord, .yes => ⟨44, ⟨369, 3⟩, ⟨723, 3⟩, ⟨495, 3⟩⟩
  | .dass, .no => ⟨44, ⟨-526, 3⟩, ⟨669, 3⟩, ⟨-684, 3⟩⟩
  | .dass, .yes => ⟨44, ⟨891, 3⟩, ⟨631, 3⟩, ⟨108, 2⟩⟩

/-- A row of Experiment 2 results, p. 13: how often an order was chosen in a position. In the
released data each of the 30 participants chose once in each position, among ten control
pairs of each group, although the paper describes four test pairs per participant. -/
structure Choice where
  /-- How many participants chose the order. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of Experiment 2 results, p. 13, by position and order; from an experiment;
recomputed from the authors' released data by `scripts/check_statistics.py`. -/
def choices : Position → Order → Choice
  | .preverbal, .dpFirst => ⟨23⟩
  | .preverbal, .cpFirst => ⟨7⟩
  | .postverbal, .dpFirst => ⟨23⟩
  | .postverbal, .cpFirst => ⟨7⟩

end Schwarzer2026
