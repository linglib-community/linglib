module

public import Linglib.Data.Statistics.Schema

/-!
# IcardEtAl2017: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/IcardEtAl2017.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Two 2 (causal structure) x 2 (norm violation) x 4 (vignette) between-subjects experiments in which
participants rated, on a 1 to 7 scale, their agreement that the varied agent caused the outcome.
Experiment 1 varies a prescriptive norm, Experiment 2 a statistical one. The tables record the
participant counts and the condition means and standard deviations printed for each causal
structure, collapsed over the four vignettes; the by-vignette means are only plotted (Figures A1 and
B1). Section numbers are those of the accepted preprint (PsyArXiv g7cqk).

## Raw data

* <https://osf.io/j23gr>: the raw data of both experiments, as the paper states; not downloaded

## References

* [icard-et-al-2017]
-/

@[expose] public section

namespace IcardEtAl2017

open Data.Statistics

/-- The two experiments, by the kind of norm the varied agent violates. -/
inductive Experiment where
  /-- 1: Experiment 1, prescriptive norms -/
  | prescriptive
  /-- 2: Experiment 2, statistical norms -/
  | statistical
  deriving DecidableEq, Repr, Fintype

/-- The causal structure of the vignette, how the outcome depends on the two agents. -/
inductive CausalStructure where
  /-- conjunctive: the outcome needs both agents -/
  | conjunctive
  /-- disjunctive: the outcome needs either agent -/
  | disjunctive
  deriving DecidableEq, Repr, Fintype

/-- Whether the varied agent's action violates the norm. -/
inductive Normality where
  /-- normative: the varied agent follows the norm -/
  | normative
  /-- norm violation: the varied agent violates the norm -/
  | violation
  deriving DecidableEq, Repr, Fintype

/-- Workers recruited for each experiment. (sections 5.1.1 and 5.2.1; checked against the page
images.) -/
def recruited : ℕ := 480

/-- A row of sections 5.1.2 and 5.2.2: the participants excluded for failing a manipulation check
and those analyzed. -/
structure Participants where
  /-- Participants excluded. -/
  excluded : ℕ
  /-- Participants analyzed. -/
  analyzed : ℕ
  deriving DecidableEq, Repr

/-- The cells of sections 5.1.2 and 5.2.2, by experiment; from an experiment; checked against the
page images. -/
def participants : Experiment → Participants
  | .prescriptive => ⟨54, 426⟩
  | .statistical => ⟨110, 370⟩

/-- A row of sections 5.1.2 and 5.2.2: the mean agreement rating and its standard deviation in
each cell, collapsed over vignettes. -/
structure Rating where
  /-- The mean agreement rating, 1 to 7. -/
  mean : Decimal
  /-- The standard deviation. -/
  sd : Decimal
  deriving DecidableEq, Repr

/-- The cells of sections 5.1.2 and 5.2.2, by experiment and structure and normality; from an
experiment; checked against the page images. -/
def ratings : Experiment → CausalStructure → Normality → Rating
  | .prescriptive, .conjunctive, .violation => ⟨⟨561, 2⟩, ⟨179, 2⟩⟩
  | .prescriptive, .conjunctive, .normative => ⟨⟨337, 2⟩, ⟨211, 2⟩⟩
  | .prescriptive, .disjunctive, .violation => ⟨⟨325, 2⟩, ⟨205, 2⟩⟩
  | .prescriptive, .disjunctive, .normative => ⟨⟨418, 2⟩, ⟨193, 2⟩⟩
  | .statistical, .conjunctive, .violation => ⟨⟨558, 2⟩, ⟨141, 2⟩⟩
  | .statistical, .conjunctive, .normative => ⟨⟨458, 2⟩, ⟨188, 2⟩⟩
  | .statistical, .disjunctive, .violation => ⟨⟨389, 2⟩, ⟨197, 2⟩⟩
  | .statistical, .disjunctive, .normative => ⟨⟨467, 2⟩, ⟨173, 2⟩⟩

end IcardEtAl2017
