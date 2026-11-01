module

public import Linglib.Data.Statistics.Schema

/-!
# ClausWalch2024: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/ClausWalch2024.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Three web-based experiments in German on how numeral modification bears on framing effects. Each
offers a risky-choice framing scenario (a war zone with 600 lives at stake and a sure and a risky
response plan, after Mandel 2014; participants choose a plan) or an attribute framing scenario (a
project team asking for more funding after 50 projects, after Duchon et al. 1989; participants
approve or reject), with the sure outcome or the team's record stated in a positive frame (lives
saved, successful projects) or a negative one (lives lost, unsuccessful projects). Experiment 1
modifies the numerals with genau 'exactly', frame within subjects, both scenarios. Experiments 2
(risky choice) and 3 (attribute) cross frame, within subjects, with the modifier of the critical
numeral, bis zu 'up to' or höchstens 'at most', between subjects. The tables print the share of
sure-option choices or of approvals per cell; the generalized linear mixed models are reported in
the text.

## References

* [claus-walch-2024]
-/

@[expose] public section

namespace ClausWalch2024

open Data.Statistics

/-- How the outcome is stated. -/
inductive Frame where
  /-- Positive: as lives saved or successful projects -/
  | positive
  /-- Negative: as lives lost or unsuccessful projects -/
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The upper-bounding modifier of the critical numeral in Experiments 2 and 3. -/
inductive Modifier where
  /-- Bis zu 'up to': the directional modifier bis zu -/
  | bisZu
  /-- Höchstens 'at most': the superlative modifier höchstens -/
  | hoechstens
  deriving DecidableEq, Repr, Fintype

/-- The experiment, by scenario. -/
inductive Experiment where
  /-- Experiment 1, risky-choice framing: genau, the risky-choice scenario -/
  | exp1RiskyChoice
  /-- Experiment 1, attribute framing: genau, the attribute framing scenario -/
  | exp1Attribute
  /-- Experiment 2: bis zu and höchstens, the risky-choice scenario -/
  | exp2
  /-- Experiment 3: bis zu and höchstens, the attribute framing scenario -/
  | exp3
  deriving DecidableEq, Repr, Fintype

/-- A fixed effect of the mixed model, with deviation coding (+.5, -.5). -/
inductive Effect where
  /-- FRAME: the main effect of frame -/
  | frame
  /-- MODIFIER: the main effect of modifier -/
  | modifier
  /-- MODIFIER x FRAME: the interaction of modifier and frame -/
  | interaction
  deriving DecidableEq, Repr, Fintype

/-- The lives at stake in the risky-choice scenario. (Experiment 1, Materials and (3), p. 4146;
checked against the page images.) -/
def livesAtStake : ℕ := 600

/-- The lives the sure option saves in the positive frame. ((3), p. 4146; checked against the
page images.) -/
def livesSaved : ℕ := 200

/-- The lives lost under the sure option in the negative frame. ((3), p. 4146; checked against
the page images.) -/
def livesLost : ℕ := 400

/-- The team's last projects in the attribute framing scenario. ((4), p. 4146; checked against
the page images.) -/
def projects : ℕ := 50

/-- The successful projects, in the positive frame. ((4), p. 4146; checked against the page
images.) -/
def successfulProjects : ℕ := 30

/-- The unsuccessful projects, in the negative frame. ((4), p. 4146; checked against the page
images.) -/
def unsuccessfulProjects : ℕ := 20

/-- The participants analysed in Experiment 1. (Experiment 1, Participants, p. 4146; checked
against the page images.) -/
def exp1Participants : ℕ := 52

/-- The participants analysed in Experiment 2. (Experiment 2, Participants, p. 4147; checked
against the page images.) -/
def exp2Participants : ℕ := 101

/-- The participants analysed in Experiment 3. (Experiment 3, Participants, p. 4148; checked
against the page images.) -/
def exp3Participants : ℕ := 94

/-- A row of Table 1, p. 4147: the proportion of sure-option choices in the risky-choice framing
trials of Experiment 1, by frame. -/
structure SureChoices1 where
  /-- The percentage of sure-option choices. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 4147, by frame; from an experiment; checked against the page images. -/
def table1 : Frame → SureChoices1
  | .positive => ⟨⟨519, 1⟩⟩
  | .negative => ⟨⟨346, 1⟩⟩

/-- A row of Table 2, p. 4147: the proportion of approvals in the attribute framing trials of
Experiment 1, by frame. -/
structure Approvals2 where
  /-- The percentage of approvals. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 4147, by frame; from an experiment; checked against the page images. -/
def table2 : Frame → Approvals2
  | .positive => ⟨⟨923, 1⟩⟩
  | .negative => ⟨⟨654, 1⟩⟩

/-- A row of Table 3, p. 4148: the proportion of sure-option choices in the risky-choice framing
trials of Experiment 2, by modifier and frame. -/
structure SureChoices3 where
  /-- The percentage of sure-option choices. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 3, p. 4148, by modifier and frame; from an experiment; checked against the
page images. -/
def table3 : Modifier → Frame → SureChoices3
  | .bisZu, .positive => ⟨⟨592, 1⟩⟩
  | .bisZu, .negative => ⟨⟨449, 1⟩⟩
  | .hoechstens, .positive => ⟨⟨423, 1⟩⟩
  | .hoechstens, .negative => ⟨⟨558, 1⟩⟩

/-- A row of Table 4, p. 4148: the proportion of approvals in the attribute framing trials of
Experiment 3, by modifier and frame. -/
structure Approvals4 where
  /-- The percentage of approvals. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 4148, by modifier and frame; from an experiment; checked against the
page images. -/
def table4 : Modifier → Frame → Approvals4
  | .bisZu, .positive => ⟨⟨889, 1⟩⟩
  | .bisZu, .negative => ⟨⟨689, 1⟩⟩
  | .hoechstens, .positive => ⟨⟨673, 1⟩⟩
  | .hoechstens, .negative => ⟨⟨714, 1⟩⟩

/-- A row of Results and Discussion of Experiments 1–3, pp. 4146–4148: a fixed effect of the
generalized linear mixed model (binomial logit, participants as random factor) fitted to an
experiment's choices. -/
structure MixedModelEffect where
  /-- The experiment and scenario. -/
  experiment : Experiment
  /-- The fixed effect. -/
  effect : Effect
  /-- The estimate. -/
  b : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The z statistic. -/
  z : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 8 rows of Results and Discussion of Experiments 1–3, pp. 4146–4148, in the paper's order;
from an experiment; checked against the page images. -/
def mixedModels : List MixedModelEffect :=
  [⟨.exp1RiskyChoice, .frame, ⟨143, 2⟩, ⟨65, 2⟩, ⟨222, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp1Attribute, .frame, ⟨1543, 2⟩, ⟨423, 2⟩, ⟨365, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.exp2, .interaction, ⟨-135, 2⟩, ⟨64, 2⟩, ⟨-209, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp2, .modifier, ⟨15, 2⟩, ⟨37, 2⟩, ⟨40, 2⟩, ⟨.eq, ⟨69, 2⟩⟩⟩,
   ⟨.exp2, .frame, ⟨2, 2⟩, ⟨31, 2⟩, ⟨7, 2⟩, ⟨.eq, ⟨95, 2⟩⟩⟩,
   ⟨.exp3, .interaction, ⟨-3453, 2⟩, ⟨1654, 2⟩, ⟨-209, 2⟩, ⟨.lt, ⟨5, 2⟩⟩⟩,
   ⟨.exp3, .modifier, ⟨1052, 2⟩, ⟨1131, 2⟩, ⟨93, 2⟩, ⟨.eq, ⟨35, 2⟩⟩⟩,
   ⟨.exp3, .frame, ⟨1141, 2⟩, ⟨1209, 2⟩, ⟨94, 2⟩, ⟨.eq, ⟨35, 2⟩⟩⟩]

end ClausWalch2024
