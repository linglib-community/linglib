module

public import Linglib.Data.Experiments.Schema

/-!
# BeltramaSchwarz2024: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/BeltramaSchwarz2024.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

Two experiments on American English round numerals, with the speaker described as Nerdy, as Chill,
or not at all (between subjects), crossed with Screen Fit (within subjects): the number on a visible
phone screen matched the uttered one, diverged from it largely, or diverged slightly (Imprecise).
Experiment 1 (Covered Screen) asked which phone the speaker was looking at, a covered choice
rejecting the visible one; Experiment 2 (Truth Value Judgment) showed the screen the speaker looked
at and asked whether the answer was right. Rejection is a covered choice or a wrong judgment.

## References

* [beltrama-schwarz-2024]
-/

@[expose] public section

namespace BeltramaSchwarz2024

open Data.Experiments

/-- The task of an experiment. -/
inductive Task where
  /-- Covered Screen: Experiment 1: choose the phone the speaker was looking at, a covered choice
  rejecting the visible screen -/
  | coveredScreen
  /-- Truth Value Judgment: Experiment 2: judge the speaker's answer right or wrong given the
  visible screen -/
  | truthValueJudgment
  deriving DecidableEq, Repr, Fintype

/-- The stereotype the interlocutors are described as; the No.Persona baseline describes none. -/
inductive Persona where
  /-- Nerdy: described as Nerdy -/
  | nerdy
  /-- Chill: described as Chill -/
  | chill
  deriving DecidableEq, Repr, Fintype

/-- The relation of the number on the visible screen to the uttered one. -/
inductive ScreenFit where
  /-- Match: identical -/
  | match
  /-- Mismatch: largely divergent -/
  | mismatch
  /-- Imprecise: slightly divergent -/
  | imprecise
  deriving DecidableEq, Repr, Fintype

/-- Screen Fit recoded as a binary factor for the analyses. -/
inductive Fit where
  /-- Control: Match and Mismatch collapsed -/
  | control
  /-- Imprecise: the Imprecise level -/
  | imprecise
  deriving DecidableEq, Repr, Fintype

/-- A range of values the bare numeral *$200* can be taken to describe. -/
inductive Range where
  /-- exactly $200: the exact value -/
  | exact
  /-- $195–$205: a range of ten dollars -/
  | narrow
  /-- $190–$210: a range of twenty dollars -/
  | wide
  deriving DecidableEq, Repr, Fintype

/-- A trait a persona is introduced with. -/
inductive Descriptor where
  /-- studious: studious -/
  | studious
  /-- articulate: articulate -/
  | articulate
  /-- introverted: introverted -/
  | introverted
  /-- uptight: uptight -/
  | uptight
  /-- laid-back: laid-back -/
  | laidBack
  /-- sociable: sociable -/
  | sociable
  /-- extroverted: extroverted -/
  | extroverted
  /-- care-free: care-free -/
  | careFree
  deriving DecidableEq, Repr, Fintype

/-- The paper's reading of a comparison of rejection rates, the first condition against the
second. -/
inductive Verdict where
  /-- higher: higher -/
  | higher
  /-- lower: lower -/
  | lower
  /-- no difference: no difference -/
  | noDifference
  deriving DecidableEq, Repr, Fintype

/-- A regression the paper reports. -/
inductive Model where
  /-- Persona × Screen Fit: Persona (reference No.Persona) and binary Screen Fit, all trials -/
  | main
  /-- Persona × Gender × Similarity: Persona and Speaker Gender sum coded and rescaled
  Similarity, Imprecise trials -/
  | similarity
  /-- Similarity, Nerdy reference: the similarity model with Persona treatment coded, Nerdy as
  reference -/
  | similarityNerdy
  /-- Similarity, Chill reference: the similarity model with Persona treatment coded, Chill as
  reference -/
  | similarityChill
  /-- Persona × Task: both experiments' Imprecise trials, Task sum coded -/
  | combined
  deriving DecidableEq, Repr, Fintype

/-- A coefficient of a model. -/
inductive Term where
  /-- Chill: Chill against No.Persona -/
  | chill
  /-- Nerdy: Nerdy against No.Persona -/
  | nerdy
  /-- Chill × Screen Fit: its interaction with Screen Fit -/
  | chillScreenFit
  /-- Nerdy × Screen Fit: its interaction with Screen Fit -/
  | nerdyScreenFit
  /-- Screen Fit: Screen Fit -/
  | screenFit
  /-- Persona: Persona -/
  | persona
  /-- Similarity: Similarity -/
  | similarity
  /-- Speaker Gender: Speaker Gender -/
  | gender
  /-- Persona × Similarity: interaction -/
  | personaSimilarity
  /-- Persona × Speaker Gender: interaction -/
  | personaGender
  /-- Speaker Gender × Similarity: interaction -/
  | genderSimilarity
  /-- Persona × Speaker Gender × Similarity: interaction -/
  | personaGenderSimilarity
  /-- Nerdy × Task: interaction -/
  | nerdyTask
  deriving DecidableEq, Repr, Fintype

/-- Experimental items, each in nine Persona × Screen Fit versions. (§4.2, p. 9; checked against
the page images.) -/
def items : ℕ := 24

/-- Filler dialogues. (§4.2, p. 10; checked against the PDF text layer only.) -/
def fillers : ℕ := 24

/-- Imprecise trials per participant, against six Match and six Mismatch. (§4.2, p. 10; checked
against the PDF text layer only.) -/
def impreciseTrials : ℕ := 12

/-- The amount of the utterance of Figure 1, in dollars. (Figure 1, p. 8; checked against the
page images.) -/
def uttered : ℕ := 200

/-- The least deviation of an Imprecise screen, in percent of the count unit. (§4.1, p. 9;
checked against the page images.) -/
def bandLow : ℕ := 5

/-- The greatest deviation of an Imprecise screen, in percent of the count unit. (§4.1, p. 9;
checked against the page images.) -/
def bandHigh : ℕ := 18

/-- The count unit of the dollar amounts the band is relative to. (§4.1, p. 9; checked against
the page images.) -/
def countUnit : ℕ := 100

/-- A row of §4.4, p. 11 (Experiment 1); §5.2, p. 17 (Experiment 2): the participants of an
experiment, recruited on Prolific. -/
structure Participants where
  /-- Recruited. -/
  recruited : ℕ
  /-- Median age. -/
  ageMedian : ℕ
  /-- Female. -/
  female : ℕ
  /-- Male. -/
  male : ℕ
  /-- Other. -/
  other : ℕ
  deriving DecidableEq, Repr

/-- The cells of §4.4, p. 11 (Experiment 1); §5.2, p. 17 (Experiment 2), by task; checked against
the page images. -/
def participants : Task → Participants
  | .coveredScreen => ⟨282, 33, 166, 114, 2⟩
  | .truthValueJudgment => ⟨244, 33, 135, 102, 7⟩

/-- A row of §4.1, p. 8: the traits participants were told a persona describes. -/
structure Descriptors where
  /-- The traits. -/
  traits : List Descriptor
  deriving DecidableEq, Repr

/-- The cells of §4.1, p. 8, by persona; checked against the page images. -/
def descriptors : Persona → Descriptors
  | .nerdy => ⟨[.studious, .articulate, .introverted, .uptight]⟩
  | .chill => ⟨[.laidBack, .sociable, .extroverted, .careFree]⟩

/-- A row of Figure 1, p. 8: the visible screen of each Screen Fit level for the utterance "The
price is $200". -/
structure Screen where
  /-- The amount on the visible screen, in dollars. -/
  displayed : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figure 1, p. 8, by screenFit; checked against the page images. -/
def screens : ScreenFit → Screen
  | .match => ⟨⟨20000, 2⟩⟩
  | .mismatch => ⟨⟨65006, 2⟩⟩
  | .imprecise => ⟨⟨20706, 2⟩⟩

/-- A row of §2, p. 5: the ranges of values the paper offers as interpretations of "The ticket
costs $200". -/
structure RangeRow where
  /-- Its least value, in dollars. -/
  lower : ℕ
  /-- Its greatest value, in dollars. -/
  upper : ℕ
  deriving DecidableEq, Repr

/-- The cells of §2, p. 5, by range; checked against the page images. -/
def ranges : Range → RangeRow
  | .exact => ⟨200, 200⟩
  | .narrow => ⟨195, 205⟩
  | .wide => ⟨190, 210⟩

/-- A row of §4.5, p. 12; §5.3, p. 17; §6, p. 20; §7, p. 21: the paper's reading of the rejection
rate in the Imprecise condition with a persona against the No.Persona baseline. -/
structure VerdictRow where
  /-- The paper's reading of its rejection rate against No.Persona. -/
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The cells of §4.5, p. 12; §5.3, p. 17; §6, p. 20; §7, p. 21, by task and persona; checked
against the page images. -/
def verdicts : Task → Persona → VerdictRow
  | .coveredScreen, .nerdy => ⟨.higher⟩
  | .coveredScreen, .chill => ⟨.lower⟩
  | .truthValueJudgment, .nerdy => ⟨.noDifference⟩
  | .truthValueJudgment, .chill => ⟨.lower⟩

/-- A row of §4.5, pp. 12–13; §5.3, p. 17; §6, p. 20: a contrast of rejection rates between a
persona and No.Persona, extracted with emmeans. -/
structure PersonaContrast where
  /-- The task. -/
  task : Task
  /-- The recoded Screen Fit. -/
  fit : Fit
  /-- The persona compared with No.Persona. -/
  persona : Persona
  /-- The standard error. -/
  se : Decimal
  /-- The z statistic, unsigned as printed. -/
  z : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 8 rows of §4.5, pp. 12–13; §5.3, p. 17; §6, p. 20, in the paper's order; checked against
the page images. -/
def personaContrasts : List PersonaContrast :=
  [⟨.coveredScreen, .imprecise, .nerdy, ⟨20, 2⟩, ⟨662, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .imprecise, .chill, ⟨20, 2⟩, ⟨761, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .control, .nerdy, ⟨18, 2⟩, ⟨7, 2⟩, ⟨.eq, ⟨99, 2⟩⟩⟩,
   ⟨.coveredScreen, .control, .chill, ⟨18, 2⟩, ⟨5, 2⟩, ⟨.eq, ⟨99, 2⟩⟩⟩,
   ⟨.truthValueJudgment, .imprecise, .chill, ⟨24, 2⟩, ⟨843, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.truthValueJudgment,  -- printed as Nerdy vs. No.Persona in the sentence on Chill
     .control,
     .nerdy,
     ⟨24, 2⟩,
     ⟨5, 2⟩,
     ⟨.eq, ⟨97, 2⟩⟩⟩,
   ⟨.coveredScreen, .imprecise, .nerdy, ⟨43, 2⟩, ⟨440, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,  -- combined analysis, §6
   ⟨.truthValueJudgment,  -- combined analysis, §6
     .imprecise,
     .nerdy,
     ⟨45, 2⟩,
     ⟨151, 2⟩,
     ⟨.eq, ⟨28, 2⟩⟩⟩]

/-- A row of §6, pp. 20–21: a contrast of Imprecise rejection rates between the two tasks within
a persona condition. -/
structure TaskContrast where
  /-- The persona condition, none for No.Persona. -/
  persona : Option Persona
  /-- The paper's reading of the Truth Value Judgment rejection rate against the Covered Screen
  one. -/
  verdict : Verdict
  /-- The standard error. -/
  se : Decimal
  /-- The z statistic. -/
  z : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 3 rows of §6, pp. 20–21, in the paper's order; checked against the page images. -/
def taskContrasts : List TaskContrast :=
  [⟨none, .noDifference, ⟨37, 2⟩, ⟨100, 2⟩, ⟨.eq, ⟨30, 2⟩⟩⟩,
   ⟨some .nerdy, .noDifference, ⟨46, 2⟩, ⟨176, 2⟩, ⟨.eq, ⟨8, 2⟩⟩⟩,
   ⟨some .chill, .noDifference, ⟨37, 2⟩, ⟨6, 2⟩, ⟨.eq, ⟨95, 2⟩⟩⟩]

/-- A row of §4.5, pp. 12–15; §5.3, pp. 17–19; §6, p. 20: a coefficient of a mixed-effects
logistic regression on rejections, covered choices in Experiment 1 and wrong judgments in
Experiment 2. -/
structure Coefficient where
  /-- The experiment, Truth Value Judgment for the combined analysis. -/
  task : Task
  /-- The model. -/
  model : Model
  /-- The coefficient. -/
  term : Term
  /-- Its estimate. -/
  beta : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The z statistic, unsigned as printed. -/
  z : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 26 rows of §4.5, pp. 12–15; §5.3, pp. 17–19; §6, p. 20, in the paper's order; checked
against the page images. -/
def coefficients : List Coefficient :=
  [⟨.coveredScreen, .main, .chill, ⟨-67, 2⟩, ⟨13, 2⟩, ⟨486, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .main, .nerdy, ⟨77, 2⟩, ⟨14, 2⟩, ⟨554, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .main, .nerdyScreenFit, ⟨-78, 2⟩, ⟨13, 2⟩, ⟨57, 1⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .main, .chillScreenFit, ⟨66, 2⟩, ⟨13, 2⟩, ⟨486, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .main, .screenFit, ⟨0, 2⟩, ⟨10, 2⟩, ⟨9, 2⟩, ⟨.eq, ⟨92, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarity, .persona, ⟨223, 2⟩, ⟨24, 2⟩, ⟨912, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.coveredScreen, .similarity, .similarity, ⟨60, 2⟩, ⟨23, 2⟩, ⟨259, 2⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarity, .gender, ⟨1, 2⟩, ⟨27, 2⟩, ⟨5, 2⟩, ⟨.eq, ⟨97, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarity, .personaSimilarity, ⟨65, 2⟩, ⟨45, 2⟩, ⟨143, 2⟩, ⟨.eq, ⟨15, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarity, .personaGender, ⟨33, 2⟩, ⟨28, 2⟩, ⟨18, 2⟩, ⟨.eq, ⟨23, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarity, .genderSimilarity, ⟨6, 2⟩, ⟨14, 2⟩, ⟨46, 2⟩, ⟨.eq, ⟨64, 2⟩⟩⟩,
   ⟨.coveredScreen,
     .similarity,
     .personaGenderSimilarity,
     ⟨33, 2⟩,
     ⟨29, 2⟩,
     ⟨113, 2⟩,
     ⟨.eq, ⟨25, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarityNerdy, .similarity, ⟨92, 2⟩, ⟨36, 2⟩, ⟨256, 2⟩, ⟨.eq, ⟨1, 2⟩⟩⟩,
   ⟨.coveredScreen, .similarityChill, .similarity, ⟨27, 2⟩, ⟨28, 2⟩, ⟨95, 2⟩, ⟨.eq, ⟨33, 2⟩⟩⟩,
   ⟨.truthValueJudgment, .main, .chill, ⟨104, 2⟩, ⟨16, 2⟩, ⟨629, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.truthValueJudgment, .main, .chillScreenFit, ⟨100, 2⟩, ⟨16, 2⟩, ⟨614, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.truthValueJudgment,  -- printed as Nerd
     .main,
     .nerdy,
     ⟨2, 2⟩,
     ⟨15, 2⟩,
     ⟨15, 2⟩,
     ⟨.eq, ⟨87, 2⟩⟩⟩,
   ⟨.truthValueJudgment,  -- printed as Nerd and Screen Fit
     .main,
     .nerdyScreenFit,
     ⟨3, 2⟩,
     ⟨18, 2⟩,
     ⟨18, 2⟩,
     ⟨.eq, ⟨85, 2⟩⟩⟩,
   ⟨.truthValueJudgment, .similarity, .persona, ⟨157, 2⟩, ⟨27, 2⟩, ⟨568, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩,
   ⟨.truthValueJudgment, .similarity, .similarity, ⟨24, 2⟩, ⟨27, 2⟩, ⟨89, 2⟩, ⟨.eq, ⟨36, 2⟩⟩⟩,
   ⟨.truthValueJudgment, .similarity, .gender, ⟨13, 2⟩, ⟨11, 2⟩, ⟨117, 2⟩, ⟨.eq, ⟨23, 2⟩⟩⟩,
   ⟨.truthValueJudgment,  -- printed as No.Persona*Similarity
     .similarity,
     .personaSimilarity,
     ⟨27, 2⟩,
     ⟨27, 2⟩,
     ⟨101, 2⟩,
     ⟨.eq, ⟨30, 2⟩⟩⟩,
   ⟨.truthValueJudgment, .similarity, .personaGender, ⟨7, 2⟩, ⟨7, 2⟩, ⟨102, 2⟩, ⟨.eq, ⟨30, 2⟩⟩⟩,
   ⟨.truthValueJudgment, .similarity, .genderSimilarity, ⟨4, 2⟩, ⟨7, 2⟩, ⟨54, 2⟩, ⟨.eq, ⟨58, 2⟩⟩⟩,
   ⟨.truthValueJudgment,
     .similarity,
     .personaGenderSimilarity,
     ⟨3, 2⟩,
     ⟨7, 2⟩,
     ⟨41, 2⟩,
     ⟨.eq, ⟨67, 2⟩⟩⟩,
   ⟨.truthValueJudgment,  -- combined analysis of both tasks, §6
     .combined,
     .nerdyTask,
     ⟨62, 2⟩,
     ⟨31, 2⟩,
     ⟨199, 2⟩,
     ⟨.eq, ⟨4, 2⟩⟩⟩]

end BeltramaSchwarz2024
