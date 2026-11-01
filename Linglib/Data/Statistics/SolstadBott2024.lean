module

public import Linglib.Data.Statistics.Schema

/-!
# SolstadBott2024: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/SolstadBott2024.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The three rating experiments on German occasion verbs. Block 1 of Experiments 1 and 2: the
acceptability of a trigger's sentence in a neutral context, after a sentence supplying the
projective content (anaphoric) and before one (cataphoric), on a slider transformed to [0, 1], with
the likelihood-ratio tests of a supported context against the neutral one. Block 2: the projectivity
and at-issueness of the occasion implication and of the implications of stimulus-experiencer and
experiencer-stimulus psychological verbs, in the paradigm of Tonhauser, Beaver and Degen (2018),
with 1 the maximal projectivity and the maximal at-issueness; the established triggers run alongside
are plotted only. Experiment 3: the projectivity of the content from a conditional antecedent
holding the trigger alone, before a conjunct entailing the content, or after one.

## Raw data

* <https://osf.io/76rxb/>: materials, trial-level data and the analysis scripts of the three
  experiments (footnote 6); the Block 1 means are recomputed from the archive
  RMD_files_occasion_verbs.zip

## References

* [solstad-bott-2024]
-/

@[expose] public section

namespace SolstadBott2024

open Data.Statistics

/-- The two experiments with a Block 2. -/
inductive Experiment where
  /-- Experiment 1: 16 occasion verbs beside seven established triggers, 71 participants -/
  | exp1
  /-- Experiment 2: 14 occasion verbs and 18 psychological verbs beside six established triggers,
  60 participants -/
  | exp2
  deriving DecidableEq, Repr, Fintype

/-- The Implicit Causality verb classes whose implications were rated. -/
inductive Trigger where
  /-- occasion verbs: agent-evocator verbs; the occasion implication -/
  | occasion
  /-- se-verbs: stimulus-experiencer psychological verbs -/
  | stimulusExperiencer
  /-- es-verbs: experiencer-stimulus psychological verbs -/
  | experiencerStimulus
  deriving DecidableEq, Repr, Fintype

/-- The unit over which a correlation was computed. -/
inductive Level where
  /-- trigger types: ratings aggregated over trigger types -/
  | triggerTypes
  /-- occasion verbs: the individual occasion verbs -/
  | occasionVerbs
  deriving DecidableEq, Repr, Fintype

/-- The context types of Block 1. -/
inductive Context where
  /-- neutral: the trigger's sentence after an introductory sentence only -/
  | neutral
  /-- anaphoric: a sentence supplying the projective content precedes the trigger's sentence -/
  | anaphoric
  /-- cataphoric: a sentence supplying the projective content follows the trigger's sentence -/
  | cataphoric
  deriving DecidableEq, Repr, Fintype

/-- The trigger types of Block 1 of Experiment 1. -/
inductive TriggerOne where
  /-- occasion verbs: the sixteen occasion verbs; the occasion implication -/
  | occasion
  /-- personal pronoun: the existence of a referent -/
  | pronoun
  /-- demonstrative NP: the speaker indicates a referent -/
  | demonstrative
  /-- possessive NP: the possessor implication -/
  | possessive
  /-- NRRC: the content of a non-restrictive relative clause -/
  | nrrc
  /-- know: wissen; the content of the complement -/
  | know
  /-- discover: entdecken; the content of the complement -/
  | discover
  /-- stop: aufhören; the prestate -/
  | stop
  deriving DecidableEq, Repr, Fintype

/-- The trigger types and verb classes of Block 1 of Experiment 2. -/
inductive TriggerTwo where
  /-- occasion verbs: the sixteen occasion verbs; the occasion implication -/
  | occasion
  /-- too: auch, ebenfalls; the existence of an alternative -/
  | too
  /-- again: wieder -/
  | again
  /-- definite article: definite descriptions -/
  | definite
  /-- manage: schaffen, the implicative -/
  | manage
  /-- cleft: clefts -/
  | cleft
  /-- appositive: appositives -/
  | appositive
  /-- es-verbs: experiencer-stimulus psychological verbs -/
  | experiencerStimulus
  /-- se-verbs: stimulus-experiencer psychological verbs -/
  | stimulusExperiencer
  deriving DecidableEq, Repr, Fintype

/-- The antecedent types of Experiment 3. -/
inductive Antecedent where
  /-- trigger first: the trigger's clause conjoined with a following clause entailing the content -/
  | triggerFirst
  /-- trigger last: the trigger's clause conjoined with a preceding clause entailing the content -/
  | triggerLast
  /-- trigger only: the trigger's clause alone -/
  | triggerOnly
  deriving DecidableEq, Repr, Fintype

/-- The two groups of items in Experiment 3. -/
inductive TriggerGroup where
  /-- occasion verbs: 24 items with the sixteen occasion verbs -/
  | occasion
  /-- Mandelkern triggers: 24 items translated from Mandelkern et al. (2020): sich freuen dass,
  wissen, aufhören, weiterhin -/
  | factiveAspectual
  deriving DecidableEq, Repr, Fintype

/-- Participants remaining in Experiment 1 after exclusions. (§2.2.1, p. 11:19; checked against
the page images.) -/
def participantsExp1 : ℕ := 71

/-- Native German participants in Experiment 2, all included in the analysis. (§3.1.1, pp.
11:30-31; checked against the page images.) -/
def participantsExp2 : ℕ := 60

/-- Participants remaining in Experiment 3 after exclusions. (§4.2.2, p. 11:44; checked against
the page images.) -/
def participantsExp3 : ℕ := 58

/-- A row of Figure 3, p. 11:27, plotted only: the mean acceptability rating of a trigger type's
sentence in a context type in Block 1 of Experiment 1, on [0, 1] with 1 completely acceptable -/
structure ContextMeanExp1 where
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figure 3, p. 11:27, plotted only, by trigger and context; from an experiment;
recomputed from the authors' released data by `scripts/check_statistics.py`. -/
def blockOneExp1 : TriggerOne → Context → ContextMeanExp1
  | .occasion, .neutral => ⟨⟨51, 2⟩⟩
  | .occasion, .anaphoric => ⟨⟨73, 2⟩⟩
  | .occasion, .cataphoric => ⟨⟨69, 2⟩⟩
  | .pronoun, .neutral => ⟨⟨24, 2⟩⟩
  | .pronoun, .anaphoric => ⟨⟨89, 2⟩⟩
  | .pronoun, .cataphoric => ⟨⟨25, 2⟩⟩
  | .demonstrative, .neutral => ⟨⟨24, 2⟩⟩
  | .demonstrative, .anaphoric => ⟨⟨71, 2⟩⟩
  | .demonstrative, .cataphoric => ⟨⟨30, 2⟩⟩
  | .possessive, .neutral => ⟨⟨73, 2⟩⟩
  | .possessive, .anaphoric => ⟨⟨76, 2⟩⟩
  | .possessive, .cataphoric => ⟨⟨38, 2⟩⟩
  | .nrrc, .neutral => ⟨⟨74, 2⟩⟩
  | .nrrc, .anaphoric => ⟨⟨47, 2⟩⟩
  | .nrrc, .cataphoric => ⟨⟨36, 2⟩⟩
  | .know, .neutral => ⟨⟨72, 2⟩⟩
  | .know, .anaphoric => ⟨⟨50, 2⟩⟩
  | .know, .cataphoric => ⟨⟨36, 2⟩⟩
  | .discover, .neutral => ⟨⟨86, 2⟩⟩
  | .discover, .anaphoric => ⟨⟨38, 2⟩⟩
  | .discover, .cataphoric => ⟨⟨35, 2⟩⟩
  | .stop, .neutral => ⟨⟨80, 2⟩⟩
  | .stop, .anaphoric => ⟨⟨77, 2⟩⟩
  | .stop, .cataphoric => ⟨⟨71, 2⟩⟩

/-- A row of §2.3.2, pp. 11:28-29: the likelihood-ratio tests of a supported context against the
neutral context for one trigger type in Block 1 of Experiment 1 -/
structure ContextTestExp1 where
  /-- The trigger type. -/
  trigger : TriggerOne
  /-- The context compared with the neutral one. -/
  context : Context
  /-- The χ² statistic. -/
  chiSquare : Decimal
  /-- Its degrees of freedom. -/
  df : ℕ
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 4 rows of §2.3.2, pp. 11:28-29, in the paper's order; from an experiment; checked against
the page images. -/
def contextTestsExp1 : List ContextTestExp1 :=
  [⟨.occasion, .anaphoric, ⟨2908, 2⟩, 1, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.occasion, .cataphoric, ⟨3672, 2⟩, 1, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.pronoun, .cataphoric, ⟨3, 2⟩, 1, ⟨.eq, ⟨87, 2⟩⟩⟩,
   ⟨.demonstrative, .cataphoric, ⟨192, 2⟩, 1, ⟨.eq, ⟨17, 2⟩⟩⟩]

/-- A row of Figure 7, p. 11:37, plotted only; the occasion-verb means are printed in §3.2.2, p.
11:36: the mean acceptability rating of a trigger type's sentence in a context type in Block
1 of Experiment 2, on [0, 1] with 1 completely acceptable -/
structure ContextMeanExp2 where
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figure 7, p. 11:37, plotted only; the occasion-verb means are printed in §3.2.2,
p. 11:36, by trigger and context; from an experiment; recomputed from the authors' released
data by `scripts/check_statistics.py`. -/
def blockOneExp2 : TriggerTwo → Context → ContextMeanExp2
  | .occasion, .neutral => ⟨⟨49, 2⟩⟩
  | .occasion, .anaphoric => ⟨⟨69, 2⟩⟩
  | .occasion, .cataphoric => ⟨⟨68, 2⟩⟩
  | .too, .neutral => ⟨⟨45, 2⟩⟩
  | .too, .anaphoric => ⟨⟨75, 2⟩⟩
  | .too, .cataphoric => ⟨⟨50, 2⟩⟩
  | .again, .neutral => ⟨⟨75, 2⟩⟩
  | .again, .anaphoric => ⟨⟨67, 2⟩⟩
  | .again, .cataphoric => ⟨⟨62, 2⟩⟩
  | .definite, .neutral => ⟨⟨70, 2⟩⟩
  | .definite, .anaphoric => ⟨⟨70, 2⟩⟩
  | .definite, .cataphoric => ⟨⟨51, 2⟩⟩
  | .manage, .neutral => ⟨⟨79, 2⟩⟩
  | .manage, .anaphoric => ⟨⟨74, 2⟩⟩
  | .manage, .cataphoric => ⟨⟨53, 2⟩⟩
  | .cleft, .neutral => ⟨⟨57, 2⟩⟩
  | .cleft, .anaphoric => ⟨⟨53, 2⟩⟩
  | .cleft, .cataphoric => ⟨⟨27, 2⟩⟩
  | .appositive, .neutral => ⟨⟨64, 2⟩⟩
  | .appositive, .anaphoric => ⟨⟨56, 2⟩⟩
  | .appositive, .cataphoric => ⟨⟨41, 2⟩⟩
  | .experiencerStimulus, .neutral => ⟨⟨69, 2⟩⟩
  | .experiencerStimulus, .anaphoric => ⟨⟨75, 2⟩⟩
  | .experiencerStimulus, .cataphoric => ⟨⟨74, 2⟩⟩
  | .stimulusExperiencer, .neutral => ⟨⟨59, 2⟩⟩
  | .stimulusExperiencer, .anaphoric => ⟨⟨72, 2⟩⟩
  | .stimulusExperiencer, .cataphoric => ⟨⟨69, 2⟩⟩

/-- A row of §3.2.2, pp. 11:36-37: the likelihood-ratio tests of a supported context against the
neutral context for one trigger type in Block 1 of Experiment 2 -/
structure ContextTestExp2 where
  /-- The trigger type. -/
  trigger : TriggerTwo
  /-- The context compared with the neutral one. -/
  context : Context
  /-- The χ² statistic. -/
  chiSquare : Decimal
  /-- Its degrees of freedom. -/
  df : ℕ
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 3 rows of §3.2.2, pp. 11:36-37, in the paper's order; from an experiment; checked against
the page images. -/
def contextTestsExp2 : List ContextTestExp2 :=
  [⟨.occasion, .anaphoric, ⟨2465, 2⟩, 1, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.occasion, .cataphoric, ⟨3162, 2⟩, 1, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.too, .cataphoric, ⟨115, 2⟩, 1, ⟨.eq, ⟨28, 2⟩⟩⟩]

/-- A row of §2.3.1, p. 11:25; §3.2.1, pp. 11:33-34; the by-trigger points of Figures 1 and 4 are
plotted only: the mean projectivity and at-issueness ratings of a verb class's implication in
Block 2, with the range over individual verbs where printed -/
structure Rating where
  /-- The experiment. -/
  experiment : Experiment
  /-- The verb class. -/
  trigger : Trigger
  /-- The number of verbs analysed. -/
  verbs : ℕ
  /-- Mean certain-that rating, 1 maximal. -/
  projectivity : Decimal
  /-- Mean asking-whether rating, 1 maximal at-issueness. -/
  atIssueness : Decimal
  /-- The range over individual verbs, where printed. -/
  projectivityRange : Option (List Decimal)
  /-- The range over individual verbs, where printed. -/
  atIssuenessRange : Option (List Decimal)
  deriving DecidableEq, Repr

/-- The 4 rows of §2.3.1, p. 11:25; §3.2.1, pp. 11:33-34; the by-trigger points of Figures 1 and
4 are plotted only, in the paper's order; from an experiment; checked against the page
images. -/
def blockTwo : List Rating :=
  [⟨.exp1, .occasion, 16, ⟨79, 2⟩, ⟨32, 2⟩, some [⟨73, 2⟩, ⟨87, 2⟩], some [⟨17, 2⟩, ⟨57, 2⟩]⟩,
   ⟨.exp2,  -- loben and gratulieren excluded for copy-and-paste errors, §3.2, p. 11:33
     .occasion,
     14,
     ⟨69, 2⟩,
     ⟨35, 2⟩,
     none,
     none⟩,
   ⟨.exp2, .stimulusExperiencer, 9, ⟨54, 2⟩, ⟨52, 2⟩, none, none⟩,
   ⟨.exp2, .experiencerStimulus, 9, ⟨52, 2⟩, ⟨46, 2⟩, none, none⟩]

/-- A row of §2.3.1, pp. 11:24-26; §3.2.1, p. 11:34: Pearson correlations of mean projectivity
with mean at-issueness -/
structure Correlation where
  /-- The experiment. -/
  experiment : Experiment
  /-- The unit of aggregation. -/
  level : Level
  /-- Pearson's r. -/
  r : Decimal
  /-- Degrees of freedom of the t test. -/
  df : ℕ
  /-- The t statistic. -/
  t : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 3 rows of §2.3.1, pp. 11:24-26; §3.2.1, p. 11:34, in the paper's order; from an
experiment; checked against the page images. -/
def correlations : List Correlation :=
  [⟨.exp1,  -- marginally significant; the sentence cites Tonhauser, Beaver and Degen 2018 as the pattern replicated
     .triggerTypes,
     ⟨-70, 2⟩,
     6,
     ⟨-237, 2⟩,
     ⟨.eq, ⟨6, 2⟩⟩⟩,
   ⟨.exp1,  -- one lexicalization per verb; the paper cautions against reading the breakdown as more than limited data
     .occasionVerbs,
     ⟨5, 2⟩,
     14,
     ⟨18, 2⟩,
     ⟨.eq, ⟨86, 2⟩⟩⟩,
   ⟨.exp2, .triggerTypes, ⟨-90, 2⟩, 7, ⟨-533, 2⟩, ⟨.lt, ⟨1, 2⟩⟩⟩]

/-- A row of Table 3, analyses B and C, p. 11:48: the follow-up regression of projectivity on
antecedent type for one group of items in Experiment 3, scaled to [0, 100], with the trigger-
first antecedent as the reference level: its mean, and the difference of each other
antecedent type from it -/
structure Contrast where
  /-- The parameter estimate. -/
  estimate : Decimal
  /-- Its standard error. -/
  sme : Decimal
  /-- The t value. -/
  t : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 3, analyses B and C, p. 11:48, by group and antecedent; from an
experiment; checked against the page images. -/
def followUp : TriggerGroup → Antecedent → Contrast
  | .occasion, .triggerFirst => ⟨⟨4621, 2⟩, ⟨232, 2⟩, ⟨1993, 2⟩⟩
  | .occasion, .triggerOnly => ⟨⟨2372, 2⟩, ⟨188, 2⟩, ⟨1260, 2⟩⟩
  | .occasion, .triggerLast => ⟨⟨-197, 2⟩, ⟨188, 2⟩, ⟨-105, 2⟩⟩
  | .factiveAspectual, .triggerFirst => ⟨⟨8185, 2⟩, ⟨234, 2⟩, ⟨3492, 2⟩⟩
  | .factiveAspectual, .triggerOnly => ⟨⟨353, 2⟩, ⟨185, 2⟩, ⟨191, 2⟩⟩
  | .factiveAspectual, .triggerLast => ⟨⟨-3016, 2⟩, ⟨185, 2⟩, ⟨-1633, 2⟩⟩

/-- A row of §4.3, p. 11:47: the likelihood-ratio test of the trigger-first against the trigger-
last antecedent for one group of items in Experiment 3 -/
structure OrderTest where
  /-- The χ² statistic. -/
  chiSquare : Decimal
  /-- Its degrees of freedom. -/
  df : ℕ
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of §4.3, p. 11:47, by group; from an experiment; checked against the page images. -/
def orderTests : TriggerGroup → OrderTest
  | .occasion => ⟨⟨130, 2⟩, 1, ⟨.eq, ⟨26, 2⟩⟩⟩
  | .factiveAspectual => ⟨⟨2076, 1⟩, 1, ⟨.lt, ⟨1, 3⟩⟩⟩

end SolstadBott2024
