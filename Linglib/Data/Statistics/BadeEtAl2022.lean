module

public import Linglib.Data.Statistics.Schema

/-!
# BadeEtAl2022: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/BadeEtAl2022.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

One inference-endorsement experiment crossing modal (epistemic might vs deontic allowed to, within
subjects) with the structure of the reasoning problem (canonical, flat, reversed, between subjects)
and the order of the conjuncts (within subjects). Participants judged whether the conclusion follows
from the premises; targets had the illusory-inference form modal(a and b), a therefore b.
Generalized linear mixed-effects contrasts are reported as printed, with Holm-corrected p-values;
the qualitative verdict column is the paper's prose reading of each contrast.

## References

* [bade-picat-chung-mascarenhas-2022]
-/

@[expose] public section

namespace BadeEtAl2022

open Data.Statistics

/-- The modal of the target items; deontic is the models' reference level. -/
inductive Modal where
  /-- Deontic: was allowed to -/
  | deontic
  /-- Epistemic: might have -/
  | epistemic
  deriving DecidableEq, Repr, Fintype

/-- The structure of the reasoning problem (12). -/
inductive Structure where
  /-- Canonical: modal(a and b); a, therefore b -/
  | canonical
  /-- Flat: a and modal(a and b), therefore b: one sentence, no question-answer dynamic -/
  | flat
  /-- Reversed: a; modal(a and b), therefore b -/
  | reversed
  deriving DecidableEq, Repr, Fintype

/-- Which conjunct of premise 1 appears in premise 2. -/
inductive Order where
  /-- Left: left conjunct in premise 2, right in the conclusion -/
  | left
  /-- Right: right conjunct in premise 2, left in the conclusion -/
  | right
  deriving DecidableEq, Repr, Fintype

/-- The pairwise comparisons of Tables 1-4; the first member is named first. -/
inductive Contrast where
  /-- Canon. vs. no-base.: canonical targets against no-baselines -/
  | canonicalVsBaseline
  /-- Canon. vs. rev.: canonical against reversed targets -/
  | canonicalVsReversed
  /-- Canon. vs. flat: canonical against flat targets -/
  | canonicalVsFlat
  /-- Flat vs. no-baseline: flat targets against no-baselines -/
  | flatVsBaseline
  /-- Reversed vs. no-baseline: reversed targets against no-baselines -/
  | reversedVsBaseline
  deriving DecidableEq, Repr, Fintype

/-- The paper's prose reading of a contrast: whether the first member drew more yes-responses. -/
inductive Verdict where
  /-- higher: significantly more yes-responses -/
  | higher
  /-- marginally higher: only marginally significant -/
  | marginallyHigher
  /-- no difference: no significant difference -/
  | noDifference
  /-- lower: significantly fewer yes-responses -/
  | lower
  deriving DecidableEq, Repr, Fintype

/-- The alternative-generating item of an illusory-inference paradigm. -/
inductive Generator where
  /-- disjunction: or else -/
  | disjunction
  /-- indefinite: some pilot -/
  | indefinite
  /-- might: epistemic might -/
  | might
  /-- allowed to: deontic allowed to -/
  | allowedTo
  deriving DecidableEq, Repr, Fintype

/-- The anatomy of illusory inferences from alternatives (section 3.2). -/
inductive Criterion where
  /-- A Fallacy: more fallacious conclusions than for invalid controls -/
  | fallacy
  /-- B Order of premises: fewer fallacious conclusions with reverse order -/
  | orderOfPremises
  /-- C Dynamics: no fallacious conclusions without dynamics -/
  | dynamics
  /-- D Rate: rate reflects the available mechanisms -/
  | rate
  deriving DecidableEq, Repr, Fintype

/-- The paper's verdict on a criterion for a generator. -/
inductive CriterionVerdict where
  /-- satisfied: the criterion holds -/
  | satisfied
  /-- failed: the criterion fails -/
  | failed
  /-- doubtful: the paper calls the status doubtful -/
  | doubtful
  deriving DecidableEq, Repr, Fintype

/-- The contrasts Mascarenhas and Picat (2019) report, as this paper summarizes them (11). -/
inductive PriorContrast where
  /-- canonical vs. invalid controls: -/
  | canonicalVsControls
  /-- reversed vs. invalid controls: -/
  | reversedVsControls
  /-- canonical vs. flat: -/
  | canonicalVsFlat
  /-- flat vs. invalid controls: -/
  | flatVsControls
  /-- canonical vs. P1: P1: the first premise alone -/
  | canonicalVsP1
  /-- canonical vs. reversed: the null result -/
  | canonicalVsReversed
  deriving DecidableEq, Repr, Fintype

/-- Participants recruited via Prolific. (§2.3.1, p. 2:13; checked against the PDF text layer
only.) -/
def recruited : ℕ := 183

/-- Participants excluded (14.2%). (§2.3.1, p. 2:13; checked against the PDF text layer only.) -/
def excluded : ℕ := 26

/-- Participants analyzed. (§2.3.1, p. 2:13; checked against the PDF text layer only.) -/
def analyzed : ℕ := 157

/-- Items per within-subjects condition. (§2.3.1, p. 2:12; checked against the PDF text layer
only.) -/
def itemsPerWithinCondition : ℕ := 6

/-- Critical items, distributed over four lists per structure group. (§2.3.1, p. 2:13; checked
against the PDF text layer only.) -/
def criticalItems : ℕ := 24

/-- Control items: valid and invalid modus ponens and disjunctive syllogism. (§2.3.1, p. 2:13;
checked against the PDF text layer only.) -/
def controlItems : ℕ := 12

/-- Baseline items: conjunction elimination, for the error-rate baseline. (§2.3.1, p. 2:13;
checked against the PDF text layer only.) -/
def baselineItems : ℕ := 12

/-- Reasoning problems each participant solved. (§2.3.1, p. 2:13; checked against the PDF text
layer only.) -/
def problemsPerParticipant : ℕ := 48

/-- Sub-experiments participants were randomly assigned to. (§2.3.1, p. 2:13; checked against the
PDF text layer only.) -/
def experimentalLists : ℕ := 12

/-- Log-likelihood-ratio chi-square for the structure-by-modal interaction, df 2. (§2.3.2, p.
2:14; checked against the PDF text layer only.) -/
def chiSqStructureModal : Decimal := ⟨33887, 3⟩

/-- Log-likelihood-ratio chi-square for the modal-by-order-by-structure interaction, df 6.
(§2.3.2, fn. 9, p. 2:17; checked against the PDF text layer only.) -/
def chiSqOrderInteraction : Decimal := ⟨13683, 3⟩

/-- Lower bound of the acceptance rate of illusory inferences from disjunction. (§1.1, p. 2:3;
checked against the PDF text layer only.) -/
def disjunctionAcceptanceLowPct : ℕ := 80

/-- Upper bound of the acceptance rate of illusory inferences from disjunction. (§1.1, p. 2:3;
checked against the PDF text layer only.) -/
def disjunctionAcceptanceHighPct : ℕ := 85

/-- Acceptance rate of illusory inferences with indefinites (Mascarenhas and Koralus 2017).
(§1.3, p. 2:5; checked against the PDF text layer only.) -/
def indefiniteAcceptancePct : ℕ := 35

/-- About half the participants drew the fallacious deontic conclusion. (§3.1, p. 2:20; checked
against the PDF text layer only.) -/
def deonticFallacyRatePct : ℕ := 50

/-- The drop in acceptance, in percentage points, under reversed premise order for disjunctions
and indefinites. (§3.2, p. 2:21; checked against the PDF text layer only.) -/
def orderDropPoints : ℕ := 10

/-- A row of Tables 1-4, pp. 2:14-2:17; verdicts §2.3.2-§2.4, pp. 2:13-2:18: a mixed-effects
contrast of Tables 1-4, with the paper's prose verdict. -/
structure Contrast10 where
  /-- The printed table the row is from. -/
  table : ℕ
  /-- The estimate. -/
  est : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The p-value. -/
  p : PValue
  /-- The Holm-corrected p-value. -/
  pCorr : PValue
  /-- The paper's reading of the contrast. -/
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The cells of Tables 1-4, pp. 2:14-2:17; verdicts §2.3.2-§2.4, pp. 2:13-2:18, by modal and
contrast; from an experiment; checked against the PDF text layer only. -/
def contrasts : Modal → Contrast → Contrast10
  | .deontic, .canonicalVsBaseline => ⟨1, ⟨69, 1⟩, ⟨15, 1⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 3⟩⟩, .higher⟩
  | .epistemic, .canonicalVsBaseline => ⟨1, ⟨62, 1⟩, ⟨15, 1⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 2⟩⟩, .higher⟩
  | .deontic, .canonicalVsReversed =>
    ⟨2,
     ⟨1, 2⟩,
     ⟨5, 1⟩,
     ⟨.eq, ⟨99, 2⟩⟩,
     ⟨.eq, ⟨99, 2⟩⟩,
     .noDifference⟩
  | .deontic, .canonicalVsFlat => ⟨2, ⟨15, 1⟩, ⟨5, 1⟩, ⟨.lt, ⟨1, 2⟩⟩, ⟨.lt, ⟨5, 2⟩⟩, .higher⟩
  | .epistemic, .canonicalVsReversed =>  -- the paper calls this contrast only marginally significant and the interaction suggestive of an order effect for epistemics
    ⟨2,
     ⟨98, 2⟩,
     ⟨5, 1⟩,
     ⟨.lt, ⟨6, 2⟩⟩,
     ⟨.eq, ⟨11, 2⟩⟩,
     .marginallyHigher⟩
  | .epistemic, .canonicalVsFlat => ⟨2, ⟨28, 1⟩, ⟨5, 1⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 3⟩⟩, .higher⟩
  | .epistemic, .flatVsBaseline =>
    ⟨3,
     ⟨5, 1⟩,
     ⟨22, 1⟩,
     ⟨.eq, ⟨83, 2⟩⟩,
     ⟨.eq, ⟨1, 0⟩⟩,
     .noDifference⟩
  | .epistemic, .reversedVsBaseline =>  -- the corrected p-value is printed smaller than the uncorrected one, as in the paper
    ⟨3,
     ⟨52, 1⟩,
     ⟨15, 1⟩,
     ⟨.eq, ⟨53, 5⟩⟩,
     ⟨.lt, ⟨1, 4⟩⟩,
     .higher⟩
  | .deontic, .flatVsBaseline =>  -- Table 4's caption misprints 'epistemics'; the text makes it the deontic table
    ⟨4,
     ⟨50, 1⟩,
     ⟨12, 1⟩,
     ⟨.lt, ⟨1, 4⟩⟩,
     ⟨.lt, ⟨1, 3⟩⟩,
     .higher⟩
  | .deontic, .reversedVsBaseline => ⟨4, ⟨65, 1⟩, ⟨12, 1⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 3⟩⟩, .higher⟩

/-- A row of Table 5, p. 2:17; §2.3.2, p. 2:17: the epistemic-against-deontic contrast within
each structure (Table 5); epistemic is named first. -/
structure ModalContrast where
  /-- The estimate. -/
  est : Decimal
  /-- The standard error. -/
  se : Decimal
  /-- The p-value. -/
  p : PValue
  /-- The Holm-corrected p-value. -/
  pCorr : PValue
  /-- Whether epistemics drew fewer yes-responses. -/
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The cells of Table 5, p. 2:17; §2.3.2, p. 2:17, by structure; from an experiment; checked
against the PDF text layer only. -/
def modalContrasts : Structure → ModalContrast
  | .canonical => ⟨⟨6, 1⟩, ⟨14, 2⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 2⟩⟩, .lower⟩
  | .flat => ⟨⟨19, 1⟩, ⟨2, 1⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 3⟩⟩, .lower⟩
  | .reversed => ⟨⟨16, 1⟩, ⟨2, 1⟩, ⟨.lt, ⟨1, 4⟩⟩, ⟨.lt, ⟨1, 3⟩⟩, .lower⟩

/-- A row of §2.1, p. 2:10: the findings of Mascarenhas and Picat (2019) as this paper reports
them. -/
structure PriorFinding where
  /-- The reported outcome. -/
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The cells of §2.1, p. 2:10, by contrast; from an experiment; checked against the PDF text
layer only. -/
def priorFindings : PriorContrast → PriorFinding
  | .canonicalVsControls => ⟨.higher⟩
  | .reversedVsControls => ⟨.higher⟩
  | .canonicalVsFlat => ⟨.higher⟩
  | .flatVsControls => ⟨.noDifference⟩
  | .canonicalVsP1 => ⟨.higher⟩
  | .canonicalVsReversed => ⟨.noDifference⟩

/-- A row of §3.2, pp. 2:21-2:22: the paper's verdict on each anatomy criterion for each
alternative generator. -/
structure AnatomyRow where
  /-- The paper's verdict. -/
  verdict : CriterionVerdict
  deriving DecidableEq, Repr

/-- The cells of §3.2, pp. 2:21-2:22, by generator and criterion; from an experiment; checked
against the PDF text layer only. -/
def anatomy : Generator → Criterion → AnatomyRow
  | .disjunction, .fallacy => ⟨.satisfied⟩
  | .disjunction, .orderOfPremises => ⟨.satisfied⟩
  | .disjunction, .dynamics => ⟨.satisfied⟩
  | .disjunction, .rate => ⟨.satisfied⟩
  | .indefinite, .fallacy => ⟨.satisfied⟩
  | .indefinite, .orderOfPremises => ⟨.satisfied⟩
  | .indefinite, .dynamics => ⟨.satisfied⟩
  | .indefinite, .rate => ⟨.satisfied⟩
  | .might, .fallacy => ⟨.satisfied⟩
  | .might, .orderOfPremises => ⟨.satisfied⟩
  | .might, .dynamics => ⟨.satisfied⟩
  | .might, .rate => ⟨.satisfied⟩
  | .allowedTo, .fallacy => ⟨.satisfied⟩
  | .allowedTo, .orderOfPremises => ⟨.failed⟩
  | .allowedTo, .dynamics => ⟨.failed⟩
  | .allowedTo, .rate => ⟨.doubtful⟩

end BadeEtAl2022
