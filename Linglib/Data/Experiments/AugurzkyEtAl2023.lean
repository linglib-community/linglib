module

public import Linglib.Data.Experiments.Schema

/-!
# AugurzkyEtAl2023: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/AugurzkyEtAl2023.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

Two web-based picture-sentence verification experiments with a plural definite bound by a
quantifier, 'Every boy opened his presents' against 'No boy opened his presents' (Experiment 1) and
against 'Not every boy opened his presents' (Experiment 2). Each picture shows four boys with nine
presents each, opened ones coloured and closed ones grey. CONTEXT, a family rule that the presents
be opened before the neighbours arrive (UNIVERSAL) or not before the grandparents arrive
(EXISTENTIAL), is between subjects and is reinforced by a secondary task asking whether the rule was
respected; TRUTH VALUE (true, false, mixed) and POLARITY (every against the negative quantifier) are
within subjects. Participants rated how well the sentence described the picture on a five-point
scale from 'completely false' to 'completely true'. The mixed conditions are analysed by cumulative
logistic mixed-effects models with CONTEXT sum-coded and POLARITY treatment-coded with the negative
quantifier as baseline, and random by-subject intercepts and slopes; CONTEXT is reported recoded as
Lax (EXISTENTIAL for every, UNIVERSAL for the negative quantifier) or Strict. The paper reports the
tests of the effects, not the cell means, which appear only in Figures 3 and 5.

## References

* [augurzky-etal-2023]
-/

@[expose] public section

namespace AugurzkyEtAl2023

open Data.Experiments

/-- The experiment. -/
inductive Experiment where
  /-- Experiment 1: every against no -/
  | one
  /-- Experiment 2: every against not every -/
  | two
  deriving DecidableEq, Repr, Fintype

/-- The quantifier binding the plural definite, the positive or negative level of POLARITY. -/
inductive Quantifier where
  /-- every: 'Every boy opened his presents' -/
  | every
  /-- no: 'No boy opened his presents' -/
  | no
  /-- not every: 'Not every boy opened his presents' -/
  | notEvery
  deriving DecidableEq, Repr, Fintype

/-- The factor CONTEXT: what the family rule makes relevant. -/
inductive Context where
  /-- EXISTENTIAL: wait for the grandparents before opening any presents, which raises whether
  any presents were opened -/
  | existential
  /-- UNIVERSAL: open the presents before the neighbours arrive, which raises whether all
  presents were opened -/
  | universal
  deriving DecidableEq, Repr, Fintype

/-- The factor TRUTH VALUE of a picture for a sentence. -/
inductive Truth where
  /-- true: the sentence is true on every reading -/
  | trueControl
  /-- false: the sentence is false on every reading -/
  | falseControl
  /-- mixed: the sentence is true on a non-maximal reading only -/
  | mixed
  deriving DecidableEq, Repr, Fintype

/-- The conditions a model was fitted to. -/
inductive Model where
  /-- mixed: the mixed conditions -/
  | mixed
  /-- controls: the true and false conditions -/
  | controls
  deriving DecidableEq, Repr, Fintype

/-- The term of a model that a test is of. -/
inductive Effect where
  /-- CONTEXT: the main effect of CONTEXT -/
  | context
  /-- POLARITY: the main effect of POLARITY -/
  | polarity
  /-- CONTEXT × POLARITY: the interaction of CONTEXT and POLARITY -/
  | interaction
  /-- CONTEXT and its interactions: the joint effect of CONTEXT and its interactions -/
  | contextTerms
  deriving DecidableEq, Repr, Fintype

/-- The boys in a picture. (§3.1.1; checked against the page images.) -/
def boys : ℕ := 4

/-- The presents of each boy. (§3.1.1; checked against the page images.) -/
def presents : ℕ := 9

/-- The points of the rating scale. (§3; checked against the PDF text layer only.) -/
def scalePoints : ℕ := 5

/-- The lists the items of each experiment were spread over. (§3.1.1, §3.2.1; checked against the
PDF text layer only.) -/
def lists : ℕ := 8

/-- The mean accuracy in Experiment 1 on the true and false conditions, in percent. (§3.1.2;
checked against the page images.) -/
def controlAccuracy : Decimal := ⟨983, 1⟩

/-- A row of §3.1.1, §3.2.1: the participants of an experiment, recruited from Prolific Academic,
and those excluded for an error rate of at least 25% on the controls. -/
structure Participants where
  /-- The native speakers of English recruited. -/
  recruited : ℕ
  /-- The participants excluded. -/
  excluded : ℕ
  deriving DecidableEq, Repr

/-- The cells of §3.1.1, §3.2.1, by experiment; checked against the PDF text layer only. -/
def participants : Experiment → Participants
  | .one => ⟨192, 7⟩
  | .two => ⟨192, 10⟩

/-- A row of Figures 1 and 4: the example picture the figure gives for a condition: how many of
his nine presents each boy opened, in the figure's order of the boys. -/
structure Picture where
  /-- The experiment. -/
  experiment : Experiment
  /-- The quantifier of the sentence. -/
  quantifier : Quantifier
  /-- The truth value of the picture for the sentence. -/
  truth : Truth
  /-- The presents each boy opened. -/
  opened : List ℕ
  deriving DecidableEq, Repr

/-- The 12 rows of Figures 1 and 4, in the paper's order; checked against the page images. -/
def pictures : List Picture :=
  [⟨.one, .every, .trueControl, [9, 9, 9, 9]⟩,
   ⟨.one, .every, .falseControl, [0, 0, 0, 0]⟩,
   ⟨.one, .every, .mixed, [5, 9, 3, 9]⟩,
   ⟨.one, .no, .trueControl, [0, 0, 0, 0]⟩,
   ⟨.one, .no, .falseControl, [9, 9, 9, 9]⟩,
   ⟨.one, .no, .mixed, [0, 4, 0, 3]⟩,  -- Nathan, Leo, Frank, Mike
   ⟨.two, .every, .trueControl, [9, 9, 9, 9]⟩,
   ⟨.two, .every, .falseControl, [0, 0, 0, 0]⟩,
   ⟨.two, .every, .mixed, [5, 9, 3, 9]⟩,
   ⟨.two, .notEvery, .trueControl, [0, 9, 0, 9]⟩,
   ⟨.two, .notEvery, .falseControl, [9, 9, 9, 9]⟩,
   ⟨.two,  -- §3.2.1 says two opened all and two none, the true control
     .notEvery,
     .mixed,
     [5, 9, 3, 9]⟩]

/-- A row of §3.1.2, §3.2.2: a χ² test of a term of a cumulative logistic mixed-effects model. -/
structure Test where
  /-- The experiment. -/
  experiment : Experiment
  /-- The conditions the model was fitted to. -/
  model : Model
  /-- The term tested. -/
  effect : Effect
  /-- The degrees of freedom of the chi-square statistic. -/
  df : ℕ
  /-- The chi-square statistic. -/
  chiSq : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 7 rows of §3.1.2, §3.2.2, in the paper's order; checked against the page images. -/
def tests : List Test :=
  [⟨.one, .mixed, .context, 1, ⟨49, 0⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.one, .mixed, .polarity, 1, ⟨93, 0⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.one, .mixed, .interaction, 1, ⟨11, 0⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.two, .controls, .contextTerms, 3, ⟨46, 2⟩, ⟨.eq, ⟨93, 2⟩⟩⟩,
   ⟨.two, .mixed, .context, 1, ⟨89, 0⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.two, .mixed, .polarity, 1, ⟨2, 2⟩, ⟨.eq, ⟨90, 2⟩⟩⟩,
   ⟨.two, .mixed, .interaction, 1, ⟨21, 1⟩, ⟨.eq, ⟨15, 2⟩⟩⟩]

end AugurzkyEtAl2023
