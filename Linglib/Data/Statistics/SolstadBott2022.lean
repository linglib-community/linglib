module

public import Linglib.Data.Statistics.Schema

/-!
# SolstadBott2022: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/SolstadBott2022.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Four sentence-continuation experiments in German on stimulus-experiencer and experiencer-stimulus
verbs. Experiment 1 (52 participants): the referent of continuations after weil 'because' and sodass
'and so'. Experiment 2 (the same participants): the discourse relation and the referent of
continuations after a full stop. Experiment 3 (64 participants): the discourse relation of
continuations after a full stop that had to be about a marked argument. Experiment 4 (56
participants): the type of explanation or consequence after a connective and a pronoun congruent or
incongruent with the connective's bias. The verb gefallen 'appeal to' is excluded throughout.

## Raw data

* <https://osf.io/5ewbd/>: the data and analyses of the four experiments (note 3)

## References

* [solstad-bott-2022]
-/

@[expose] public section

namespace SolstadBott2022

open Data.Statistics

/-- The two classes of psychological verbs tested, twenty German verbs each. -/
inductive VerbClass where
  /-- STIM-EXP: stimulus-experiencer verbs such as ärgern 'annoy', VerbNet class 31.1 -/
  | stimExp
  /-- EXP-STIM: experiencer-stimulus verbs such as bewundern 'admire', VerbNet class 31.2 -/
  | expStim
  deriving DecidableEq, Repr, Fintype

/-- The connectives ending the prompts of Experiments 1 and 4. -/
inductive Connective where
  /-- weil: 'because' -/
  | because
  /-- sodass: 'and so' -/
  | andSo
  deriving DecidableEq, Repr, Fintype

/-- The two arguments of a prompt Name1 verb-ed Name2, in the subject-verb-object reading. -/
inductive Position where
  /-- subject: the first-mentioned argument, NP1 -/
  | subject
  /-- object: the second-mentioned argument, NP2 -/
  | object
  deriving DecidableEq, Repr, Fintype

/-- The three most common discourse relations of the continuations after a full stop. -/
inductive Relation where
  /-- Explanation: the continuation passes the weil 'because' insertion test -/
  | explanation
  /-- Consequence: the continuation passes the sodass 'and so' insertion test -/
  | consequence
  /-- Contrast: contrast or violated expectation, by the aber 'but' insertion test -/
  | contrast
  deriving DecidableEq, Repr, Fintype

/-- Whether the pronoun ending a prompt of Experiment 4 refers to the argument the connective is
biased to. -/
inductive Congruency where
  /-- congruent: the pronoun refers to the biased argument -/
  | congruent
  /-- incongruent: the pronoun refers to the other argument -/
  | incongruent
  deriving DecidableEq, Repr, Fintype

/-- The correlation between the mean I-Caus and I-Cons biases of the verbs in Experiment 1.
(Section 2.3, p. 1322; checked against the page images.) -/
def biasCorrelation : Decimal := ⟨-94, 2⟩

/-- A row of Table 1, p. 1322: the referent of the continuations in Experiment 1, by connective
and verb class. -/
structure Coreference where
  /-- The percentage of continuations referring to the argument. -/
  percent : Decimal
  /-- The number of continuations referring to the argument. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 1322, by connective and verbClass and reference; from an experiment;
checked against the page images. -/
def coreference : Connective → VerbClass → Position → Coreference
  | .because, .stimExp, .subject => ⟨⟨874, 1⟩, 388⟩
  | .because, .stimExp, .object => ⟨⟨126, 1⟩, 56⟩
  | .because, .expStim, .subject => ⟨⟨40, 1⟩, 20⟩
  | .because, .expStim, .object => ⟨⟨960, 1⟩, 474⟩
  | .andSo, .stimExp, .subject => ⟨⟨48, 1⟩, 21⟩
  | .andSo, .stimExp, .object => ⟨⟨952, 1⟩, 419⟩
  | .andSo, .expStim, .subject => ⟨⟨779, 1⟩, 339⟩
  | .andSo, .expStim, .object => ⟨⟨221, 1⟩, 96⟩

/-- A row of Section 3.3, p. 1325: the share of a discourse relation among the continuations
after a full stop in Experiment 2, printed in the text. -/
structure RelationShare where
  /-- The percentage of continuations with the relation. -/
  percent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Section 3.3, p. 1325, by verbClass and relation; from an experiment; checked
against the page images. -/
def relations : VerbClass → Relation → RelationShare
  | .stimExp, .explanation => ⟨⟨582, 1⟩⟩
  | .stimExp, .consequence =>  -- printed as 21.1 with Figure 3 and as 21.4 with the regression on the same page
    ⟨⟨211, 1⟩⟩
  | .stimExp, .contrast => ⟨⟨58, 1⟩⟩
  | .expStim, .explanation => ⟨⟨602, 1⟩⟩
  | .expStim, .consequence => ⟨⟨99, 1⟩⟩
  | .expStim, .contrast => ⟨⟨148, 1⟩⟩

/-- A row of Table 3, p. 1326: the referent of the continuations in Experiment 2, by the
discourse relation produced and verb class. -/
structure RelationCoreference where
  /-- The percentage of continuations referring to the argument. -/
  percent : Decimal
  /-- The number of continuations referring to the argument. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 3, p. 1326, by relation and verbClass and reference; from an experiment;
checked against the page images. -/
def coreferenceByRelation : Relation → VerbClass → Position → RelationCoreference
  | .explanation, .stimExp, .subject => ⟨⟨792, 1⟩, 401⟩
  | .explanation, .stimExp, .object => ⟨⟨208, 1⟩, 105⟩
  | .explanation, .expStim, .subject => ⟨⟨73, 1⟩, 41⟩
  | .explanation, .expStim, .object => ⟨⟨927, 1⟩, 520⟩
  | .consequence, .stimExp, .subject => ⟨⟨32, 1⟩, 6⟩
  | .consequence, .stimExp, .object => ⟨⟨968, 1⟩, 184⟩
  | .consequence, .expStim, .subject => ⟨⟨845, 1⟩, 71⟩
  | .consequence, .expStim, .object => ⟨⟨155, 1⟩, 13⟩
  | .contrast, .stimExp, .subject => ⟨⟨257, 1⟩, 9⟩
  | .contrast, .stimExp, .object => ⟨⟨743, 1⟩, 26⟩
  | .contrast, .expStim, .subject => ⟨⟨192, 1⟩, 23⟩
  | .contrast, .expStim, .object => ⟨⟨808, 1⟩, 97⟩

/-- A row of Section 4.4, p. 1328: the shares of explanations and consequences among the
continuations of Experiment 3, by verb class and the argument the continuation had to be
about, printed in the text. -/
structure ForcedReference where
  /-- The percentage of explanations. -/
  explanation : Decimal
  /-- The percentage of consequences. -/
  consequence : Decimal
  deriving DecidableEq, Repr

/-- The cells of Section 4.4, p. 1328, by verbClass and reference; from an experiment; checked
against the page images. -/
def forcedReference : VerbClass → Position → ForcedReference
  | .stimExp, .subject => ⟨⟨838, 1⟩, ⟨37, 1⟩⟩
  | .stimExp, .object => ⟨⟨429, 1⟩, ⟨442, 1⟩⟩
  | .expStim, .subject => ⟨⟨491, 1⟩, ⟨324, 1⟩⟩
  | .expStim, .object => ⟨⟨767, 1⟩, ⟨30, 1⟩⟩

/-- A row of Table 4, p. 1333: explanations and consequences of Experiment 4 that specify the
contingency relation of the predicate, by verb class and congruency; consequence
specifications are merged with proximate experiencer-consequences. -/
structure Specification where
  /-- The percentage of explanations that are broadly specifying. -/
  explanationSpecifyingPercent : Decimal
  /-- The number of broadly specifying explanations. -/
  explanationSpecifying : ℕ
  /-- The percentage of other explanations. -/
  explanationOtherPercent : Decimal
  /-- The number of other explanations. -/
  explanationOther : ℕ
  /-- The percentage of consequences that are broadly specifying. -/
  consequenceSpecifyingPercent : Decimal
  /-- The number of broadly specifying consequences. -/
  consequenceSpecifying : ℕ
  /-- The percentage of other consequences. -/
  consequenceOtherPercent : Decimal
  /-- The number of other consequences. -/
  consequenceOther : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 1333, by verbClass and congruency; from an experiment; checked
against the page images. -/
def specifications : VerbClass → Congruency → Specification
  | .stimExp, .congruent => ⟨⟨876, 1⟩, 227, ⟨124, 1⟩, 32, ⟨240, 1⟩, 62, ⟨760, 1⟩, 196⟩
  | .stimExp, .incongruent => ⟨⟨30, 1⟩, 6, ⟨970, 1⟩, 193, ⟨79, 1⟩, 14, ⟨921, 1⟩, 164⟩
  | .expStim, .congruent => ⟨⟨982, 1⟩, 271, ⟨18, 1⟩, 5, ⟨42, 1⟩, 11, ⟨958, 1⟩, 250⟩
  | .expStim, .incongruent => ⟨⟨85, 1⟩, 22, ⟨915, 1⟩, 236, ⟨4, 1⟩, 1, ⟨996, 1⟩, 244⟩

end SolstadBott2022
