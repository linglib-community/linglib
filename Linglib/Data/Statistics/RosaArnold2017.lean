module

public import Linglib.Data.Statistics.Schema

/-!
# RosaArnold2017: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/RosaArnold2017.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The pronoun rates of the three production experiments, an in-person event retelling, a sentence
completion over the story materials, and a sentence completion with disconnected items, by the
continued character's thematic role, its grammatical role, and whether the two characters share a
gender, with the next-mention rating study over the Experiment 1 stimuli. Page numbers are those of
the authors' accepted manuscript. Experiment 2 also codes each continuation's coherence relation,
collapsed into Occasion/Result and Other.

## References

* [rosa-arnold-2017]
-/

@[expose] public section

namespace RosaArnold2017

open Data.Statistics

/-- The three production experiments. -/
inductive Experiment where
  /-- 1: in-person event retelling -/
  | retelling
  /-- 2: sentence completion over the story materials -/
  | completion
  /-- 3: sentence completion with disconnected items -/
  | renamed
  deriving DecidableEq, Repr, Fintype

/-- The thematic role of the continued character. -/
inductive Role where
  /-- goal: the goal of the transfer -/
  | goal
  /-- source: the source of the transfer -/
  | source
  deriving DecidableEq, Repr, Fintype

/-- The grammatical role of the continued character in the prompt sentence. -/
inductive Gram where
  /-- subject: the subject -/
  | subject
  /-- nonsubject: a nonsubject -/
  | nonsubject
  deriving DecidableEq, Repr, Fintype

/-- Whether the two characters share a gender. -/
inductive Gender where
  /-- same-gender: the characters share a gender -/
  | same
  /-- different-gender: the characters differ in gender -/
  | different
  deriving DecidableEq, Repr, Fintype

/-- The coherence relation coded for a continuation in Experiment 2. -/
inductive CoherenceCode where
  /-- elaboration: elaboration -/
  | elaboration
  /-- explanation: explanation -/
  | explanation
  /-- occasion: occasion -/
  | occasion
  /-- parallel: parallel -/
  | parallel
  /-- result: result -/
  | result
  /-- violated expectations: violated expectations -/
  | violatedExpectation
  /-- background: background -/
  | background
  deriving DecidableEq, Repr, Fintype

/-- The two groups the coherence codes are collapsed into. -/
inductive CoherenceGroup where
  /-- Occasion/Result: occasion or result, events that follow the previous one -/
  | occasionResult
  /-- Other: every other continuation type -/
  | other
  deriving DecidableEq, Repr, Fintype

/-- The participants of the next-mention rating study. (Rating studies, manuscript p. 20; checked
against the page images.) -/
def raters : ℕ := 20

/-- The percentage of choices of the goal as the character more likely to be talked about next.
(Rating studies, manuscript p. 20; checked against the page images.) -/
def goalNextMention : ℕ := 71

/-- The percentage of choices of the subject as the character more likely to be talked about
next. (Rating studies, manuscript p. 20; checked against the page images.) -/
def subjectNextMention : ℕ := 54

/-- A row of Tables 1, 4 and 7 (manuscript pp. 25, 33, 38): the rate of pronoun production in a
cell of an experiment. -/
structure Rate where
  /-- The percentage of continuations with a pronoun, as printed. -/
  pronouns : ℕ
  deriving DecidableEq, Repr

/-- The cells of Tables 1, 4 and 7 (manuscript pp. 25, 33, 38), by experiment and gender and gram
and role; from an experiment; checked against the page images. -/
def rates : Experiment → Gender → Gram → Role → Rate
  | .retelling, .different, .subject, .goal => ⟨64⟩
  | .retelling, .different, .subject, .source => ⟨37⟩
  | .retelling, .different, .nonsubject, .goal => ⟨31⟩
  | .retelling, .different, .nonsubject, .source => ⟨18⟩
  | .retelling, .same, .subject, .goal => ⟨59⟩
  | .retelling, .same, .subject, .source => ⟨22⟩
  | .retelling, .same, .nonsubject, .goal => ⟨23⟩
  | .retelling, .same, .nonsubject, .source => ⟨15⟩
  | .completion, .different, .subject, .goal => ⟨83⟩
  | .completion, .different, .subject, .source => ⟨78⟩
  | .completion, .different, .nonsubject, .goal => ⟨55⟩
  | .completion, .different, .nonsubject, .source => ⟨33⟩
  | .completion, .same, .subject, .goal => ⟨69⟩
  | .completion, .same, .subject, .source => ⟨69⟩
  | .completion, .same, .nonsubject, .goal => ⟨18⟩
  | .completion, .same, .nonsubject, .source => ⟨19⟩
  | .renamed, .different, .subject, .goal => ⟨71⟩
  | .renamed, .different, .subject, .source => ⟨71⟩
  | .renamed, .different, .nonsubject, .goal => ⟨38⟩
  | .renamed, .different, .nonsubject, .source => ⟨33⟩
  | .renamed, .same, .subject, .goal => ⟨68⟩
  | .renamed, .same, .subject, .source => ⟨64⟩
  | .renamed, .same, .nonsubject, .goal => ⟨33⟩
  | .renamed, .same, .nonsubject, .source => ⟨10⟩

/-- A row of Tables 1 and 4 (manuscript pp. 25, 33): the overall rate of pronoun production for a
thematic role. -/
structure Overall where
  /-- The overall percentage; Table 7 prints none. -/
  pronouns : Option ℕ
  deriving DecidableEq, Repr

/-- The cells of Tables 1 and 4 (manuscript pp. 25, 33), by experiment and role; from an
experiment; checked against the page images. -/
def overall : Experiment → Role → Overall
  | .retelling, .goal => ⟨some 43⟩
  | .retelling, .source => ⟨some 23⟩
  | .completion, .goal => ⟨some 63⟩
  | .completion, .source => ⟨some 51⟩
  | .renamed, .goal => ⟨none⟩
  | .renamed, .source => ⟨none⟩

/-- A row of manuscript p. 32: the group each coherence code of Experiment 2 is collapsed into. -/
structure CoherenceGrouping where
  /-- The group it is collapsed into. -/
  group : CoherenceGroup
  deriving DecidableEq, Repr

/-- The cells of manuscript p. 32, by code; from an experiment; checked against the page images. -/
def coherenceGroups : CoherenceCode → CoherenceGrouping
  | .elaboration => ⟨.other⟩
  | .explanation => ⟨.other⟩
  | .occasion => ⟨.occasionResult⟩
  | .parallel => ⟨.other⟩
  | .result => ⟨.occasionResult⟩
  | .violatedExpectation => ⟨.other⟩
  | .background => ⟨.other⟩

/-- A row of manuscript p. 32: the number of Experiment 2 continuations by the continued
character's role and the coherence group. -/
structure ContinuationCount where
  /-- The number of continuations. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of manuscript p. 32, by role and group; from an experiment; checked against the
page images. -/
def continuationCounts : Role → CoherenceGroup → ContinuationCount
  | .goal, .occasionResult => ⟨120⟩
  | .goal, .other => ⟨103⟩
  | .source, .occasionResult => ⟨81⟩
  | .source, .other => ⟨121⟩

/-- A row of manuscript p. 33: the contrast in pronoun use between goal and source continuations
in Experiment 2, by coherence group. -/
structure GoalEffect where
  /-- The estimate β. -/
  estimate : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- The t-value. -/
  t : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of manuscript p. 33, by group; from an experiment; checked against the page images. -/
def goalEffects : CoherenceGroup → GoalEffect
  | .occasionResult => ⟨⟨122, 2⟩, ⟨40, 2⟩, ⟨306, 2⟩, ⟨.eq, ⟨2, 3⟩⟩⟩
  | .other => ⟨⟨86, 2⟩, ⟨55, 2⟩, ⟨156, 2⟩, ⟨.eq, ⟨12, 2⟩⟩⟩

/-- A row of Table 6, manuscript p. 34: the goal by coherence relation interaction of the
Experiment 2 production model. -/
structure CoherenceInteraction where
  /-- The estimate. -/
  estimate : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- The t-value. -/
  t : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The row of Table 6, manuscript p. 34; from an experiment; checked against the page images. -/
def coherenceInteraction : List CoherenceInteraction :=
  [⟨⟨108, 2⟩, ⟨57, 2⟩, ⟨188, 2⟩, ⟨.eq, ⟨6, 2⟩⟩⟩]

end RosaArnold2017
