module

public import Linglib.Data.Statistics.Schema

/-!
# KehlerRohde2013: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/KehlerRohde2013.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The passage-completion results the paper synthesizes from the authors' earlier experiments: an
aspect manipulation, an instruction manipulation, a prompt manipulation and a voice manipulation,
each reporting proportions of Source interpretations, coherence relations, next mentions or
pronominalized references. Proportions are printed to two places; the paper prints the Violated
Expectation relation as Violated Exp in Tables 3, 4 and 6. The first-mention rates of the prompt
manipulation and the figures of the worked example from Arnold (2001)'s Source-Goal data are printed
in the text, not in a table.

## References

* [kehler-rohde-2013]
-/

@[expose] public section

namespace KehlerRohde2013

open Data.Statistics

/-- The aspect of the context sentence, (7) against (8). -/
inductive Aspect where
  /-- Perfective: John passed a comic to Bill -/
  | perfective
  /-- Imperfective: John was passing a comic to Bill -/
  | imperfective
  deriving DecidableEq, Repr, Fintype

/-- The five most common coherence relations of the continuations. -/
inductive Relation where
  /-- Occasion: the continuation follows on the end state -/
  | occasion
  /-- Elaboration: the continuation redescribes the eventuality -/
  | elaboration
  /-- Explanation: the continuation gives a cause -/
  | explanation
  /-- Violated Expectation: the continuation runs against an expectation -/
  | violatedExpectation
  /-- Result: the continuation gives an effect -/
  | result
  deriving DecidableEq, Repr, Fintype

/-- The instruction of the instruction manipulation. -/
inductive Instruction where
  /-- What next?: What happened next? -/
  | whatNext
  /-- Why?: Why? -/
  | why
  deriving DecidableEq, Repr, Fintype

/-- Whether the prompt supplies a pronoun, (10a) against (10b). -/
inductive Prompt where
  /-- Pronoun: the prompt ends in He -/
  | pronoun
  /-- No Pronoun: the prompt ends after the context sentence -/
  | noPronoun
  deriving DecidableEq, Repr, Fintype

/-- The voice of the context sentence of the voice manipulation, (20). -/
inductive Voice where
  /-- Active: Amanda amazed Brittany -/
  | active
  /-- Passive: Brittany was amazed by Amanda -/
  | passive
  deriving DecidableEq, Repr, Fintype

/-- The grammatical position of the referent in the context sentence. -/
inductive Position where
  /-- Surface Subject: the subject -/
  | subject
  /-- Surface Non-Subject: the non-subject -/
  | nonSubject
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 1, p. 10: the proportion of Source interpretations by aspect. -/
structure AspectSource where
  /-- The proportion of Source interpretations. -/
  sourceInterpretation : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 10, by aspect; from an experiment; checked against the page images. -/
def sourceByAspect : Aspect → AspectSource
  | .perfective => ⟨⟨57, 2⟩⟩
  | .imperfective => ⟨⟨80, 2⟩⟩

/-- A row of Table 2, p. 11: the frequency of a coherence relation in the perfective condition
and its bias to the Source. -/
structure Perfective where
  /-- The proportion of continuations with the relation. -/
  frequency : Decimal
  /-- The proportion of its pronouns assigned to the Source. -/
  biasToSource : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 11, by relation; from an experiment; checked against the page
images. -/
def relationsPerfective : Relation → Perfective
  | .occasion => ⟨⟨38, 2⟩, ⟨18, 2⟩⟩
  | .elaboration => ⟨⟨28, 2⟩, ⟨98, 2⟩⟩
  | .explanation => ⟨⟨18, 2⟩, ⟨80, 2⟩⟩
  | .violatedExpectation => ⟨⟨8, 2⟩, ⟨76, 2⟩⟩
  | .result => ⟨⟨6, 2⟩, ⟨8, 2⟩⟩

/-- A row of Table 3, p. 13: the proportion of continuations with a coherence relation under an
instruction. -/
structure InstructionFrequency where
  /-- The proportion of continuations with the relation. -/
  frequency : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 3, p. 13, by relation and instruction; from an experiment; checked against
the page images. -/
def relationsByInstruction : Relation → Instruction → InstructionFrequency
  | .occasion, .whatNext => ⟨⟨71, 2⟩⟩
  | .occasion, .why => ⟨⟨1, 2⟩⟩
  | .elaboration, .whatNext => ⟨⟨5, 2⟩⟩
  | .elaboration, .why => ⟨⟨8, 2⟩⟩
  | .explanation, .whatNext => ⟨⟨1, 2⟩⟩
  | .explanation, .why => ⟨⟨91, 2⟩⟩
  | .violatedExpectation, .whatNext => ⟨⟨8, 2⟩⟩
  | .violatedExpectation, .why => ⟨⟨1, 2⟩⟩
  | .result, .whatNext => ⟨⟨5, 2⟩⟩
  | .result, .why => ⟨⟨0, 0⟩⟩

/-- A row of Table 4, p. 14: the bias of a coherence relation to the Source in the original
experiment and in the instruction manipulation. -/
structure ConditionedBias where
  /-- P(pronoun = Source | CR) in the original experiment. -/
  original : Decimal
  /-- P(pronoun = Source | CR) in the instruction manipulation. -/
  instructionManipulation : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 14, by relation; from an experiment; checked against the page
images. -/
def biasesByRelation : Relation → ConditionedBias
  | .occasion => ⟨⟨18, 2⟩, ⟨27, 2⟩⟩
  | .elaboration => ⟨⟨98, 2⟩, ⟨100, 2⟩⟩
  | .explanation => ⟨⟨80, 2⟩, ⟨82, 2⟩⟩
  | .violatedExpectation => ⟨⟨76, 2⟩, ⟨74, 2⟩⟩
  | .result => ⟨⟨8, 2⟩, ⟨9, 2⟩⟩

/-- A row of Table 5, p. 14: the proportion of Source interpretations under an instruction. -/
structure InstructionSource where
  /-- The proportion of Source interpretations. -/
  sourceInterpretation : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 5, p. 14, by instruction; from an experiment; checked against the page
images. -/
def sourceByInstruction : Instruction → InstructionSource
  | .whatNext => ⟨⟨34, 2⟩⟩
  | .why => ⟨⟨82, 2⟩⟩

/-- A row of Table 6, p. 17: the proportion of continuations with a coherence relation by prompt
type. -/
structure PromptFrequency where
  /-- The proportion of continuations with the relation. -/
  frequency : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 6, p. 17, by relation and prompt; from an experiment; checked against the
page images. -/
def relationsByPrompt : Relation → Prompt → PromptFrequency
  | .occasion, .noPronoun => ⟨⟨36, 2⟩⟩
  | .occasion, .pronoun => ⟨⟨28, 2⟩⟩
  | .elaboration, .noPronoun => ⟨⟨6, 2⟩⟩
  | .elaboration, .pronoun => ⟨⟨20, 2⟩⟩
  | .explanation, .noPronoun => ⟨⟨20, 2⟩⟩
  | .explanation, .pronoun => ⟨⟨28, 2⟩⟩
  | .violatedExpectation, .noPronoun => ⟨⟨18, 2⟩⟩
  | .violatedExpectation, .pronoun => ⟨⟨14, 2⟩⟩
  | .result, .noPronoun => ⟨⟨13, 2⟩⟩
  | .result, .pronoun => ⟨⟨5, 2⟩⟩

/-- A row of p. 16: the percentage of first mentions to the Goal by prompt type, printed in the
text. -/
structure GoalMention where
  /-- The percentage of first mentions to the Goal. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of p. 16, by prompt; from an experiment; checked against the page images. -/
def goalFirstMentions : Prompt → GoalMention
  | .noPronoun => ⟨84⟩
  | .pronoun => ⟨48⟩

/-- A row of Table 7, p. 24: the proportion of next mentions of the causally implicated referent
by voice and prompt. -/
structure CausalMention where
  /-- The proportion of next mentions of the causally implicated referent. -/
  proportion : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 7, p. 24, by voice and prompt; from an experiment; checked against the
page images. -/
def causalMentions : Voice → Prompt → CausalMention
  | .active, .pronoun => ⟨⟨77, 2⟩⟩
  | .active, .noPronoun => ⟨⟨59, 2⟩⟩
  | .passive, .pronoun => ⟨⟨42, 2⟩⟩
  | .passive, .noPronoun => ⟨⟨76, 2⟩⟩

/-- A row of Table 8, p. 24: the proportion of Explanation relations by voice and prompt. -/
structure ExplanationRate where
  /-- The proportion of Explanation relations. -/
  proportion : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 8, p. 24, by voice and prompt; from an experiment; checked against the
page images. -/
def explanations : Voice → Prompt → ExplanationRate
  | .active, .pronoun => ⟨⟨75, 2⟩⟩
  | .active, .noPronoun => ⟨⟨60, 2⟩⟩
  | .passive, .pronoun => ⟨⟨52, 2⟩⟩
  | .passive, .noPronoun => ⟨⟨72, 2⟩⟩

/-- A row of Table 9, p. 25: the proportion of pronominalized references to a position by voice. -/
structure Pronominalized where
  /-- The proportion of references that are pronouns. -/
  proportion : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 9, p. 25, by voice and position; from an experiment; checked against the
page images. -/
def pronominalizations : Voice → Position → Pronominalized
  | .active, .subject => ⟨⟨62, 2⟩⟩
  | .active, .nonSubject => ⟨⟨24, 2⟩⟩
  | .passive, .subject => ⟨⟨87, 2⟩⟩
  | .passive, .nonSubject => ⟨⟨23, 2⟩⟩

/-- A row of Table 10, p. 26: the predicted and the actual bias of a pronoun to the subject by
voice. -/
structure SubjectBias where
  /-- The bias predicted from the no-pronoun conditions. -/
  predicted : Decimal
  /-- The bias measured with the pronoun prompt. -/
  actual : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 10, p. 26, by voice; from an experiment; checked against the page images. -/
def subjectBiases : Voice → SubjectBias
  | .active => ⟨⟨81, 2⟩, ⟨74, 2⟩⟩
  | .passive => ⟨⟨59, 2⟩, ⟨60, 2⟩⟩

/-- A row of p. 15: the proportion of references to a position that were pronominalized in Arnold
(2001)'s Source-Goal contexts, the subject being the Source and the non-subject the Goal,
printed in the text. -/
structure ArnoldPronominalized where
  /-- The proportion of references that are pronouns. -/
  proportion : Decimal
  deriving DecidableEq, Repr

/-- The cells of p. 15, by position; from an experiment; checked against the page images. -/
def arnoldPronominalizations : Position → ArnoldPronominalized
  | .subject => ⟨⟨76, 2⟩⟩
  | .nonSubject => ⟨⟨20, 2⟩⟩

/-- A row of p. 15: the worked example of Equation (11) on Arnold (2001)'s data, printed in the
text: the next-mention probability of the Goal, the probability of a pronoun, and the
predicted interpretation bias of a pronoun toward the Goal. -/
structure ArnoldPrediction where
  /-- P(Goal), the next-mention probability of the Goal. -/
  goalNextMention : Decimal
  /-- P(pronoun), the probability of pronominalization. -/
  pronounRate : Decimal
  /-- The interpretation bias toward the Goal that Equation (11) predicts. -/
  goalInterpretation : Decimal
  deriving DecidableEq, Repr

/-- The row of p. 15; from an experiment; checked against the page images. -/
def arnoldPrediction : List ArnoldPrediction :=
  [⟨⟨86, 2⟩, ⟨28, 2⟩, ⟨61, 2⟩⟩]

end KehlerRohde2013
