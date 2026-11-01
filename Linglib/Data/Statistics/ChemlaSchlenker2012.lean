module

public import Linglib.Data.Statistics.Schema

/-!
# ChemlaSchlenker2012: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/ChemlaSchlenker2012.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Five experiments on French sentences with the anaphoric trigger aussi ('too') in if-, or- and
unless-sentences, in the canonical order, where the clause that can satisfy the presupposition
precedes the trigger, and the inverse order, where it follows. Experiments 1 and 4 collected
inferential judgments, rating on a continuous scale from no to yes whether the conditional or the
unconditional presupposition follows from a sentence; Experiments 2, 3 and 5 collected acceptability
judgments, with control sentences for local accommodation with too and with the, a justified
presupposition and no presupposition. Experiments 1 and 2 were run on one group of participants, 3
and 4 on a second, and 5, with complex fillers, on a third (Table 3). The tables print means and,
for the inferential experiments, one-way ANOVAs comparing the two inferences; standard errors are
shown only as error bars and are not recorded.

## References

* [chemla-schlenker-2012]
-/

@[expose] public section

namespace ChemlaSchlenker2012

open Data.Statistics

/-- The connective of a target sentence (§2.5, (48)–(49)). -/
inductive Construction where
  /-- if: a conditional, 'if p, qq'' or 'if not qq', not p' -/
  | ifSentence
  /-- or: a disjunction, '(not p) or qq'' or 'qq' or (not p)' -/
  | orSentence
  /-- unless: an unless-sentence, 'unless qq', not p'; only the inverse order was tested -/
  | unlessSentence
  deriving DecidableEq, Repr, Fintype

/-- The order of the trigger and the clause that can satisfy its presupposition ((48)–(49)). -/
inductive Order where
  /-- canonical: the satisfying clause precedes the trigger -/
  | canonical
  /-- inverse: the trigger precedes the satisfying clause -/
  | inverse
  deriving DecidableEq, Repr, Fintype

/-- The inference rated in the inferential judgment task ((56)). -/
inductive Inference where
  /-- conditional: the conditional presupposition, 'studying abroad would be stupid of Ann' -/
  | conditional
  /-- unconditional: the unconditional presupposition, 'Ann will make a stupid decision' -/
  | unconditional
  deriving DecidableEq, Repr, Fintype

/-- The control sentences of the acceptability judgment tasks ((57)–(60)). -/
inductive Control where
  /-- (57) local accommodation too: a negated too-sentence whose presupposition must be
  accommodated locally -/
  | localAccommodationToo
  /-- (58) justified presupposition: a too-sentence whose presupposition is satisfied by the
  preceding sentence -/
  | justifiedPresupposition
  /-- (59) non presuppositional: the sentence without a trigger -/
  | nonPresuppositional
  /-- (60) local accommodation the: a negated definite description whose presupposition must be
  accommodated locally -/
  | localAccommodationThe
  deriving DecidableEq, Repr, Fintype

/-- The participants of Experiments 1 and 2. (§3.1.1.1, p. 202; checked against the PDF text
layer only.) -/
def participantsGroup1 : ℕ := 18

/-- The participants of Experiments 3 and 4. (§3.3.1.1, p. 210; checked against the PDF text
layer only.) -/
def participantsGroup2 : ℕ := 17

/-- The participants of Experiment 5. (§3.4.1.1, p. 213; checked against the page images.) -/
def participantsGroup3 : ℕ := 16

/-- A row of Table 4, p. 206: the mean rating of an inference drawn from a target sentence in
Experiment 1. -/
structure Experiment1Inference where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The inference whose robustness is rated. -/
  inference : Inference
  /-- The mean rating, normalized per participant, as a percentage of the scale from no to yes. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 10 rows of Table 4, p. 206, in the paper's order; from an experiment; checked against the
page images. -/
def experiment1Inferences : List Experiment1Inference :=
  [⟨.ifSentence, .canonical, .conditional, ⟨87, 0⟩⟩,
   ⟨.ifSentence, .canonical, .unconditional, ⟨58, 0⟩⟩,
   ⟨.ifSentence, .inverse, .conditional, ⟨73, 0⟩⟩,
   ⟨.ifSentence, .inverse, .unconditional, ⟨49, 0⟩⟩,
   ⟨.orSentence, .canonical, .conditional, ⟨75, 0⟩⟩,
   ⟨.orSentence, .canonical, .unconditional, ⟨40, 0⟩⟩,
   ⟨.orSentence, .inverse, .conditional, ⟨75, 0⟩⟩,
   ⟨.orSentence, .inverse, .unconditional, ⟨58, 0⟩⟩,
   ⟨.unlessSentence, .inverse, .conditional, ⟨67, 0⟩⟩,
   ⟨.unlessSentence, .inverse, .unconditional, ⟨33, 0⟩⟩]

/-- A row of Table 4, p. 206: the one-way ANOVA comparing the two inferences from a target
sentence in Experiment 1. -/
structure Experiment1Test where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The error degrees of freedom of the one-way ANOVA F(1, dfError). -/
  dfError : ℕ
  /-- The F statistic. -/
  f : Decimal
  /-- The p-value. -/
  p : PValue
  /-- The partial eta squared. -/
  eta2 : Decimal
  deriving DecidableEq, Repr

/-- The 5 rows of Table 4, p. 206, in the paper's order; from an experiment; checked against the
page images. -/
def experiment1Tests : List Experiment1Test :=
  [⟨.ifSentence, .canonical, 17, ⟨32, 0⟩, ⟨.lt, ⟨1, 3⟩⟩, ⟨40, 2⟩⟩,
   ⟨.ifSentence, .inverse, 17, ⟨16, 0⟩, ⟨.lt, ⟨1, 3⟩⟩, ⟨33, 2⟩⟩,
   ⟨.orSentence, .canonical, 17, ⟨45, 0⟩, ⟨.lt, ⟨1, 3⟩⟩, ⟨42, 2⟩⟩,
   ⟨.orSentence, .inverse, 17, ⟨66, 1⟩, ⟨.lt, ⟨5, 2⟩⟩, ⟨22, 2⟩⟩,
   ⟨.unlessSentence, .inverse, 17, ⟨22, 0⟩, ⟨.lt, ⟨1, 3⟩⟩, ⟨36, 2⟩⟩]

/-- A row of Table 5, p. 209: the mean acceptability of a target sentence in Experiment 2. -/
structure Experiment2Target where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The mean acceptability rating, as a percentage of the scale. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 5 rows of Table 5, p. 209, in the paper's order; from an experiment; checked against the
page images. -/
def experiment2Targets : List Experiment2Target :=
  [⟨.ifSentence, .inverse, ⟨60, 0⟩⟩,
   ⟨.ifSentence, .canonical, ⟨87, 0⟩⟩,
   ⟨.orSentence, .inverse, ⟨55, 0⟩⟩,
   ⟨.orSentence, .canonical, ⟨53, 0⟩⟩,
   ⟨.unlessSentence, .inverse, ⟨64, 0⟩⟩]

/-- A row of Table 5, p. 209: the mean acceptability of a control sentence in Experiment 2. -/
structure Experiment2Control where
  /-- The mean acceptability rating, as a percentage of the scale. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 5, p. 209, by control; from an experiment; checked against the page
images. -/
def experiment2Controls : Control → Experiment2Control
  | .localAccommodationToo => ⟨⟨32, 0⟩⟩
  | .justifiedPresupposition => ⟨⟨80, 0⟩⟩
  | .nonPresuppositional => ⟨⟨71, 0⟩⟩
  | .localAccommodationThe => ⟨⟨54, 0⟩⟩

/-- A row of Table 6, p. 211: the mean acceptability of a target sentence in Experiment 3. -/
structure Experiment3Target where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The mean acceptability rating, as a percentage of the scale. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 5 rows of Table 6, p. 211, in the paper's order; from an experiment; checked against the
page images. -/
def experiment3Targets : List Experiment3Target :=
  [⟨.ifSentence, .inverse, ⟨41, 0⟩⟩,
   ⟨.ifSentence, .canonical, ⟨83, 0⟩⟩,
   ⟨.orSentence, .inverse, ⟨36, 0⟩⟩,
   ⟨.orSentence, .canonical, ⟨30, 0⟩⟩,
   ⟨.unlessSentence, .inverse, ⟨42, 0⟩⟩]

/-- A row of Table 6, p. 211: the mean acceptability of a control sentence in Experiment 3. -/
structure Experiment3Control where
  /-- The mean acceptability rating, as a percentage of the scale. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 6, p. 211, by control; from an experiment; checked against the page
images. -/
def experiment3Controls : Control → Experiment3Control
  | .localAccommodationToo => ⟨⟨28, 0⟩⟩
  | .justifiedPresupposition => ⟨⟨80, 0⟩⟩
  | .nonPresuppositional => ⟨⟨78, 0⟩⟩
  | .localAccommodationThe => ⟨⟨77, 0⟩⟩

/-- A row of Table 7, p. 212: the mean rating of an inference drawn from a target sentence in
Experiment 4. -/
structure Experiment4Inference where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The inference whose robustness is rated. -/
  inference : Inference
  /-- The mean rating, normalized per participant, as a percentage of the scale from no to yes. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 10 rows of Table 7, p. 212, in the paper's order; from an experiment; checked against the
page images. -/
def experiment4Inferences : List Experiment4Inference :=
  [⟨.ifSentence, .canonical, .conditional, ⟨83, 0⟩⟩,
   ⟨.ifSentence, .canonical, .unconditional, ⟨64, 0⟩⟩,
   ⟨.ifSentence, .inverse, .conditional, ⟨61, 0⟩⟩,
   ⟨.ifSentence, .inverse, .unconditional, ⟨50, 0⟩⟩,
   ⟨.orSentence, .canonical, .conditional, ⟨64, 0⟩⟩,
   ⟨.orSentence, .canonical, .unconditional, ⟨36, 0⟩⟩,
   ⟨.orSentence, .inverse, .conditional, ⟨66, 0⟩⟩,
   ⟨.orSentence, .inverse, .unconditional, ⟨54, 0⟩⟩,
   ⟨.unlessSentence, .inverse, .conditional, ⟨63, 0⟩⟩,
   ⟨.unlessSentence, .inverse, .unconditional, ⟨39, 0⟩⟩]

/-- A row of Table 7, p. 212: the one-way ANOVA comparing the two inferences from a target
sentence in Experiment 4. -/
structure Experiment4Test where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The error degrees of freedom of the one-way ANOVA F(1, dfError). -/
  dfError : ℕ
  /-- The F statistic. -/
  f : Decimal
  /-- The p-value. -/
  p : PValue
  /-- The partial eta squared. -/
  eta2 : Decimal
  deriving DecidableEq, Repr

/-- The 5 rows of Table 7, p. 212, in the paper's order; from an experiment; checked against the
page images. -/
def experiment4Tests : List Experiment4Test :=
  [⟨.ifSentence, .canonical, 16, ⟨11, 0⟩, ⟨.lt, ⟨1, 2⟩⟩, ⟨29, 2⟩⟩,
   ⟨.ifSentence, .inverse, 16, ⟨20, 1⟩, ⟨.eq, ⟨18, 2⟩⟩, ⟨10, 2⟩⟩,
   ⟨.orSentence, .canonical, 16, ⟨23, 0⟩, ⟨.lt, ⟨1, 3⟩⟩, ⟨37, 2⟩⟩,
   ⟨.orSentence, .inverse, 16, ⟨42, 1⟩, ⟨.eq, ⟨56, 3⟩⟩, ⟨17, 2⟩⟩,
   ⟨.unlessSentence, .inverse, 16, ⟨11, 0⟩, ⟨.lt, ⟨1, 2⟩⟩, ⟨29, 2⟩⟩]

/-- A row of Table 8, p. 214: the mean acceptability of a target sentence in Experiment 5. -/
structure Experiment5Target where
  /-- The connective of the target sentence. -/
  construction : Construction
  /-- The order of the trigger and the filtering clause. -/
  order : Order
  /-- The mean acceptability rating, as a percentage of the scale. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The 5 rows of Table 8, p. 214, in the paper's order; from an experiment; checked against the
page images. -/
def experiment5Targets : List Experiment5Target :=
  [⟨.ifSentence, .inverse, ⟨52, 0⟩⟩,
   ⟨.ifSentence, .canonical, ⟨86, 0⟩⟩,
   ⟨.orSentence, .inverse, ⟨49, 0⟩⟩,
   ⟨.orSentence, .canonical, ⟨45, 0⟩⟩,
   ⟨.unlessSentence, .inverse, ⟨60, 0⟩⟩]

/-- A row of Table 8, p. 214: the mean acceptability of a control sentence in Experiment 5. -/
structure Experiment5Control where
  /-- The mean acceptability rating, as a percentage of the scale. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 8, p. 214, by control; from an experiment; checked against the page
images. -/
def experiment5Controls : Control → Experiment5Control
  | .localAccommodationToo => ⟨⟨45, 0⟩⟩
  | .justifiedPresupposition => ⟨⟨78, 0⟩⟩
  | .nonPresuppositional => ⟨⟨83, 0⟩⟩
  | .localAccommodationThe => ⟨⟨77, 0⟩⟩

end ChemlaSchlenker2012
