module

public import Linglib.Data.Experiments.Schema

/-!
# KrizChemla2015: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/KrizChemla2015.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Truth-value judgments of sentences with a plural definite, unembedded and in the scope of negation,
all or every, no, and exactly two, against displays of nine symbols, or of four cells of nine
symbols each (Experiments A0 to A3, B1 to B3), or against pictures of four boys with nine presents
each (C2 to C4). Method A asks one group whether a sentence is completely true and another whether
it is completely false; method B offers completely true, completely false and neither. A gap is
diagnosed by three logistic mixed-effects comparisons of the target sentences (the) with the
controls (all the).

## References

* [kriz-chemla-2015]
-/

@[expose] public section

namespace KrizChemla2015

open Data.Experiments

/-- The experiment; method A asks one group whether a sentence is completely true and another
whether it is completely false, method B offers completely true, completely false and
neither. -/
inductive Experiment where
  /-- A0: Method A, unembedded. -/
  | a0
  /-- A1: Method A, unembedded and under negation. -/
  | a1
  /-- A2: Method A, under all and no. -/
  | a2
  /-- A3: Method A, under all and exactly. -/
  | a3
  /-- B1: Method B, unembedded and under negation. -/
  | b1
  /-- B2: Method B, under all and no. -/
  | b2
  /-- B3: Method B, under all and exactly. -/
  | b3
  /-- C2: Presents pictures, under every and no. -/
  | c2
  /-- C3: Presents pictures, under all and exactly, with GAP?. -/
  | c3
  /-- C4: Presents pictures, under all and exactly, with GAP??. -/
  | c4
  deriving DecidableEq, Repr, Fintype

/-- The environment the plural definite is embedded in. -/
inductive Embedding where
  /-- E-∅: The definite is unembedded, (11): 'The triangles are blue'. -/
  | unembedded
  /-- E-neg: The definite is under sentential negation: 'The triangles are not blue'. -/
  | negation
  /-- E-all: The definite is in the scope of all, (12), or every, (19): 'In all the cells, the
  symbols are green', 'Every boy found his presents'. -/
  | all
  /-- E-no: The definite is in the scope of no, (13), (20): 'No boy found his presents'. -/
  | no
  /-- E-exactly: The definite is in the scope of exactly two, (17), (24): 'Exactly 2 of the 4
  boys found their presents'. -/
  | exactly
  deriving DecidableEq, Repr, Fintype

/-- The situation type a display realizes for its sentence. -/
inductive Condition where
  /-- TRUE: The sentence is designed to be true. -/
  | clearlyTrue
  /-- FALSE: The sentence is designed to be false. -/
  | clearlyFalse
  /-- GAP: The variants with some and with all in place of the definite differ. -/
  | gap
  /-- GAP?: Under exactly n, more than n cells contain target symbols and fewer than n contain
  only target symbols. -/
  | gapQ
  /-- GAP??: Under exactly n, exactly n cells contain only target symbols and another contains
  some. -/
  | gapQQ
  deriving DecidableEq, Repr, Fintype

/-- How Table 13 marks an item. -/
inductive ItemStatus where
  /-- unmarked: The item was used as listed. -/
  | used
  /-- round brackets: The item was faulty in Experiments A2 and B2 and excluded from the
  analysis. -/
  | faulty
  /-- square brackets: The item replaced a faulty one in Experiment C2. -/
  | replacement
  deriving DecidableEq, Repr, Fintype

/-- Whether evidence for a gap was found. -/
inductive Found where
  /-- yes: Table 2 frames the cell, Table 12 prints yes. -/
  | yes
  /-- no: Table 2 leaves the cell unframed, Table 12 prints no. -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- How many of their students a teacher likes in a situation of Table 12. -/
inductive Share where
  /-- all: All of them. -/
  | all
  /-- half: Half of them. -/
  | half
  /-- none: None of them. -/
  | none
  deriving DecidableEq, Repr, Fintype

/-- The symbols in a cell, or the presents of a boy. (§2.1.2, §5.2.2; checked against the page
images.) -/
def symbols : ℕ := 9

/-- The cells of an embedded display, or the boys of a picture. (§3.2.2, (24); checked against
the page images.) -/
def cells : ℕ := 4

/-- The numeral of the E-exactly sentences. ((17), (24); checked against the page images.) -/
def numeral : ℕ := 2

/-- A row of Table 2: each experiment's test of a gap condition and whether it found evidence for
a gap, the framed cells of Table 2. -/
structure GapTest where
  /-- The experiment. -/
  experiment : Experiment
  /-- The environment. -/
  embedding : Embedding
  /-- The gap condition. -/
  condition : Condition
  /-- Whether the cell is framed. -/
  found : Found
  deriving DecidableEq, Repr

/-- The 27 rows of Table 2, in the paper's order; checked against the page images. -/
def gapTests : List GapTest :=
  [⟨.a0, .unembedded, .gap, .yes⟩,
   ⟨.a1, .unembedded, .gap, .yes⟩,
   ⟨.b1, .unembedded, .gap, .yes⟩,
   ⟨.a2, .unembedded, .gap, .yes⟩,
   ⟨.b2, .unembedded, .gap, .yes⟩,
   ⟨.a3, .unembedded, .gap, .yes⟩,
   ⟨.b3, .unembedded, .gap, .yes⟩,
   ⟨.a1, .negation, .gap, .yes⟩,
   ⟨.b1, .negation, .gap, .yes⟩,
   ⟨.a2, .all, .gap, .yes⟩,
   ⟨.b2, .all, .gap, .yes⟩,
   ⟨.c2, .all, .gap, .yes⟩,
   ⟨.a3, .all, .gap, .yes⟩,
   ⟨.b3, .all, .gap, .yes⟩,
   ⟨.c3, .all, .gap, .yes⟩,
   ⟨.c4, .all, .gap, .yes⟩,
   ⟨.a2, .no, .gap, .no⟩,  -- the ungrammatical E-no sentences of fn 10
   ⟨.b2, .no, .gap, .no⟩,  -- the ungrammatical E-no sentences of fn 10
   ⟨.c2, .no, .gap, .yes⟩,
   ⟨.a3, .exactly, .gap, .yes⟩,
   ⟨.b3, .exactly, .gap, .yes⟩,
   ⟨.c3, .exactly, .gap, .yes⟩,
   ⟨.c4, .exactly, .gap, .yes⟩,
   ⟨.a3, .exactly, .gapQ, .no⟩,
   ⟨.b3, .exactly, .gapQ, .no⟩,
   ⟨.c3, .exactly, .gapQ, .no⟩,
   ⟨.c4, .exactly, .gapQQ, .yes⟩]

/-- A row of Table 13: the target displays of each environment and condition, a display giving
for each cell how many of its nine symbols have the target color. E-neg used the E-∅ displays
and E-every (Experiment C2) the E-all ones. -/
structure Item where
  /-- The environment. -/
  embedding : Embedding
  /-- The condition. -/
  condition : Condition
  /-- The target-color count of each cell. -/
  cells : List ℕ
  /-- How the item is marked. -/
  status : ItemStatus
  deriving DecidableEq, Repr

/-- The 65 rows of Table 13, in the paper's order; checked against the page images. -/
def items : List Item :=
  [⟨.unembedded, .clearlyFalse, [0], .used⟩,
   ⟨.unembedded, .gap, [8], .used⟩,
   ⟨.unembedded, .gap, [6], .used⟩,
   ⟨.unembedded, .gap, [4], .used⟩,
   ⟨.unembedded, .gap, [2], .used⟩,
   ⟨.unembedded, .clearlyTrue, [9], .used⟩,
   ⟨.all, .clearlyFalse, [0, 9, 9, 0], .used⟩,
   ⟨.all, .clearlyFalse, [9, 7, 7, 0], .used⟩,
   ⟨.all, .clearlyFalse, [9, 0, 7, 9], .used⟩,
   ⟨.all, .clearlyFalse, [9, 4, 4, 0], .used⟩,
   ⟨.all, .clearlyFalse, [4, 0, 4, 4], .used⟩,
   ⟨.all, .clearlyFalse, [4, 9, 9, 0], .used⟩,
   ⟨.all, .gap, [9, 9, 2, 9], .used⟩,
   ⟨.all, .gap, [9, 9, 3, 9], .used⟩,
   ⟨.all, .gap, [9, 4, 9, 9], .used⟩,
   ⟨.all, .gap, [9, 9, 6, 9], .used⟩,
   ⟨.all, .gap, [9, 7, 9, 9], .used⟩,
   ⟨.all, .gap, [9, 9, 9, 5], .used⟩,
   ⟨.all, .clearlyTrue, [9, 9, 9, 9], .used⟩,
   ⟨.no, .clearlyFalse, [9, 0, 0, 9], .used⟩,
   ⟨.no, .clearlyFalse, [5, 0, 0, 9], .used⟩,
   ⟨.no, .clearlyFalse, [0, 9, 2, 0], .used⟩,
   ⟨.no, .clearlyFalse, [0, 5, 5, 0], .faulty⟩,
   ⟨.no, .clearlyFalse, [5, 0, 5, 5], .faulty⟩,
   ⟨.no, .clearlyFalse, [0, 2, 2, 0], .faulty⟩,
   ⟨.no, .clearlyFalse, [5, 0, 0, 9], .replacement⟩,
   ⟨.no, .clearlyFalse, [5, 0, 0, 9], .replacement⟩,
   ⟨.no, .clearlyFalse, [9, 9, 0, 9], .replacement⟩,
   ⟨.no, .gap, [0, 0, 7, 0], .used⟩,
   ⟨.no, .gap, [0, 0, 6, 0], .used⟩,
   ⟨.no, .gap, [0, 0, 3, 0], .used⟩,
   ⟨.no, .gap, [0, 0, 6, 0], .used⟩,  -- printed a second time
   ⟨.no, .gap, [0, 5, 0, 0], .used⟩,
   ⟨.no, .gap, [0, 2, 0, 0], .used⟩,
   ⟨.no, .clearlyTrue, [0, 0, 0, 0], .used⟩,
   ⟨.exactly, .clearlyFalse, [0, 9, 0, 0], .used⟩,
   ⟨.exactly, .clearlyFalse, [9, 9, 9, 0], .used⟩,
   ⟨.exactly, .clearlyFalse, [0, 0, 0, 0], .used⟩,
   ⟨.exactly, .clearlyFalse, [4, 0, 0, 0], .used⟩,
   ⟨.exactly, .clearlyFalse, [9, 9, 9, 9], .used⟩,
   ⟨.exactly, .clearlyFalse, [9, 9, 9, 4], .used⟩,
   ⟨.exactly, .gap, [9, 2, 0, 0], .used⟩,
   ⟨.exactly, .gap, [0, 4, 9, 0], .used⟩,
   ⟨.exactly, .gap, [7, 0, 9, 0], .used⟩,
   ⟨.exactly, .gap, [3, 3, 0, 0], .used⟩,
   ⟨.exactly, .gap, [0, 5, 5, 0], .used⟩,
   ⟨.exactly, .gap, [0, 8, 0, 8], .used⟩,
   ⟨.exactly, .clearlyTrue, [9, 9, 0, 0], .used⟩,
   ⟨.exactly, .clearlyTrue, [9, 0, 9, 0], .used⟩,
   ⟨.exactly, .clearlyTrue, [9, 0, 0, 9], .used⟩,
   ⟨.exactly, .clearlyTrue, [0, 9, 0, 9], .used⟩,
   ⟨.exactly, .clearlyTrue, [0, 0, 9, 9], .used⟩,
   ⟨.exactly, .clearlyTrue, [0, 9, 9, 0], .used⟩,
   ⟨.exactly, .gapQ, [9, 2, 0, 2], .used⟩,
   ⟨.exactly, .gapQ, [3, 3, 9, 0], .used⟩,
   ⟨.exactly, .gapQ, [0, 4, 9, 4], .used⟩,
   ⟨.exactly,  -- two full cells, against §3.3.2's description of the GAP? items
     .gapQ,
     [5, 5, 9, 9],
     .used⟩,
   ⟨.exactly, .gapQ, [9, 6, 6, 0], .used⟩,
   ⟨.exactly, .gapQ, [7, 9, 0, 7], .used⟩,
   ⟨.exactly, .gapQQ, [9, 2, 0, 9], .used⟩,
   ⟨.exactly, .gapQQ, [3, 9, 9, 0], .used⟩,
   ⟨.exactly, .gapQQ, [0, 9, 9, 4], .used⟩,
   ⟨.exactly, .gapQQ, [9, 5, 9, 0], .used⟩,
   ⟨.exactly, .gapQQ, [9, 9, 6, 0], .used⟩,
   ⟨.exactly, .gapQQ, [7, 9, 0, 9], .used⟩]

/-- A row of §2.1.6, Tables 3–11: the three statistical diagnostics of a gap for each environment
and gap condition of an experiment, the coefficient, the χ² statistic and the p-value as
printed, as a decimal or as a power of ten. -/
structure Diagnostic where
  /-- The experiment. -/
  experiment : Experiment
  /-- The environment. -/
  embedding : Embedding
  /-- The gap condition. -/
  condition : Condition
  /-- The diagnostic, 1 to 3. -/
  diagnostic : ℕ
  /-- The coefficient β. -/
  beta : Decimal
  /-- The χ² statistic. -/
  chiSq : Decimal
  /-- The p-value, printed as a decimal or as a power of ten. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 81 rows of §2.1.6, Tables 3–11, in the paper's order; checked against the page images. -/
def diagnostics : List Diagnostic :=
  [⟨.a0, .unembedded, .gap, 1, ⟨56, 1⟩, ⟨347, 0⟩, ⟨.lt, ⟨1, 15⟩⟩⟩,
   ⟨.a0, .unembedded, .gap, 2, ⟨63, 1⟩, ⟨623, 0⟩, ⟨.lt, ⟨1, 15⟩⟩⟩,
   ⟨.a0, .unembedded, .gap, 3, ⟨525, 2⟩, ⟨615, 2⟩, ⟨.eq, ⟨13, 3⟩⟩⟩,
   ⟨.a1, .unembedded, .gap, 1, ⟨-78, 1⟩, ⟨132, 1⟩, ⟨.eq, ⟨3, 4⟩⟩⟩,
   ⟨.a1, .unembedded, .gap, 2, ⟨-51, 1⟩, ⟨979, 2⟩, ⟨.eq, ⟨2, 3⟩⟩⟩,
   ⟨.a1, .unembedded, .gap, 3, ⟨-35, 0⟩, ⟨126, 1⟩, ⟨.eq, ⟨4, 4⟩⟩⟩,
   ⟨.a1, .negation, .gap, 1, ⟨-38, 1⟩, ⟨980, 2⟩, ⟨.eq, ⟨2, 3⟩⟩⟩,
   ⟨.a1, .negation, .gap, 2, ⟨-44, 1⟩, ⟨198, 1⟩, ⟨.eq, ⟨1, 5⟩⟩⟩,
   ⟨.a1, .negation, .gap, 3, ⟨-49, 1⟩, ⟨117, 1⟩, ⟨.eq, ⟨7, 4⟩⟩⟩,
   ⟨.a2, .unembedded, .gap, 1, ⟨-49, 1⟩, ⟨289, 1⟩, ⟨.eq, ⟨1, 7⟩⟩⟩,
   ⟨.a2, .unembedded, .gap, 2, ⟨-46, 1⟩, ⟨627, 2⟩, ⟨.eq, ⟨12, 3⟩⟩⟩,
   ⟨.a2, .unembedded, .gap, 3, ⟨-39, 1⟩, ⟨572, 2⟩, ⟨.eq, ⟨17, 3⟩⟩⟩,
   ⟨.a2, .all, .gap, 1, ⟨-38, 1⟩, ⟨697, 2⟩, ⟨.eq, ⟨8, 3⟩⟩⟩,
   ⟨.a2, .all, .gap, 2, ⟨-35, 1⟩, ⟨110, 1⟩, ⟨.eq, ⟨9, 4⟩⟩⟩,
   ⟨.a2, .all, .gap, 3, ⟨-37, 1⟩, ⟨711, 2⟩, ⟨.eq, ⟨8, 3⟩⟩⟩,
   ⟨.a2, .no, .gap, 1, ⟨-16, 2⟩, ⟨74, 3⟩, ⟨.eq, ⟨79, 2⟩⟩⟩,
   ⟨.a2, .no, .gap, 2, ⟨-14, 1⟩, ⟨217, 2⟩, ⟨.eq, ⟨14, 2⟩⟩⟩,
   ⟨.a2, .no, .gap, 3, ⟨-69, 2⟩, ⟨85, 2⟩, ⟨.eq, ⟨36, 2⟩⟩⟩,
   ⟨.a3, .unembedded, .gap, 1, ⟨-45, 1⟩, ⟨247, 1⟩, ⟨.eq, ⟨1, 6⟩⟩⟩,
   ⟨.a3, .unembedded, .gap, 2, ⟨-36, 1⟩, ⟨111, 1⟩, ⟨.eq, ⟨9, 4⟩⟩⟩,
   ⟨.a3, .unembedded, .gap, 3, ⟨-39, 1⟩, ⟨103, 1⟩, ⟨.eq, ⟨1, 3⟩⟩⟩,
   ⟨.a3, .all, .gap, 1, ⟨-25, 1⟩, ⟨105, 1⟩, ⟨.eq, ⟨1, 3⟩⟩⟩,
   ⟨.a3, .all, .gap, 2, ⟨-114, 2⟩, ⟨457, 2⟩, ⟨.eq, ⟨3, 2⟩⟩⟩,
   ⟨.a3, .all, .gap, 3, ⟨-15, 1⟩, ⟨391, 2⟩, ⟨.eq, ⟨48, 3⟩⟩⟩,
   ⟨.a3, .exactly, .gap, 1, ⟨-91, 1⟩, ⟨107, 1⟩, ⟨.eq, ⟨1, 3⟩⟩⟩,
   ⟨.a3, .exactly, .gap, 2, ⟨-64, 1⟩, ⟨127, 1⟩, ⟨.eq, ⟨4, 4⟩⟩⟩,
   ⟨.a3, .exactly, .gap, 3, ⟨-47, 1⟩, ⟨545, 2⟩, ⟨.eq, ⟨20, 3⟩⟩⟩,
   ⟨.a3, .exactly, .gapQ, 1, ⟨-34, 1⟩, ⟨527, 2⟩, ⟨.eq, ⟨2, 2⟩⟩⟩,
   ⟨.a3, .exactly, .gapQ, 2, ⟨-12, 1⟩, ⟨25, 1⟩, ⟨.eq, ⟨11, 2⟩⟩⟩,
   ⟨.a3, .exactly, .gapQ, 3, ⟨-46, 2⟩, ⟨48, 2⟩, ⟨.eq, ⟨49, 2⟩⟩⟩,
   ⟨.b1, .unembedded, .gap, 1, ⟨75, 1⟩, ⟨726, 1⟩, ⟨.eq, ⟨1, 16⟩⟩⟩,
   ⟨.b1, .unembedded, .gap, 2, ⟨72, 1⟩, ⟨122, 0⟩, ⟨.eq, ⟨1, 27⟩⟩⟩,
   ⟨.b1, .unembedded, .gap, 3, ⟨29, 1⟩, ⟨24, 0⟩, ⟨.eq, ⟨1, 6⟩⟩⟩,
   ⟨.b1, .negation, .gap, 1, ⟨21, 0⟩, ⟨641, 1⟩, ⟨.eq, ⟨1, 15⟩⟩⟩,
   ⟨.b1, .negation, .gap, 2, ⟨64, 1⟩, ⟨96, 0⟩, ⟨.eq, ⟨1, 22⟩⟩⟩,
   ⟨.b1, .negation, .gap, 3, ⟨28, 0⟩, ⟨123, 0⟩, ⟨.eq, ⟨1, 28⟩⟩⟩,
   ⟨.b2, .unembedded, .gap, 1, ⟨52, 1⟩, ⟨152, 1⟩, ⟨.eq, ⟨1, 4⟩⟩⟩,
   ⟨.b2, .unembedded, .gap, 2, ⟨85, 1⟩, ⟨258, 1⟩, ⟨.eq, ⟨1, 6⟩⟩⟩,
   ⟨.b2, .unembedded, .gap, 3, ⟨27, 1⟩, ⟨147, 1⟩, ⟨.eq, ⟨1, 4⟩⟩⟩,
   ⟨.b2, .all, .gap, 1, ⟨38, 1⟩, ⟨108, 1⟩, ⟨.eq, ⟨10, 4⟩⟩⟩,
   ⟨.b2, .all, .gap, 2, ⟨35, 1⟩, ⟨140, 1⟩, ⟨.eq, ⟨2, 4⟩⟩⟩,
   ⟨.b2, .all, .gap, 3, ⟨8, 1⟩, ⟨35, 1⟩, ⟨.eq, ⟨61, 3⟩⟩⟩,
   ⟨.b2, .no, .gap, 1, ⟨-68, 2⟩, ⟨108, 2⟩, ⟨.eq, ⟨30, 2⟩⟩⟩,
   ⟨.b2, .no, .gap, 2, ⟨14, 1⟩, ⟨177, 2⟩, ⟨.eq, ⟨18, 2⟩⟩⟩,
   ⟨.b2, .no, .gap, 3, ⟨18, 2⟩, ⟨31, 2⟩, ⟨.eq, ⟨58, 2⟩⟩⟩,
   ⟨.b3, .unembedded, .gap, 1, ⟨105, 1⟩, ⟨37, 0⟩, ⟨.eq, ⟨1, 9⟩⟩⟩,
   ⟨.b3, .unembedded, .gap, 2, ⟨54, 1⟩, ⟨285, 1⟩, ⟨.eq, ⟨1, 7⟩⟩⟩,
   ⟨.b3, .unembedded, .gap, 3, ⟨22, 1⟩, ⟨115, 1⟩, ⟨.eq, ⟨7, 4⟩⟩⟩,
   ⟨.b3, .all, .gap, 1, ⟨31, 1⟩, ⟨221, 1⟩, ⟨.eq, ⟨1, 5⟩⟩⟩,
   ⟨.b3, .all, .gap, 2, ⟨22, 1⟩, ⟨153, 1⟩, ⟨.eq, ⟨1, 4⟩⟩⟩,
   ⟨.b3, .all, .gap, 3, ⟨16, 1⟩, ⟨74, 1⟩, ⟨.eq, ⟨6, 3⟩⟩⟩,
   ⟨.b3, .exactly, .gap, 1, ⟨20, 1⟩, ⟨712, 2⟩, ⟨.eq, ⟨76, 4⟩⟩⟩,
   ⟨.b3, .exactly, .gap, 2, ⟨35, 1⟩, ⟨209, 1⟩, ⟨.eq, ⟨1, 5⟩⟩⟩,
   ⟨.b3, .exactly, .gap, 3, ⟨18, 1⟩, ⟨44, 1⟩, ⟨.eq, ⟨36, 3⟩⟩⟩,
   ⟨.b3, .exactly, .gapQ, 1, ⟨-17, 2⟩, ⟨65, 3⟩, ⟨.eq, ⟨80, 2⟩⟩⟩,
   ⟨.b3, .exactly, .gapQ, 2, ⟨17, 1⟩, ⟨574, 2⟩, ⟨.eq, ⟨17, 3⟩⟩⟩,
   ⟨.b3, .exactly, .gapQ, 3, ⟨99, 2⟩, ⟨18, 1⟩, ⟨.eq, ⟨18, 2⟩⟩⟩,
   ⟨.c2, .all, .gap, 1, ⟨67, 1⟩, ⟨267, 1⟩, ⟨.eq, ⟨1, 6⟩⟩⟩,  -- printed E-every
   ⟨.c2, .all, .gap, 2, ⟨77, 1⟩, ⟨351, 1⟩, ⟨.eq, ⟨1, 8⟩⟩⟩,  -- printed E-every
   ⟨.c2, .all, .gap, 3, ⟨49, 1⟩, ⟨40, 1⟩, ⟨.eq, ⟨46, 3⟩⟩⟩,  -- printed E-every
   ⟨.c2, .no, .gap, 1, ⟨13, 1⟩, ⟨82, 1⟩, ⟨.eq, ⟨4, 3⟩⟩⟩,
   ⟨.c2, .no, .gap, 2, ⟨11, 1⟩, ⟨52, 1⟩, ⟨.eq, ⟨22, 3⟩⟩⟩,
   ⟨.c2, .no, .gap, 3, ⟨16, 1⟩, ⟨78, 1⟩, ⟨.eq, ⟨5, 3⟩⟩⟩,
   ⟨.c3, .all, .gap, 1, ⟨19, 1⟩, ⟨188, 1⟩, ⟨.eq, ⟨1, 4⟩⟩⟩,
   ⟨.c3, .all, .gap, 2, ⟨16, 1⟩, ⟨164, 1⟩, ⟨.eq, ⟨1, 4⟩⟩⟩,
   ⟨.c3, .all, .gap, 3, ⟨15, 1⟩, ⟨97, 1⟩, ⟨.eq, ⟨2, 3⟩⟩⟩,
   ⟨.c3, .exactly, .gap, 1, ⟨39, 1⟩, ⟨210, 1⟩, ⟨.eq, ⟨1, 5⟩⟩⟩,
   ⟨.c3, .exactly, .gap, 2, ⟨77, 1⟩, ⟨388, 1⟩, ⟨.eq, ⟨1, 9⟩⟩⟩,
   ⟨.c3, .exactly, .gap, 3, ⟨66, 1⟩, ⟨135, 1⟩, ⟨.eq, ⟨2, 4⟩⟩⟩,
   ⟨.c3, .exactly, .gapQ, 1, ⟨-45, 2⟩, ⟨14, 1⟩, ⟨.eq, ⟨23, 2⟩⟩⟩,
   ⟨.c3, .exactly, .gapQ, 2, ⟨68, 2⟩, ⟨20, 1⟩, ⟨.eq, ⟨15, 2⟩⟩⟩,
   ⟨.c3, .exactly, .gapQ, 3, ⟨-1, 2⟩, ⟨2, 2⟩, ⟨.eq, ⟨88, 2⟩⟩⟩,
   ⟨.c4, .all, .gap, 1, ⟨22, 1⟩, ⟨175, 1⟩, ⟨.eq, ⟨1, 6⟩⟩⟩,
   ⟨.c4, .all, .gap, 2, ⟨14, 1⟩, ⟨99, 1⟩, ⟨.eq, ⟨2, 3⟩⟩⟩,
   ⟨.c4, .all, .gap, 3, ⟨15, 1⟩, ⟨76, 1⟩, ⟨.eq, ⟨6, 3⟩⟩⟩,
   ⟨.c4, .exactly, .gap, 1, ⟨82, 1⟩, ⟨167, 1⟩, ⟨.eq, ⟨1, 4⟩⟩⟩,
   ⟨.c4, .exactly, .gap, 2, ⟨67, 1⟩, ⟨362, 1⟩, ⟨.eq, ⟨1, 8⟩⟩⟩,
   ⟨.c4, .exactly, .gap, 3, ⟨57, 1⟩, ⟨68, 1⟩, ⟨.eq, ⟨9, 3⟩⟩⟩,
   ⟨.c4, .exactly, .gapQQ, 1, ⟨44, 1⟩, ⟨134, 1⟩, ⟨.eq, ⟨2, 4⟩⟩⟩,
   ⟨.c4, .exactly, .gapQQ, 2, ⟨76, 1⟩, ⟨494, 1⟩, ⟨.eq, ⟨1, 11⟩⟩⟩,
   ⟨.c4, .exactly, .gapQQ, 3, ⟨70, 1⟩, ⟨115, 1⟩, ⟨.eq, ⟨7, 4⟩⟩⟩]

/-- A row of Table 12: the situations of the theoretical comparison for 'Exactly 2 teachers like
their students', how many of their students Bill, Mary and Sue like, the condition each
corresponds to and whether a gap was found there. The truth values of the parses and the
construals' predictions it also prints are derived in the study. -/
structure Situation where
  /-- Bill's share. -/
  bill : Share
  /-- Mary's share. -/
  mary : Share
  /-- Sue's share. -/
  sue : Share
  /-- The corresponding condition. -/
  condition : Condition
  /-- Whether a gap was found. -/
  found : Found
  deriving DecidableEq, Repr

/-- The 6 rows of Table 12, in the paper's order; checked against the page images. -/
def situations : List Situation :=
  [⟨.all, .all, .none, .clearlyTrue, .no⟩,  -- s1
   ⟨.all, .all, .all, .clearlyFalse, .no⟩,  -- s2
   ⟨.all, .none, .none, .clearlyFalse, .no⟩,  -- s3
   ⟨.all, .half, .none, .gap, .yes⟩,  -- s4
   ⟨.all, .half, .half, .gapQ, .no⟩,  -- s5
   ⟨.all, .all, .half, .gapQQ, .yes⟩]  -- s6

end KrizChemla2015
