module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Syntax.CCG.Interface
public import Linglib.Data.Examples.PickeringBarry1991
public import Linglib.Data.Examples.Readers

/-!
# Pickering and Barry (1991): Sentence Processing without Empty Categories

[pickering-barry-1991] argue that the processor associates the filler of an unbounded dependency
directly with its subcategoriser, never with an empty category. A pattern of associations is
disjoint ($aabb$) or nested ($abba$), and a nested one holds an element in memory while another
association forms. Without empty categories [the filler–verb pattern is nested exactly in the
nested constructions of [chomsky-1965]](##table2) and [in the sentences hard to
process](##difficulty), while [empty categories nest multiple pied piping to any
depth](##peripheralGaps_isNested). In the paper's categorial grammar [each wh-word abstracts over
the argument its verb assigns](##embedded_questions), and [(82d) has no derivation](##no_der82d).

## Implementation notes

Positions are those of the words of the paper's annotated strings, empty categories included,
with a bracketed filler such as *[on which]* one word (the paper's footnote 3). The gap-free
analysis reads its filler and subcategoriser off the same positions, since a pattern depends only
on their order. The paper prints only the gap-free analysis (61) of (60); its empty categories
follow each stranded preposition, as the paper places the one of (13). A relative clause spans
its empty categories, so the word *nonnull* in Chomsky's definition does work on the
empty-category analysis.

The grammar is the paper's: application (76) and forward composition (80b). Its rule (80a),
which combines a subject with a transitive verb before the object, is forward type raising of
the subject composed with the verb, so the lexicon carries the raised subject, as in
`Syntax/CCG/Derivation`. An embedded question denotes the property its wh-word abstracts, and a
prepositional phrase the individual its preposition takes; the paper leaves both meanings open.

## References

* [pickering-barry-1991]
* [chomsky-1965]
* [van-benthem-1986]
-/

@[expose] public section

namespace PickeringBarry1991

open Examples
open scoped CCG

/-! ### Associations and their patterns -/

/-- A dependency of an annotated sentence records the positions of its filler, of the empty
category the empty-category analysis posits, and of its subcategoriser. -/
structure Dependency where
  /-- The position of the filler. -/
  filler : ℕ
  /-- The position of the empty category. -/
  gap : ℕ
  /-- The position of the subcategoriser. -/
  verb : ℕ
  deriving DecidableEq, Repr

/-- The span between two positions. -/
def span (i j : ℕ) : NonemptyInterval ℕ := ⟨(min i j, max i j), min_le_max⟩

@[simp] theorem span_fst (i j : ℕ) : (span i j).fst = min i j := rfl

@[simp] theorem span_snd (i j : ℕ) : (span i j).snd = max i j := rfl

namespace Dependency

/-- The filler–gap association of the empty-category analysis. -/
def fillerGap (d : Dependency) : NonemptyInterval ℕ := span d.filler d.gap

/-- The gap–verb association of the empty-category analysis. -/
def gapVerb (d : Dependency) : NonemptyInterval ℕ := span d.gap d.verb

/-- The filler–verb association of the gap-free analysis. -/
def fillerVerb (d : Dependency) : NonemptyInterval ℕ := span d.filler d.verb

end Dependency

/-- A pattern of associations is disjoint, $aabb$, $aabbcc$, …, when no two associations
overlap. -/
def IsDisjoint (L : List (NonemptyInterval ℕ)) : Prop := L.Pairwise fun a b ↦ ¬ a.Overlaps b

/-- A pattern of associations is nested, $abba$, $abccba$, …, when of any two associations one
lies strictly inside the other. -/
def IsNested (L : List (NonemptyInterval ℕ)) : Prop :=
  L.Pairwise fun a b ↦ a.During b ∨ b.During a

instance (L : List (NonemptyInterval ℕ)) : Decidable (IsDisjoint L) :=
  inferInstanceAs (Decidable (L.Pairwise _))

instance (L : List (NonemptyInterval ℕ)) : Decidable (IsNested L) :=
  inferInstanceAs (Decidable (L.Pairwise _))

/-! ### Nested constructions -/

/-- The nested construction of [chomsky-1965], as the paper quotes it: the phrase `A` falls
totally within `B`, with some nonnull element to its left within `B` and some nonnull element to
its right within `B`. The positions in `null` hold empty categories. -/
def NestedIn (null : List ℕ) (A B : NonemptyInterval ℕ) : Prop :=
  A ≤ B ∧ (∃ k < A.fst, B.fst ≤ k ∧ k ∉ null) ∧ ∃ k ≤ B.snd, A.snd < k ∧ k ∉ null

instance (null : List ℕ) (A B : NonemptyInterval ℕ) : Decidable (NestedIn null A B) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- Where no element is null, a phrase is nested in another when it lies strictly inside it: the
-- paper's simplification of Chomsky's definition by removing the word *nonnull*.
theorem nestedIn_nil_iff {A B : NonemptyInterval ℕ} : NestedIn [] A B ↔ A.During B := by
  simp only [NestedIn, NonemptyInterval.le_def, NonemptyInterval.During, List.not_mem_nil,
    not_false_eq_true, and_true]
  constructor
  · rintro ⟨-, ⟨k, hk, hBk⟩, k', hk', hAk'⟩
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁.le, h₂.le⟩, ⟨B.fst, h₁, le_rfl⟩, B.snd, le_rfl, h₂⟩

/-- An annotated sentence records its dependencies and the spans of its relative clauses. -/
structure Analysis where
  /-- The dependencies. -/
  deps : List Dependency
  /-- The spans of the relative clauses, their empty categories included. -/
  clauses : List (NonemptyInterval ℕ)

namespace Analysis

/-- The filler–gap associations. -/
def fillerGap (A : Analysis) : List (NonemptyInterval ℕ) := A.deps.map Dependency.fillerGap

/-- The gap–verb associations. -/
def gapVerb (A : Analysis) : List (NonemptyInterval ℕ) := A.deps.map Dependency.gapVerb

/-- The filler–verb associations. -/
def fillerVerb (A : Analysis) : List (NonemptyInterval ℕ) := A.deps.map Dependency.fillerVerb

/-- A sentence is a nested construction when one of its relative clauses is nested in another,
the empty categories of the analysis being its null elements. -/
def IsNestedConstruction (A : Analysis) : Prop :=
  ∃ a ∈ A.clauses, ∃ b ∈ A.clauses, NestedIn (A.deps.map (·.gap)) a b

instance (A : Analysis) : Decidable A.IsNestedConstruction :=
  inferInstanceAs (Decidable (∃ _ ∈ A.clauses, _))

end Analysis

/-! ### The constructions -/

/-- The multiple subject relative with `n` clauses, (44), (51), annotated as (46): *I saw the
farmer [who]ₐ Øₐ [owned]ₐ the dog [which]_b Ø_b [chased]_b the cat …*, each clause placing a
filler, its empty category and its verb in succession. -/
def localGaps (n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦ ⟨4 + 5 * k, 5 + 5 * k, 6 + 5 * k⟩

/-- The multiple object relative with `n` clauses, (45), (52), annotated as (47): *The cat
[which]ₐ the dog [which]_b the farmer [owned]_b Ø_b [chased]ₐ Øₐ fled …*, the fillers in
succession and then the verbs in reverse order, each followed by its empty category. -/
def centreEmbedded (n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦
    ⟨2 + 3 * k, 2 + 3 * n + 2 * (n - 1 - k) + 1, 2 + 3 * n + 2 * (n - 1 - k)⟩

/-- The German multiple subject relative with `n` clauses, (48), (53), annotated as (49): *Der
Bauer [der]ₐ Øₐ das Mädchen [das]_b Ø_b den Jungen [küßte]_b [schlug]ₐ ging …*, each filler
followed by its empty category and the verbs at the end in reverse order. -/
def verbFinal (n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦ ⟨2 + 4 * k, 3 + 4 * k, 2 + 4 * n + (n - 1 - k)⟩

/-- The `n` clauses from position `a` that each place a filler and two words later its verb,
while the empty-category analysis sites every empty category at the end of the sentence in
reverse order: multiple pied piping (42), (54), (55), annotated as (50), *John found the saucer
[on which]ₐ Mary [put]ₐ the cup [into which]_b I [poured]_b the tea Ø_b Øₐ*; the recursive
passive (93), annotated as (94), from `0`; and the double-object relatives of (62). -/
def peripheralGaps (a n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦ ⟨a + 5 * k, a + 5 * n + (n - 1 - k), a + 5 * k + 2⟩

/-- Multiple preposition stranding (60), annotated as (61): *John found the saucer [which]ₐ Mary
put the cup [which]_b I poured the tea [into]_b Ø_b [on]ₐ Øₐ*. -/
def stranding : List Dependency := [⟨4, 17, 16⟩, ⟨9, 15, 14⟩]

/-! ### The four sentence types (Tables 1 and 2) -/

/-- The multiple subject relative (44), with relative clauses *who … the cat* and *which chased
the cat*. -/
def subjectRelative : Analysis := ⟨localGaps 2, [span 4 13, span 9 13]⟩

/-- The multiple object relative (45), with relative clauses *which … chased Øₐ* and *which the
farmer owned Ø_b*. -/
def objectRelative : Analysis := ⟨centreEmbedded 2, [span 2 11, span 5 9]⟩

/-- The German multiple subject relative (48), with relative clauses *der … schlug* and *das Ø_b
den Jungen küßte*. -/
def germanSubjectRelative : Analysis := ⟨verbFinal 2, [span 2 11, span 6 10]⟩

/-- Multiple pied piping (42), with relative clauses *on which … the tea Ø_b Øₐ* and *into which
I poured the tea Ø_b*. -/
def multiplePiedPiping : Analysis := ⟨peripheralGaps 4 2, [span 4 15, span 9 14]⟩

/-- The four sentence types of Tables 1 and 2. -/
def sentenceTypes : List Analysis :=
  [subjectRelative, objectRelative, germanSubjectRelative, multiplePiedPiping]

-- Table 1: the filler–gap and gap–verb patterns and the construction type of each sentence type
theorem table1 :
    (IsDisjoint subjectRelative.fillerGap ∧ IsDisjoint subjectRelative.gapVerb ∧
      ¬ subjectRelative.IsNestedConstruction) ∧
    (IsNested objectRelative.fillerGap ∧ IsDisjoint objectRelative.gapVerb ∧
      objectRelative.IsNestedConstruction) ∧
    (IsDisjoint germanSubjectRelative.fillerGap ∧ IsNested germanSubjectRelative.gapVerb ∧
      germanSubjectRelative.IsNestedConstruction) ∧
    (IsNested multiplePiedPiping.fillerGap ∧ IsNested multiplePiedPiping.gapVerb ∧
      ¬ multiplePiedPiping.IsNestedConstruction) := by
  decide

/-- Without empty categories, the filler–verb pattern of each sentence type is nested if the
sentence is a nested construction and disjoint if it is not (Table 2). -/
theorem table2 : ∀ A ∈ sentenceTypes,
    (A.IsNestedConstruction → IsNested A.fillerVerb) ∧
      (¬ A.IsNestedConstruction → IsDisjoint A.fillerVerb) := by
  decide

-- Without the word *nonnull*, the empty category that ends the outer clause of (50) would make
-- multiple pied piping a nested construction.
theorem nonnull_needed :
    ∃ a ∈ multiplePiedPiping.clauses, ∃ b ∈ multiplePiedPiping.clauses, NestedIn [] a b := by
  decide

/-! ### Processing difficulty -/

/-- The paper reports the sentence hard to process. Its examples are grammatical and printed
unmarked, so difficulty is a separate observation from the judgment. -/
def Hard (e : Datum) : Prop := e.feature? "difficulty" = some "hard"

instance : DecidablePred Hard := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The sentences of the paper's argument from recursive constructions, with their
dependencies. -/
def rows : List (Datum × List Dependency) :=
  [(ex42, peripheralGaps 4 2), (ex44, localGaps 2), (ex45, centreEmbedded 2), (ex48, verbFinal 2),
   (ex51, localGaps 3), (ex52, centreEmbedded 3), (ex53, verbFinal 3), (ex54, peripheralGaps 4 3),
   (ex55, peripheralGaps 4 5), (ex60, stranding), (ex62, peripheralGaps 4 2),
   (ex93, peripheralGaps 0 2)]

/-- A sentence the paper reports is hard to process exactly when its filler–verb pattern is
nested. -/
theorem difficulty : ∀ p ∈ rows, Hard p.1 ↔ IsNested (p.2.map Dependency.fillerVerb) := by
  decide

-- The empty-category analysis, which predicts a sentence hard when either of its patterns is
-- nested, errs on exactly the multiple pied piping of (42), (54) and (55), the double-object
-- relatives of (62) and the recursive passive of (93).
theorem trace_prediction_fails :
    (rows.filter fun p ↦ ¬ (Hard p.1 ↔ IsNested (p.2.map Dependency.fillerGap) ∨
      IsNested (p.2.map Dependency.gapVerb))).map (·.1.source.paperLabel) =
        ["(42)", "(54)", "(55)", "(62)", "(93)"] := by
  decide

/-- (15) as annotated by the empty-category analysis: *[In which box]ₐ did you [put]ₐ*, the
complex noun phrase from position `4` to `16`, and *Øₐ* after it. -/
def piedPiped15 : Dependency := ⟨0, 17, 3⟩

/-- (16) as annotated by the empty-category analysis: *[Which box]ₐ did you put*, the complex
noun phrase from position `4` to `16`, and the stranded *[in]ₐ Øₐ*. -/
def stranded16 : Dependency := ⟨0, 18, 17⟩

/-- The complex noun phrase *the very large … expensive bakery* of (15) and (16). -/
def complexNP : NonemptyInterval ℕ := span 4 16

-- (15), (16): of the two, the gap-free analysis holds only the filler of the awkward (16) across
-- the complex noun phrase, and the empty-category analysis holds both.
theorem heavy_np :
    (¬ Hard ex15 ∧ Hard ex16) ∧
      (piedPiped15.fillerVerb.Precedes complexNP ∧ complexNP ≤ stranded16.fillerVerb) ∧
      complexNP ≤ piedPiped15.fillerGap ∧ complexNP ≤ stranded16.fillerGap := by
  decide

/-! ### Extending the constructions -/

/-- However many clauses multiple pied piping or the recursive passive has, the empty-category
analysis nests both of its patterns to that depth, while the filler–verb pattern stays
disjoint. -/
theorem peripheralGaps_isNested (a n : ℕ) :
    IsNested ((peripheralGaps a n).map Dependency.fillerGap) ∧
      IsNested ((peripheralGaps a n).map Dependency.gapVerb) ∧
      IsDisjoint ((peripheralGaps a n).map Dependency.fillerVerb) := by
  simp only [IsNested, IsDisjoint, peripheralGaps, List.map_map, List.pairwise_map]
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine List.pairwise_lt_range.imp_of_mem fun hi hj hij ↦ ?_
    simp only [List.mem_range] at hi hj
    simp only [Function.comp, Dependency.fillerGap, Dependency.gapVerb, Dependency.fillerVerb,
      NonemptyInterval.During, NonemptyInterval.Overlaps, span_fst, span_snd]
    omega

theorem localGaps_isDisjoint (n : ℕ) :
    IsDisjoint ((localGaps n).map Dependency.fillerGap) ∧
      IsDisjoint ((localGaps n).map Dependency.gapVerb) ∧
      IsDisjoint ((localGaps n).map Dependency.fillerVerb) := by
  simp only [IsDisjoint, localGaps, List.map_map, List.pairwise_map]
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine List.pairwise_lt_range.imp_of_mem fun hi hj hij ↦ ?_
    simp only [Function.comp, Dependency.fillerGap, Dependency.gapVerb, Dependency.fillerVerb,
      NonemptyInterval.Overlaps, span_fst, span_snd]
    omega

theorem centreEmbedded_isNested (n : ℕ) :
    IsNested ((centreEmbedded n).map Dependency.fillerGap) ∧
      IsDisjoint ((centreEmbedded n).map Dependency.gapVerb) ∧
      IsNested ((centreEmbedded n).map Dependency.fillerVerb) := by
  simp only [IsNested, IsDisjoint, centreEmbedded, List.map_map, List.pairwise_map]
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine List.pairwise_lt_range.imp_of_mem fun hi hj hij ↦ ?_
    simp only [List.mem_range] at hi hj
    simp only [Function.comp, Dependency.fillerGap, Dependency.gapVerb, Dependency.fillerVerb,
      NonemptyInterval.During, NonemptyInterval.Overlaps, span_fst, span_snd]
    omega

theorem verbFinal_isNested (n : ℕ) :
    IsDisjoint ((verbFinal n).map Dependency.fillerGap) ∧
      IsNested ((verbFinal n).map Dependency.gapVerb) ∧
      IsNested ((verbFinal n).map Dependency.fillerVerb) := by
  simp only [IsNested, IsDisjoint, verbFinal, List.map_map, List.pairwise_map]
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine List.pairwise_lt_range.imp_of_mem fun hi hj hij ↦ ?_
    simp only [List.mem_range] at hi hj
    simp only [Function.comp, Dependency.fillerGap, Dependency.gapVerb, Dependency.fillerVerb,
      NonemptyInterval.During, NonemptyInterval.Overlaps, span_fst, span_snd]
    omega

/-! ### Unbounded dependencies in categorial grammar -/

/-- The basic categories of the fragment are declarative sentence, embedded question, noun
phrase and prepositional phrase. -/
inductive Basic where
  | S
  | Q
  | NP
  | PP
  deriving DecidableEq, Repr

/-- The sentence category. -/
def sent : CCG.Cat Basic := .atom .S

/-- The embedded-question category. -/
def quest : CCG.Cat Basic := .atom .Q

/-- The noun-phrase category. -/
def np : CCG.Cat Basic := .atom .NP

/-- The prepositional-phrase category. -/
def pp : CCG.Cat Basic := .atom .PP

/-- The rules of the paper's flexible categorial grammar: application in either direction (76)
and forward composition (80b). -/
def flexible : CCG.RuleSystem Basic := fun _ a β ↦
  β = [] ∨ a.side = .right ∧ β.length = 1 ∧ ∀ b ∈ β, b.side = .right

instance (x : CCG.Cat Basic) (a : CCG.Cat.Arg Basic) (β : List (CCG.Cat.Arg Basic)) :
    Decidable (flexible x a β) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The lexicon of (79)–(85). The subject pronoun *who* takes a sentence missing its subject,
the object pronoun *whom* a sentence missing an object, and *John* carries the raised category
through which rule (80a) combines it with a verb before the verb's object. -/
def lexicon : List (String × CCG.Cat Basic) :=
  [("Sue", np), ("John", np), ("John", sent / (sent \ np)), ("Mary", np),
   ("saw", (sent \ np) / np), ("talked", (sent \ np) / pp), ("to", pp / np),
   ("wonders", (sent \ np) / quest), ("who", quest / (sent \ np)), ("whom", quest / (sent / np))]

/-- The derivation (79) of *John saw Mary*, the verb taking its object first. -/
def der79 : CCG.Derivation String flexible sent :=
  .bapp (.lex "John" np) (.fapp (.lex "saw" ((sent \ np) / np)) (.lex "Mary" np))

/-- The derivation (81) of *John saw Mary*, the subject combining with the verb first by rule
(80a). -/
def der81 : CCG.Derivation String flexible sent :=
  .fapp (.fcomp (.lex "John" (sent / (sent \ np))) (.lex "saw" ((sent \ np) / np)))
    (.lex "Mary" np)

/-- The derivation (83) of *who saw Mary*, in which the subject pronoun applies to a sentence
missing its subject. -/
def der83 : CCG.Derivation String flexible quest :=
  .fapp (.lex "who" (quest / (sent \ np))) (.fapp (.lex "saw" ((sent \ np) / np)) (.lex "Mary" np))

/-- The derivation (84) of *whom John saw*, in which the subject combines with the verb into a
sentence missing its object, which the object pronoun takes. -/
def der84 : CCG.Derivation String flexible quest :=
  .fapp (.lex "whom" (quest / (sent / np)))
    (.fcomp (.lex "John" (sent / (sent \ np))) (.lex "saw" ((sent \ np) / np)))

/-- The derivation (85) of *whom John talked to*, in which *talked to* composes into a
transitive verb, (80b), and the subject combines with it into a sentence missing the
preposition's object. -/
def der85 : CCG.Derivation String flexible quest :=
  .fapp (.lex "whom" (quest / (sent / np)))
    (.fcomp (.lex "John" (sent / (sent \ np)))
      (.fcomp (.lex "talked" ((sent \ np) / pp)) (.lex "to" (pp / np))))

/-- *Sue wonders* applied to an embedded question. -/
def wonders (d : CCG.Derivation String flexible quest) : CCG.Derivation String flexible sent :=
  .bapp (.lex "Sue" np) (.fapp (.lex "wonders" ((sent \ np) / quest)) d)

/-- (82a). -/
def der82a : CCG.Derivation String flexible sent := wonders der83

/-- (82b). -/
def der82b : CCG.Derivation String flexible sent := wonders der84

/-- (82c). -/
def der82c : CCG.Derivation String flexible sent := wonders der85

/-- The semantic type of a basic category: a sentence denotes a truth value, a noun phrase and a
prepositional phrase an individual, and an embedded question the property its wh-word
abstracts. -/
def atomTy : Basic → Montague.Ty
  | .S => .t
  | .Q => .fn .e .t
  | .NP => .e
  | .PP => .e

/-- A model of the fragment: the individuals its names denote and the relations its verbs
denote, the subject first, as in the paper's `saw(x,y)`. -/
structure Model (E : Type) where
  /-- The denotation of *Sue*. -/
  sue : E
  /-- The denotation of *John*. -/
  john : E
  /-- The denotation of *Mary*. -/
  mary : E
  /-- `saw x y`: `x` saw `y`. -/
  saw : E → E → Prop
  /-- `talkedTo x y`: `x` talked to `y`. -/
  talkedTo : E → E → Prop
  /-- `wonders x q`: `x` wonders which individuals have the property `q`. -/
  wonders : E → (E → Prop) → Prop

/-- The meanings of the lexicon in a model. A verb takes its object first, as in the paper's
`λy λx [saw(x,y)]`, the raised subject is the lift of its individual, and *who*, *whom* and *to*
pass on what they take. -/
def Model.lex {E : Type} (M : Model E) : CCG.SemLexicon String atomTy E Unit := fun w c ↦
  match w, c with
  | "Sue", .atom .NP => some M.sue
  | "John", .atom .NP => some M.john
  | "Mary", .atom .NP => some M.mary
  | "John", .rslash (.atom .S) _ (.lslash (.atom .S) _ (.atom .NP)) => some fun P ↦ P M.john
  | "saw", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .NP) => some fun y x ↦ M.saw x y
  | "talked", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .PP) =>
      some fun y x ↦ M.talkedTo x y
  | "to", .rslash (.atom .PP) _ (.atom .NP) => some id
  | "wonders", .rslash (.lslash (.atom .S) _ (.atom .NP)) _ (.atom .Q) =>
      some fun q x ↦ M.wonders x q
  | "who", .rslash (.atom .Q) _ (.lslash (.atom .S) _ (.atom .NP)) => some id
  | "whom", .rslash (.atom .Q) _ (.rslash (.atom .S) _ (.atom .NP)) => some id
  | _, _ => none

variable {E : Type} (M : Model E)

-- (79), (81): both derivations of *John saw Mary* mean `saw(John,Mary)`.
theorem der79_der81 :
    (der79.LexIn lexicon ∧ der81.LexIn lexicon ∧ der79.yield = der81.yield) ∧
      der79.interp M.lex = some (M.saw M.john M.mary) ∧
      der81.interp M.lex = some (M.saw M.john M.mary) :=
  ⟨by decide, rfl, rfl⟩

/-- Each wh-word of (82a–c) fills the argument role that its embedded verb or preposition
assigns, with no empty category: *who* abstracts over the subject of *saw*, *whom* over its
object and over the object of *to*. -/
theorem embedded_questions :
    (der82a.LexIn lexicon ∧ der82a.yield = ["Sue", "wonders", "who", "saw", "Mary"] ∧
      der82a.interp M.lex = some (M.wonders M.sue fun x ↦ M.saw x M.mary)) ∧
    (der82b.LexIn lexicon ∧ der82b.yield = ["Sue", "wonders", "whom", "John", "saw"] ∧
      der82b.interp M.lex = some (M.wonders M.sue fun y ↦ M.saw M.john y)) ∧
    (der82c.LexIn lexicon ∧ der82c.yield = ["Sue", "wonders", "whom", "John", "talked", "to"] ∧
      der82c.interp M.lex = some (M.wonders M.sue fun y ↦ M.talkedTo M.john y)) :=
  ⟨⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩⟩

/-- The noun phrases each word of the fragment contributes to the count invariant. A verb
consumes its arguments and a pronoun supplies the one it fills. -/
def npCount : String → ℤ
  | "saw" => -2
  | "talked" | "to" | "wonders" => -1
  | _ => 1

/-- *Sue wonders who John saw Mary* (82d) has no derivation, with *who* or *whom*, in any rule
system: no wh-word takes a whole sentence, so the pronoun must fill an argument role of the
embedded verb. -/
theorem no_der82d (R : CCG.RuleSystem Basic) (w : String) (hw : w = "who" ∨ w = "whom") :
    ¬ ∃ d : CCG.Derivation String R sent,
      d.LexIn lexicon ∧ d.yield = ["Sue", "wonders", w, "John", "saw", "Mary"] := by
  rintro ⟨d, hd, hy⟩
  have h := d.count_eq_sum .NP (f := npCount) (by decide) hd
  rw [hy] at h
  rcases hw with rfl | rfl <;> exact absurd h (by decide)

end PickeringBarry1991
