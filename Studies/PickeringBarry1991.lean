module

public import Mathlib.Data.List.OfFn
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Syntax.CCG.Interface
public import Linglib.Semantics.Composition.FirstOrder
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

An annotated sentence is written as the paper writes it, a list of words, fillers,
subcategorisers and empty categories, with brackets around the phrases Chomsky's definition
compares. Positions and spans are computed from that list, which prints as the example's row of
the data. A bracketed filler such as *[on which]* is one word
(the paper's footnote 3). The gap-free analysis reads its filler and subcategoriser off the same
positions, since a pattern depends only on their order. The paper prints only the gap-free
analysis (61) of (60) and no analysis of (62); their empty categories follow each stranded
preposition, as the paper places the one of (13), and end the sentence, where the paper says an
empty-category account places them. A relative clause spans its empty categories, so the word
*nonnull* in Chomsky's definition does work on the empty-category analysis.

The grammar is the paper's: application (76) and forward composition (80b). Its rule (80a),
which combines a subject with a transitive verb before the object, is forward type raising of
the subject composed with the verb, so the lexicon carries the raised subject, as in
`Syntax/CCG/Derivation`. Logical forms are terms over a first-order signature of the names and
the two transitive verbs, with a higher-order constant for *wonders*, so the lexicon is the same
in every model of it. An embedded question denotes the property its wh-word abstracts, and a
prepositional phrase the individual its preposition takes; the paper omits both meanings.

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

namespace Dependency

/-- The filler–gap association of the empty-category analysis. -/
def fillerGap (d : Dependency) : NonemptyInterval ℕ :=
  NonemptyInterval.pure d.filler ⊔ NonemptyInterval.pure d.gap

/-- The gap–verb association of the empty-category analysis. -/
def gapVerb (d : Dependency) : NonemptyInterval ℕ :=
  NonemptyInterval.pure d.gap ⊔ NonemptyInterval.pure d.verb

/-- The filler–verb association of the gap-free analysis. -/
def fillerVerb (d : Dependency) : NonemptyInterval ℕ :=
  NonemptyInterval.pure d.filler ⊔ NonemptyInterval.pure d.verb

end Dependency

open Dependency (fillerGap gapVerb fillerVerb)

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
@[mk_iff]
structure NestedIn (null : List ℕ) (A B : NonemptyInterval ℕ) : Prop where
  /-- `A` falls totally within `B`. -/
  le : A ≤ B
  /-- Some nonnull element of `B` lies to the left of `A`. -/
  nonnull_left : ∃ k < A.fst, B.fst ≤ k ∧ k ∉ null
  /-- Some nonnull element of `B` lies to the right of `A`. -/
  nonnull_right : ∃ k ≤ B.snd, A.snd < k ∧ k ∉ null

instance (null : List ℕ) (A B : NonemptyInterval ℕ) : Decidable (NestedIn null A B) :=
  decidable_of_iff' _ (nestedIn_iff null A B)

-- Where no element is null, a phrase is nested in another when it lies strictly inside it: the
-- paper's simplification of Chomsky's definition by removing the word *nonnull*.
theorem nestedIn_nil_iff {A B : NonemptyInterval ℕ} : NestedIn [] A B ↔ A.During B := by
  simp only [nestedIn_iff, NonemptyInterval.le_def, NonemptyInterval.During, List.not_mem_nil,
    not_false_eq_true, and_true]
  constructor
  · rintro ⟨-, ⟨k, hk, hBk⟩, k', hk', hAk'⟩
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁.le, h₂.le⟩, ⟨B.fst, h₁, le_rfl⟩, B.snd, le_rfl, h₂⟩

/-! ### Annotated sentences -/

/-- A token of an annotated sentence: a word, the filler, subcategoriser or empty category of the
`i`th dependency, or a bracket opening or closing a phrase. -/
inductive Token where
  | word (form : String)
  | filler (i : ℕ) (form : String)
  | subcat (i : ℕ) (form : String)
  | gap (i : ℕ)
  | lbrack
  | rbrack
  deriving Repr

namespace Token

/-- The dependency whose filler the token is. -/
def filler? : Token → Option ℕ
  | filler i _ => some i
  | _ => none

/-- The dependency whose subcategoriser the token is. -/
def subcat? : Token → Option ℕ
  | subcat i _ => some i
  | _ => none

/-- The dependency whose empty category the token is. -/
def gap? : Token → Option ℕ
  | gap i => some i
  | _ => none

/-- The printed form of the token, none for an empty category or a bracket. -/
def form? : Token → Option String
  | word w | filler _ w | subcat _ w => some w
  | _ => none

end Token

/-- The words of an annotated sentence, empty categories included and brackets dropped. -/
def words : List Token → List Token
  | [] => []
  | .lbrack :: s | .rbrack :: s => words s
  | t :: s => t :: words s

/-- Words separated by spaces, as Haskell's `unwords`. -/
-- `String.intercalate " "`, spelled with list functions, which `decide` unfolds in a module.
def unwords (ws : List String) : String := (ws.intersperse " ").foldr (· ++ ·) ""

/-- The sentence as printed: the forms of its words, separated by spaces. -/
def text (s : List Token) : String := unwords ((words s).filterMap Token.form?)

/-- The position of the first word `t` of an annotated sentence with `f t = some i`. -/
def position (s : List Token) (f : Token → Option ℕ) (i : ℕ) : ℕ :=
  (words s).findIdx (f · == some i)

/-- The dependencies of an annotated sentence, in the order of their fillers. -/
def deps (s : List Token) : List Dependency :=
  ((words s).filterMap Token.filler?).map fun i ↦
    ⟨position s Token.filler? i, position s Token.gap? i, position s Token.subcat? i⟩

/-- An annotated sentence is well formed when each of its dependencies has exactly one filler,
one subcategoriser and one empty category. -/
@[mk_iff]
structure WellFormed (s : List Token) : Prop where
  /-- No two fillers belong to the same dependency. -/
  nodup_fillers : ((words s).filterMap Token.filler?).Nodup
  /-- The empty categories belong to the dependencies of the fillers, one each. -/
  gaps_perm : ((words s).filterMap Token.gap?).Perm ((words s).filterMap Token.filler?)
  /-- The subcategorisers belong to the dependencies of the fillers, one each. -/
  subcats_perm : ((words s).filterMap Token.subcat?).Perm ((words s).filterMap Token.filler?)

instance (s : List Token) : Decidable (WellFormed s) :=
  decidable_of_iff' _ (wellFormed_iff s)

/-- The spans of the bracketed phrases of an annotated sentence, innermost first. -/
def phrases (s : List Token) : List (NonemptyInterval ℕ) := go s 0 []
where
  /-- `go s k o` reads `s` after `k` words, with the phrases that start at `o` still open. -/
  go : List Token → ℕ → List ℕ → List (NonemptyInterval ℕ)
    | [], _, _ => []
    | .lbrack :: s, k, o => go s k (k :: o)
    | .rbrack :: s, k, i :: o =>
        (NonemptyInterval.pure i ⊔ NonemptyInterval.pure (k - 1)) :: go s k o
    | .rbrack :: s, k, [] => go s k []
    | _ :: s, k, o => go s (k + 1) o

/-- A sentence is a nested construction when one of its bracketed phrases is nested in another,
its empty categories being its null elements. -/
def IsNestedConstruction (s : List Token) : Prop :=
  ∃ a ∈ phrases s, ∃ b ∈ phrases s, NestedIn ((deps s).map (·.gap)) a b

instance (s : List Token) : Decidable (IsNestedConstruction s) :=
  inferInstanceAs (Decidable (∃ _ ∈ phrases s, _))

/-! ### The annotated sentences -/

/-- The multiple subject relative (44), annotated as (46): *I saw the farmer [who]ₐ Øₐ [owned]ₐ
the dog [which]_b Ø_b [chased]_b the cat*. -/
def subjectRelative : List Token :=
  [.word "I", .word "saw", .word "the", .word "farmer",
    .lbrack, .filler 0 "who", .gap 0, .subcat 0 "owned", .word "the", .word "dog",
      .lbrack, .filler 1 "which", .gap 1, .subcat 1 "chased", .word "the", .word "cat", .rbrack,
    .rbrack]

/-- The multiple object relative (45), annotated as (47): *The cat [which]ₐ the dog [which]_b the
farmer [owned]_b Ø_b [chased]ₐ Øₐ fled*. -/
def objectRelative : List Token :=
  [.word "The", .word "cat",
    .lbrack, .filler 0 "which", .word "the", .word "dog",
      .lbrack, .filler 1 "which", .word "the", .word "farmer", .subcat 1 "owned", .gap 1, .rbrack,
    .subcat 0 "chased", .gap 0, .rbrack,
  .word "fled"]

/-- The German multiple subject relative (48), annotated as (49): *Der Bauer [der]ₐ Øₐ das Mädchen
[das]_b Ø_b den Jungen [küßte]_b [schlug]ₐ ging*. -/
def germanSubjectRelative : List Token :=
  [.word "Der", .word "Bauer",
    .lbrack, .filler 0 "der", .gap 0, .word "das", .word "Mädchen",
      .lbrack, .filler 1 "das", .gap 1, .word "den", .word "Jungen", .subcat 1 "küßte", .rbrack,
    .subcat 0 "schlug", .rbrack,
  .word "ging"]

/-- Multiple pied piping (42), annotated as (50): *John found the saucer [on which]ₐ Mary [put]ₐ
the cup [into which]_b I [poured]_b the tea Ø_b Øₐ*. -/
def multiplePiedPiping : List Token :=
  [.word "John", .word "found", .word "the", .word "saucer",
    .lbrack, .filler 0 "on which", .word "Mary", .subcat 0 "put", .word "the", .word "cup",
      .lbrack, .filler 1 "into which", .word "I", .subcat 1 "poured", .word "the", .word "tea",
      .gap 1, .rbrack,
    .gap 0, .rbrack]

/-- Multiple preposition stranding (60), as (61) annotates it, with its empty categories: *John
found the saucer [which]ₐ Mary put the cup [which]_b I poured the tea [into]_b Ø_b [on]ₐ Øₐ*. -/
def stranding : List Token :=
  [.word "John", .word "found", .word "the", .word "saucer", .filler 0 "which", .word "Mary",
    .word "put", .word "the", .word "cup", .filler 1 "which", .word "I", .word "poured",
    .word "the", .word "tea", .subcat 1 "into", .gap 1, .subcat 0 "on", .gap 0]

/-- The double-object relatives (62), under the reading in which Mary gave the slave the
punishment: *John suggested the punishment [which]ₐ Mary [gave]ₐ the slave [who]_b Tom [sold]_b
the nobleman Ø_b Øₐ*. -/
def doubleObject : List Token :=
  [.word "John", .word "suggested", .word "the", .word "punishment", .filler 0 "which",
    .word "Mary", .subcat 0 "gave", .word "the", .word "slave", .filler 1 "who", .word "Tom",
    .subcat 1 "sold", .word "the", .word "nobleman", .gap 1, .gap 0]

/-- The recursive passive (93), annotated as (94): *[A bone]ₐ was [given]ₐ a dog [which]_b was
[given]_b a man Ø_b Øₐ*. -/
def recursivePassive : List Token :=
  [.filler 0 "A bone", .word "was", .subcat 0 "given", .word "a", .word "dog", .filler 1 "which",
    .word "was", .subcat 1 "given", .word "a", .word "man", .gap 1, .gap 0]

/-- (15) as the empty-category analysis annotates it, with its complex noun phrase bracketed:
*[In which box]ₐ did you [put]ₐ the very large … expensive bakery Øₐ*. -/
def heavyPiedPiping : List Token :=
  [.filler 0 "In which box", .word "did", .word "you", .subcat 0 "put",
    .lbrack, .word "the", .word "very", .word "large", .word "and", .word "beautifully",
      .word "decorated", .word "wedding", .word "cake", .word "bought", .word "from", .word "the",
      .word "expensive", .word "bakery", .rbrack,
    .gap 0]

/-- (16) as the empty-category analysis annotates it, with its complex noun phrase bracketed:
*[Which box]ₐ did you put the very large … expensive bakery [in]ₐ Øₐ*. -/
def heavyStranding : List Token :=
  [.filler 0 "Which box", .word "did", .word "you", .word "put",
    .lbrack, .word "the", .word "very", .word "large", .word "and", .word "beautifully",
      .word "decorated", .word "wedding", .word "cake", .word "bought", .word "from", .word "the",
      .word "expensive", .word "bakery", .rbrack,
    .subcat 0 "in", .gap 0]

/-- The annotated sentences of the paper's argument from recursive constructions, with their
rows. -/
def annotated : List (Datum × List Token) :=
  [(ex42, multiplePiedPiping), (ex44, subjectRelative), (ex45, objectRelative),
   (ex48, germanSubjectRelative), (ex60, stranding), (ex62, doubleObject),
   (ex93, recursivePassive)]

-- Each annotated sentence is well formed.
theorem wellFormed_annotated :
    (∀ p ∈ annotated, WellFormed p.2) ∧ WellFormed heavyPiedPiping ∧
      WellFormed heavyStranding := by
  decide

-- Each annotated sentence, its empty categories dropped, prints as its row.
theorem text_eq_primaryText :
    (∀ p ∈ annotated, text p.2 ++ "." = p.1.primaryText) ∧
      text heavyPiedPiping ++ "?" = ex15.primaryText ∧
      text heavyStranding ++ "?" = ex16.primaryText := by
  decide +kernel

/-! ### The four sentence types (Tables 1 and 2) -/

/-- The four sentence types of Tables 1 and 2. -/
def sentenceTypes : List (List Token) :=
  [subjectRelative, objectRelative, germanSubjectRelative, multiplePiedPiping]

-- In each sentence type one relative clause falls within the other, so Chomsky's definition
-- turns on its nonnull elements.
theorem exists_phrase_lt : ∀ s ∈ sentenceTypes, ∃ a ∈ phrases s, ∃ b ∈ phrases s, a < b := by
  decide

-- Table 1: the filler–gap and gap–verb patterns and the construction type of each sentence type
theorem table1 :
    (IsDisjoint ((deps subjectRelative).map fillerGap) ∧
      IsDisjoint ((deps subjectRelative).map gapVerb) ∧
      ¬ IsNestedConstruction subjectRelative) ∧
    (IsNested ((deps objectRelative).map fillerGap) ∧
      IsDisjoint ((deps objectRelative).map gapVerb) ∧
      IsNestedConstruction objectRelative) ∧
    (IsDisjoint ((deps germanSubjectRelative).map fillerGap) ∧
      IsNested ((deps germanSubjectRelative).map gapVerb) ∧
      IsNestedConstruction germanSubjectRelative) ∧
    (IsNested ((deps multiplePiedPiping).map fillerGap) ∧
      IsNested ((deps multiplePiedPiping).map gapVerb) ∧
      ¬ IsNestedConstruction multiplePiedPiping) := by
  decide

/-- Without empty categories, the filler–verb pattern of each sentence type is nested if the
sentence is a nested construction and disjoint if it is not (Table 2). -/
theorem table2 : ∀ s ∈ sentenceTypes,
    (IsNestedConstruction s → IsNested ((deps s).map fillerVerb)) ∧
      (¬ IsNestedConstruction s → IsDisjoint ((deps s).map fillerVerb)) := by
  decide

-- Without the word *nonnull*, the empty category that ends the outer clause of (50) would make
-- multiple pied piping a nested construction.
theorem nonnull_needed :
    ∃ a ∈ phrases multiplePiedPiping, ∃ b ∈ phrases multiplePiedPiping, NestedIn [] a b := by
  decide

/-! ### Extending the constructions -/

/-- The multiple subject relative with `n` clauses, (44), (51): each clause places a filler, its
empty category and its verb in succession. -/
def localGaps (n : ℕ) : List Dependency :=
  List.ofFn fun k : Fin n ↦ ⟨4 + 5 * k, 5 + 5 * k, 6 + 5 * k⟩

/-- The multiple object relative with `n` clauses, (45), (52): the fillers in succession, then the
verbs in reverse order, each followed by its empty category. -/
def centreEmbedded (n : ℕ) : List Dependency :=
  List.ofFn fun k : Fin n ↦ ⟨2 + 3 * k, 3 + 3 * n + 2 * k.rev, 2 + 3 * n + 2 * k.rev⟩

/-- The German multiple subject relative with `n` clauses, (48), (53): each filler followed by its
empty category, and the verbs at the end in reverse order. -/
def verbFinal (n : ℕ) : List Dependency :=
  List.ofFn fun k : Fin n ↦ ⟨2 + 4 * k, 3 + 4 * k, 2 + 4 * n + k.rev⟩

/-- The `n` clauses from position `a` that each place a filler and two words later its verb,
while the empty-category analysis sites every empty category at the end of the sentence in
reverse order: multiple pied piping (42), (54), (55), the double-object relatives (62) and the
recursive passive (93). -/
def peripheralGaps (a n : ℕ) : List Dependency :=
  List.ofFn fun k : Fin n ↦ ⟨a + 5 * k, a + 5 * n + k.rev, a + 5 * k + 2⟩

-- Each construction with two clauses has the dependencies of the paper's annotation.
theorem deps_eq_ofFn :
    deps subjectRelative = localGaps 2 ∧ deps objectRelative = centreEmbedded 2 ∧
      deps germanSubjectRelative = verbFinal 2 ∧ deps multiplePiedPiping = peripheralGaps 4 2 ∧
      deps doubleObject = peripheralGaps 4 2 ∧ deps recursivePassive = peripheralGaps 0 2 := by
  decide

/-- However many clauses multiple pied piping or the recursive passive has, the empty-category
analysis nests both of its patterns to that depth. -/
theorem peripheralGaps_isNested (a n : ℕ) :
    IsNested ((peripheralGaps a n).map fillerGap) ∧
      IsNested ((peripheralGaps a n).map gapVerb) := by
  simp only [IsNested, peripheralGaps, List.map_ofFn, List.pairwise_ofFn]
  constructor <;> intro i j h <;>
    simp only [Function.comp_apply, fillerGap, gapVerb, NonemptyInterval.During,
      NonemptyInterval.fst_sup, NonemptyInterval.snd_sup, NonemptyInterval.pure, Fin.val_rev,
      Fin.lt_def] at * <;>
    omega

-- The filler–verb pattern of multiple pied piping stays disjoint at any depth.
theorem peripheralGaps_isDisjoint (a n : ℕ) :
    IsDisjoint ((peripheralGaps a n).map fillerVerb) := by
  simp only [IsDisjoint, peripheralGaps, List.map_ofFn, List.pairwise_ofFn]
  intro i j h
  simp only [Function.comp_apply, fillerVerb, NonemptyInterval.Overlaps,
    NonemptyInterval.fst_sup, NonemptyInterval.snd_sup, NonemptyInterval.pure, Fin.lt_def] at *
  omega

theorem localGaps_isDisjoint (n : ℕ) :
    IsDisjoint ((localGaps n).map fillerGap) ∧ IsDisjoint ((localGaps n).map gapVerb) ∧
      IsDisjoint ((localGaps n).map fillerVerb) := by
  simp only [IsDisjoint, localGaps, List.map_ofFn, List.pairwise_ofFn]
  refine ⟨?_, ?_, ?_⟩ <;> intro i j h <;>
    simp only [Function.comp_apply, fillerGap, gapVerb, fillerVerb, NonemptyInterval.Overlaps,
      NonemptyInterval.fst_sup, NonemptyInterval.snd_sup, NonemptyInterval.pure,
      Fin.lt_def] at * <;>
    omega

theorem centreEmbedded_isNested (n : ℕ) :
    IsNested ((centreEmbedded n).map fillerGap) ∧
      IsNested ((centreEmbedded n).map fillerVerb) := by
  simp only [IsNested, centreEmbedded, List.map_ofFn, List.pairwise_ofFn]
  constructor <;> intro i j h <;>
    simp only [Function.comp_apply, fillerGap, fillerVerb, NonemptyInterval.During,
      NonemptyInterval.fst_sup, NonemptyInterval.snd_sup, NonemptyInterval.pure, Fin.val_rev,
      Fin.lt_def] at * <;>
    omega

theorem centreEmbedded_isDisjoint (n : ℕ) : IsDisjoint ((centreEmbedded n).map gapVerb) := by
  simp only [IsDisjoint, centreEmbedded, List.map_ofFn, List.pairwise_ofFn]
  intro i j h
  simp only [Function.comp_apply, gapVerb, NonemptyInterval.Overlaps, NonemptyInterval.fst_sup,
    NonemptyInterval.snd_sup, NonemptyInterval.pure, Fin.val_rev, Fin.lt_def] at *
  omega

theorem verbFinal_isNested (n : ℕ) :
    IsNested ((verbFinal n).map gapVerb) ∧ IsNested ((verbFinal n).map fillerVerb) := by
  simp only [IsNested, verbFinal, List.map_ofFn, List.pairwise_ofFn]
  constructor <;> intro i j h <;>
    simp only [Function.comp_apply, gapVerb, fillerVerb, NonemptyInterval.During,
      NonemptyInterval.fst_sup, NonemptyInterval.snd_sup, NonemptyInterval.pure, Fin.val_rev,
      Fin.lt_def] at * <;>
    omega

theorem verbFinal_isDisjoint (n : ℕ) : IsDisjoint ((verbFinal n).map fillerGap) := by
  simp only [IsDisjoint, verbFinal, List.map_ofFn, List.pairwise_ofFn]
  intro i j h
  simp only [Function.comp_apply, fillerGap, NonemptyInterval.Overlaps, NonemptyInterval.fst_sup,
    NonemptyInterval.snd_sup, NonemptyInterval.pure, Fin.lt_def] at *
  omega

/-! ### Processing difficulty -/

/-- The paper reports the sentence hard to process. Its examples are grammatical and printed
unmarked, so difficulty is a separate observation from the judgment. -/
def Hard (e : Datum) : Prop := e.feature? "difficulty" = some "hard"

instance : DecidablePred Hard := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The sentences of the paper's argument from recursive constructions, with their
dependencies: those it annotates, and its extensions of them to further clauses. -/
def rows : List (Datum × List Dependency) :=
  annotated.map (Prod.map id deps) ++
    [(ex51, localGaps 3), (ex52, centreEmbedded 3), (ex53, verbFinal 3),
     (ex54, peripheralGaps 4 3), (ex55, peripheralGaps 4 5)]

-- Every sentence the paper reports hard to process is a row, or the heavy-NP example (16).
theorem hard_mem_rows : ∀ e ∈ all, Hard e → e ∈ rows.map Prod.fst ∨ e = ex16 := by
  decide +kernel

/-- A sentence the paper reports is hard to process exactly when its filler–verb pattern is
nested. -/
theorem difficulty : ∀ p ∈ rows, Hard p.1 ↔ IsNested (p.2.map fillerVerb) := by
  decide

-- The empty-category analysis, which predicts a sentence hard when either of its patterns is
-- nested, errs on exactly the multiple pied piping of (42), (54) and (55), the double-object
-- relatives of (62) and the recursive passive of (93).
theorem trace_prediction_fails : ∀ p ∈ rows,
    ¬ (Hard p.1 ↔ IsNested (p.2.map fillerGap) ∨ IsNested (p.2.map gapVerb)) ↔
      p.1 ∈ [ex42, ex54, ex55, ex62, ex93] := by
  decide +kernel

-- (15), (16): of the two, the gap-free analysis holds only the filler of the awkward (16) across
-- the complex noun phrase, and the empty-category analysis holds both.
theorem heavy_np :
    (¬ Hard ex15 ∧ Hard ex16) ∧
      (∃ d ∈ deps heavyPiedPiping, ∃ np ∈ phrases heavyPiedPiping,
        d.fillerVerb.Precedes np ∧ np ≤ d.fillerGap) ∧
      ∃ d ∈ deps heavyStranding, ∃ np ∈ phrases heavyStranding,
        np ≤ d.fillerVerb ∧ np ≤ d.fillerGap := by
  decide

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

/-! ### Logical forms -/

open Montague
open CCG (LexEntry)

/-- The semantic type of a basic category: a sentence denotes a truth value, a noun phrase and a
prepositional phrase an individual, and an embedded question the property its wh-word
abstracts. -/
def atomTy : Basic → Ty
  | .S => .t
  | .Q => .e ⇒ .t
  | .NP => .e
  | .PP => .e

/-- The function symbols of the fragment's signature are the names. -/
inductive Func : ℕ → Type
  | sue : Func 0
  | john : Func 0
  | mary : Func 0

/-- The relation symbols of the fragment's signature are its transitive verbs, the paper's
`saw(x,y)` and `talked-to(x,y)`, subject first. -/
inductive Rel : ℕ → Type
  | saw : Rel 2
  | talkedTo : Rel 2

/-- The first-order signature of the fragment. -/
def lang : FirstOrder.Language :=
  { Functions := Func
    Relations := Rel }

/-- The constants of the logical forms are the first-order constants of the signature and
*wonders*, which relates an individual to the property an embedded question denotes. -/
inductive Const : Ty → Type
  | fo {ty : Ty} (c : FirstOrderConstant lang ty) : Const ty
  | wonders : Const ((.e ⇒ .t) ⇒ .e ⇒ .t)

/-- At the world `w` of a model `m`, the first-order constants denote what its structure gives
them, and *wonders* denotes the relation `wo` between an individual and a property. -/
def Const.interp (m : Model lang) (w : m.W) (wo : m.E → (m.E → Prop) → Prop) :
    {ty : Ty} → Const ty → Ty.Domain m.E m.W ty
  | _, .fo c => c.interp m w
  | _, .wonders => fun q x ↦ wo x q

/-- The typing of the variables of the logical forms: the index `0` ranges over individuals and
the others over properties. -/
def indices : ℕ → Ty
  | 0 => .e
  | _ + 1 => .e ⇒ .t

/-- The lexicon of (79)–(85). A transitive verb denotes its relation object first, the paper's
`λyλx[saw(x,y)]`. The raised *John*, through which rule (80a) combines the subject with a verb
before its object, has the lift `λP[P(John)]`. The subject pronoun *who* takes a sentence missing
its subject and the object pronoun *whom* one missing an object, each passing on the property
it takes, as *to* passes on its individual. -/
def lexicon : List (LexEntry String atomTy indices Const) :=
  [⟨"Sue", np, .const (.fo (.name Func.sue))⟩, ⟨"John", np, .const (.fo (.name Func.john))⟩,
   ⟨"John", sent / (sent \ np),
      .lam 1 (.comp .functionalLeft (.var 1) (.const (.fo (.name Func.john))))⟩,
   ⟨"Mary", np, .const (.fo (.name Func.mary))⟩,
   ⟨"saw", (sent \ np) / np, .const (.fo (.rel₂ Rel.saw))⟩,
   ⟨"talked", (sent \ np) / pp, .const (.fo (.rel₂ Rel.talkedTo))⟩,
   ⟨"to", pp / np, .lam 0 (.var 0)⟩, ⟨"wonders", (sent \ np) / quest, .const .wonders⟩,
   ⟨"who", quest / (sent \ np), .lam 1 (.var 1)⟩, ⟨"whom", quest / (sent / np), .lam 1 (.var 1)⟩]

/-- The words of (82d) with the wh-word `w`. -/
def words82d (w : String) : List String := ["Sue", "wonders", w, "John", "saw", "Mary"]

-- (82d) with *who* is the row the paper stars.
theorem words82d_who : unwords (words82d "who") ++ "." = ex82d.primaryText := by
  decide +kernel

/-- *Sue wonders who John saw Mary* (82d) has no derivation, with *who* or *whom*, in any rule
system: no wh-word takes a whole sentence, so the pronoun must fill an argument role of the
embedded verb. -/
theorem no_der82d (R : CCG.RuleSystem Basic) (w : String) (hw : w = "who" ∨ w = "whom") :
    ¬ ∃ d : CCG.Derivation String R sent,
      d.LexIn (lexicon.map LexEntry.toPair) ∧ d.yield = words82d w := by
  rintro ⟨d, hd, hy⟩
  have h := d.count_eq_sum .NP
    (f := fun t ↦ (((lexicon.map LexEntry.toPair).find? (·.1 = t)).map (·.2.count .NP)).getD 0)
    (by decide) hd
  rw [hy] at h
  rcases hw with rfl | rfl <;> exact absurd h (by decide)

section Semantics

variable (m : Model lang) (w : m.W) (wo : m.E → (m.E → Prop) → Prop)
  (g : ∀ n, Ty.Domain m.E m.W (indices n))

-- (79), (81): in every model both derivations of *John saw Mary* mean `saw(John,Mary)`, the
-- relation taking its object first.
theorem der79_der81 :
    (der79.LexIn (lexicon.map LexEntry.toPair) ∧ der81.LexIn (lexicon.map LexEntry.toPair) ∧
      der79.yield = der81.yield) ∧
    der79.interp lexicon (Const.interp m w wo) g =
      some (m.pred₂ Rel.saw w (m.const Func.mary w) (m.const Func.john w)) ∧
    der81.interp lexicon (Const.interp m w wo) g =
      some (m.pred₂ Rel.saw w (m.const Func.mary w) (m.const Func.john w)) :=
  ⟨by decide, rfl, rfl⟩

/-- In every model, each wh-word of (82a–c) fills the argument role that its embedded verb or
preposition assigns, with no empty category: *who* abstracts over the subject of *saw*, *whom*
over its object and over the object of *to*. -/
theorem embedded_questions :
    (der82a.LexIn (lexicon.map LexEntry.toPair) ∧
      unwords der82a.yield ++ "." = ex82a.primaryText ∧
      der82a.interp lexicon (Const.interp m w wo) g =
        some (wo (m.const Func.sue w) fun x ↦ m.pred₂ Rel.saw w (m.const Func.mary w) x)) ∧
    (der82b.LexIn (lexicon.map LexEntry.toPair) ∧
      unwords der82b.yield ++ "." = ex82b.primaryText ∧
      der82b.interp lexicon (Const.interp m w wo) g =
        some (wo (m.const Func.sue w) fun y ↦ m.pred₂ Rel.saw w y (m.const Func.john w))) ∧
    (der82c.LexIn (lexicon.map LexEntry.toPair) ∧
      unwords der82c.yield ++ "." = ex82c.primaryText ∧
      der82c.interp lexicon (Const.interp m w wo) g =
        some (wo (m.const Func.sue w) fun y ↦ m.pred₂ Rel.talkedTo w y (m.const Func.john w))) :=
  ⟨⟨by decide, by decide +kernel, rfl⟩, ⟨by decide, by decide +kernel, rfl⟩,
    ⟨by decide, by decide +kernel, rfl⟩⟩

end Semantics

end PickeringBarry1991
