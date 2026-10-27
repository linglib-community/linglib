module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Syntax.CCG.Derivation
public import Linglib.Data.Examples.PickeringBarry1991

/-!
# Pickering and Barry (1991): Sentence Processing without Empty Categories

This file formalizes [pickering-barry-1991]'s argument that the processing of an unbounded
dependency associates the filler directly with its subcategoriser and never with an empty
category. An analysis with empty categories makes two associations per dependency, filler to
gap and gap to verb; the gap-free analysis makes one, filler to verb. Each association spans an
interval of the sentence, a pattern of associations is nested when one association lies strictly
inside another (abba) and disjoint when none overlap (aabb), and nested associations are the
ones that must be held open while others are formed.

Under the analysis with empty categories neither pattern lines up with nested constructions in
Chomsky's sense or with the reported difficulty (Table 1): the multiple pied-piping sentence
(42) has nested filler–gap and nested gap–verb associations yet is as easy as the multiple
subject relative. Under the gap-free analysis the one pattern coincides with nestedness in Chomsky's
sense (Table 2) and with the reported difficulty (`table1`, `table2`, `difficulty`,
`trace_prediction_fails`), and it stays disjoint however far the pied-piping and the recursive
passive are extended, where the empty-category analysis holds every filler to the end of the
sentence (`peripheralGaps_fillerVerb_disjoint`, `peripheralGaps_fillerGap_common`). The
categorial grammar of the paper's later sections derives the embedded questions (82a–c) with no
empty category (`der82a`, `der82b`, `der82c`), and (82d) has no derivation in any rule system
because the pronoun must fill an argument role of the embedded verb, which is the count
invariant of van Benthem (`no_der82d`).

## Implementation notes

Associations are spans between word positions of the paper's annotated strings, empty
categories included; a nested construction in Chomsky's sense is the same relation on the
lexical spans of the relative clauses, which is where the paper's removal of "nonnull" from
the definition shows up. The paper's rule (80a), which combines a subject with a transitive verb
before its object, is the composition of the subject's raised category with the verb, so the
lexicon carries the raised entry, as in `Syntax/CCG/Derivation`. The semantic side of the
derivations and the discussion of incremental interpretation are not formalized.

## References

* [pickering-barry-1991]
* [van-benthem-1986]
-/

@[expose] public section

namespace PickeringBarry1991

open Examples
open scoped CCG

/-! ### Associations and their patterns -/

/-- A dependency of an annotated sentence records the positions of its filler, of the empty
category the trace analysis posits, and of its subcategoriser. -/
structure Dependency where
  filler : ℕ
  gap : ℕ
  verb : ℕ
  deriving DecidableEq, Repr

/-- The span between two positions. -/
def span (i j : ℕ) : NonemptyInterval ℕ := ⟨(min i j, max i j), min_le_max⟩

@[simp] theorem span_fst (i j : ℕ) : (span i j).fst = min i j := rfl

@[simp] theorem span_snd (i j : ℕ) : (span i j).snd = max i j := rfl

namespace Dependency

/-- The filler–gap association of the trace analysis. -/
def fillerGap (d : Dependency) : NonemptyInterval ℕ := span d.filler d.gap

/-- The gap–verb association of the trace analysis. -/
def gapVerb (d : Dependency) : NonemptyInterval ℕ := span d.gap d.verb

/-- The filler–verb association of the gap-free analysis. -/
def fillerVerb (d : Dependency) : NonemptyInterval ℕ := span d.filler d.verb

theorem fillerVerb_gap (f g g' v : ℕ) :
    (⟨f, g, v⟩ : Dependency).fillerVerb = (⟨f, g', v⟩ : Dependency).fillerVerb := rfl

end Dependency

/-- A pattern of associations is nested when one association lies strictly inside another. -/
def Nested (L : List (NonemptyInterval ℕ)) : Prop := ∃ a ∈ L, ∃ b ∈ L, a.During b

instance (L : List (NonemptyInterval ℕ)) : Decidable (Nested L) :=
  inferInstanceAs (Decidable (∃ _ ∈ L, _))

/-- A pattern of associations is disjoint when any two of them are one before the other. -/
def Disjoint (L : List (NonemptyInterval ℕ)) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → a.Precedes b ∨ b.Precedes a

instance (L : List (NonemptyInterval ℕ)) : Decidable (Disjoint L) :=
  inferInstanceAs (Decidable (∀ _ ∈ L, ∀ _ ∈ L, _ → _))

theorem Disjoint.not_nested {L : List (NonemptyInterval ℕ)} (h : Disjoint L) : ¬ Nested L :=
  fun ⟨a, ha, b, hb, hab⟩ ↦ (h a ha b hb fun e ↦ NonemptyInterval.during_irrefl b (e ▸ hab)).elim
    (NonemptyInterval.not_precedes_of_during hab).1 (NonemptyInterval.not_precedes_of_during hab).2

/-- An annotated sentence records its dependencies and the spans of its relative clauses over
the lexical positions. -/
structure Analysis where
  deps : List Dependency
  clauses : List (NonemptyInterval ℕ)

namespace Analysis

/-- The filler–gap associations. -/
def fillerGap (A : Analysis) : List (NonemptyInterval ℕ) := A.deps.map Dependency.fillerGap

/-- The gap–verb associations. -/
def gapVerb (A : Analysis) : List (NonemptyInterval ℕ) := A.deps.map Dependency.gapVerb

/-- The filler–verb associations. -/
def fillerVerb (A : Analysis) : List (NonemptyInterval ℕ) := A.deps.map Dependency.fillerVerb

/-- A construction is nested in Chomsky's sense when a clause lies inside another with lexical
material on both sides of it. -/
def IsNestedConstruction (A : Analysis) : Prop := Nested A.clauses

instance (A : Analysis) : Decidable A.IsNestedConstruction := inferInstanceAs (Decidable (Nested _))

end Analysis

/-! ### The four sentence types (Tables 1 and 2) -/

/-- The multiple subject relative (44), *I saw the farmer [who]ₐ Ø [owned]ₐ the dog [which]ᵦ Ø
[chased]ᵦ the cat*, annotated as (46) and (56). -/
def subjectRelative : Analysis := ⟨[⟨4, 5, 6⟩, ⟨9, 10, 11⟩], [span 4 13, span 9 13]⟩

/-- The multiple object relative (45), *The cat [which]ₐ the dog [which]ᵦ the farmer [owned]ᵦ Ø
[chased]ₐ Ø fled*, annotated as (47) and (57). -/
def objectRelative : Analysis := ⟨[⟨2, 11, 10⟩, ⟨5, 9, 8⟩], [span 2 10, span 5 8]⟩

/-- The German multiple subject relative (48), *Der Bauer [der]ₐ Ø das Mädchen [das]ᵦ Ø den
Jungen [küßte]ᵦ [schlug]ₐ ging*, annotated as (49) and (58). -/
def germanSubjectRelative : Analysis := ⟨[⟨2, 3, 11⟩, ⟨6, 7, 10⟩], [span 2 11, span 6 10]⟩

/-- The multiple pied-piping sentence (42), *John found the saucer [on which]ₐ Mary [put]ₐ the
cup [into which]ᵦ I [poured]ᵦ the tea Ø Ø*, annotated as (50) and (59). -/
def piedPiping : Analysis := ⟨[⟨4, 15, 6⟩, ⟨9, 14, 11⟩], [span 4 13, span 9 13]⟩

/-- The four sentence types of Tables 1 and 2. -/
def sentenceTypes : List Analysis :=
  [subjectRelative, objectRelative, germanSubjectRelative, piedPiping]

/-- With empty categories, neither the filler–gap pattern nor the gap–verb pattern tracks the
construction type (Table 1). -/
theorem table1 :
    ¬ (∀ A ∈ sentenceTypes, Nested A.fillerGap ↔ A.IsNestedConstruction) ∧
      ¬ (∀ A ∈ sentenceTypes, Nested A.gapVerb ↔ A.IsNestedConstruction) := by
  decide

/-- Without empty categories, the filler–verb pattern is nested exactly in the nested
constructions (Table 2). -/
theorem table2 : ∀ A ∈ sentenceTypes, Nested A.fillerVerb ↔ A.IsNestedConstruction := by
  decide

/-- The four sentence types with their analyses. -/
def rows : List (Datum × Analysis) :=
  [(ex44, subjectRelative), (ex45, objectRelative), (ex48, germanSubjectRelative),
   (ex42, piedPiping)]

/-- The paper reports the sentence hard to process. Its examples are grammatical and printed
unmarked, so difficulty is a separate observation from the judgment. -/
def Hard (e : Datum) : Prop := e.feature? "difficulty" = some "hard"

instance : DecidablePred Hard := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem difficulty : ∀ p ∈ rows, Hard p.1 ↔ Nested p.2.fillerVerb := by
  decide

theorem trace_prediction_fails :
    Nested piedPiping.fillerGap ∧ Nested piedPiping.gapVerb ∧ ¬ Hard ex42 := by
  decide

-- (15), (16)
theorem stranding :
    ¬ Hard ex15 ∧ Hard ex16 ∧
      ((⟨0, 15, 3⟩ : Dependency).fillerVerb).snd
        < ((⟨0, 14, 14⟩ : Dependency).fillerVerb).snd := by
  decide

/-! ### Extending the constructions -/

/-- The constructions whose `n` relative clauses each place a filler and, two words later, its
verb, while the trace analysis sites all `n` gaps at the end of the sentence: multiple pied
piping from position 4, (42), (54), (55), and the recursive passive from position 0, (93)–(95).
-/
def peripheralGaps (a n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦ ⟨a + 5 * k, a + 5 * n + (n - 1 - k), a + 5 * k + 2⟩

/-- The multiple subject relative with `n` clauses, (44), (51), each of which places a filler,
its gap and its verb in succession. -/
def localGaps (n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦ ⟨4 + 5 * k, 5 + 5 * k, 6 + 5 * k⟩

/-- The multiple object relative with `n` clauses, (45), (52), which places the fillers in
succession and then the verbs in reverse order, each followed by its gap. -/
def centreEmbedded (n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦
    ⟨2 + 3 * k, 2 + 3 * n + 2 * (n - 1 - k) + 1, 2 + 3 * n + 2 * (n - 1 - k)⟩

/-- The German multiple subject relative with `n` clauses, (48), (53), which places each filler
before its gap and then the verbs in reverse order. -/
def verbFinal (n : ℕ) : List Dependency :=
  (List.range n).map fun k ↦ ⟨2 + 4 * k, 3 + 4 * k, 2 + 4 * n + (n - 1 - k)⟩

theorem peripheralGaps_fillerVerb_disjoint (a n : ℕ) :
    Disjoint ((peripheralGaps a n).map Dependency.fillerVerb) := by
  simp only [Disjoint, peripheralGaps, List.map_map, List.mem_map, List.mem_range,
    Function.comp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro i hi j hj hne
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact Or.inl (by simp [NonemptyInterval.Precedes, Dependency.fillerVerb]; omega)
  · exact absurd rfl hne
  · exact Or.inr (by simp [NonemptyInterval.Precedes, Dependency.fillerVerb]; omega)

theorem peripheralGaps_fillerGap_common (a n : ℕ) :
    ∀ d ∈ peripheralGaps a n, a + 5 * n ∈ d.fillerGap := by
  simp only [peripheralGaps, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Dependency.fillerGap, NonemptyInterval.mem_def, span_fst, span_snd]
  intro k hk
  omega

theorem peripheralGaps_nested (a n : ℕ) (hn : 2 ≤ n) :
    Nested ((peripheralGaps a n).map Dependency.fillerGap) ∧
      Nested ((peripheralGaps a n).map Dependency.gapVerb) := by
  simp only [Nested, peripheralGaps, List.map_map, List.mem_map, List.mem_range, Function.comp,
    exists_exists_and_eq_and, Dependency.fillerGap, Dependency.gapVerb, NonemptyInterval.During,
    span_fst, span_snd]
  exact ⟨⟨1, by omega, 0, by omega, by omega⟩, ⟨1, by omega, 0, by omega, by omega⟩⟩

theorem localGaps_disjoint (n : ℕ) :
    Disjoint ((localGaps n).map Dependency.fillerGap) ∧
      Disjoint ((localGaps n).map Dependency.gapVerb) ∧
      Disjoint ((localGaps n).map Dependency.fillerVerb) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [Disjoint, localGaps, List.map_map, List.mem_map, List.mem_range, Function.comp,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro i hi j hj hne
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · exact Or.inl (by simp [NonemptyInterval.Precedes, Dependency.fillerGap, Dependency.gapVerb,
        Dependency.fillerVerb]; omega)
    · exact absurd rfl hne
    · exact Or.inr (by simp [NonemptyInterval.Precedes, Dependency.fillerGap, Dependency.gapVerb,
        Dependency.fillerVerb]; omega)

theorem centreEmbedded_common (n : ℕ) :
    ∀ d ∈ centreEmbedded n, 2 + 3 * n ∈ d.fillerVerb ∧ 2 + 3 * n ∈ d.fillerGap := by
  simp only [centreEmbedded, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Dependency.fillerVerb, Dependency.fillerGap,
    NonemptyInterval.mem_def, span_fst, span_snd]
  intro k hk
  omega

theorem verbFinal_common (n : ℕ) :
    (∀ d ∈ verbFinal n, 2 + 4 * n ∈ d.fillerVerb ∧ 2 + 4 * n ∈ d.gapVerb) ∧
      Disjoint ((verbFinal n).map Dependency.fillerGap) := by
  refine ⟨?_, ?_⟩
  · simp only [verbFinal, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Dependency.fillerVerb, Dependency.gapVerb,
      NonemptyInterval.mem_def, span_fst, span_snd]
    intro k hk
    omega
  · simp only [Disjoint, verbFinal, List.map_map, List.mem_map, List.mem_range, Function.comp,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro i hi j hj hne
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · exact Or.inl (by simp [NonemptyInterval.Precedes, Dependency.fillerGap]; omega)
    · exact absurd rfl hne
    · exact Or.inr (by simp [NonemptyInterval.Precedes, Dependency.fillerGap]; omega)

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

/-- The lexicon of (82)–(85). The subject pronoun *who* takes a sentence missing its subject,
the object pronoun *whom* a sentence missing an object, and *John* carries the raised category
through which rule (80a) combines it with a verb before the verb's object. -/
def lexicon : List (String × CCG.Cat Basic) :=
  [("Sue", np), ("John", np), ("John", sent / (sent \ np)), ("Mary", np),
   ("saw", (sent \ np) / np), ("talked", (sent \ np) / pp), ("to", pp / np),
   ("wonders", (sent \ np) / quest), ("who", quest / (sent \ np)), ("whom", quest / (sent / np))]

/-- The derivation (83) of *who saw Mary*, in which the subject pronoun applies to a sentence
missing its subject. -/
def der83 : CCG.Derivation String .multimodal quest :=
  .fapp (.lex "who" (quest / (sent \ np))) (.fapp (.lex "saw" ((sent \ np) / np)) (.lex "Mary" np))

/-- The derivation (84) of *whom John saw*, in which the raised subject composes with the verb
into a sentence missing its object, which the object pronoun takes. -/
def der84 : CCG.Derivation String .multimodal quest :=
  .fapp (.lex "whom" (quest / (sent / np)))
    (.fcomp (.lex "John" (sent / (sent \ np))) (.lex "saw" ((sent \ np) / np)))

/-- The derivation (85) of *whom John talked to*, in which two compositions leave the
preposition's object missing. -/
def der85 : CCG.Derivation String .multimodal quest :=
  .fapp (.lex "whom" (quest / (sent / np)))
    (.fcomp (.fcomp (.lex "John" (sent / (sent \ np)))
      (.lex "talked" ((sent \ np) / pp))) (.lex "to" (pp / np)))

/-- *Sue wonders* applied to an embedded question. -/
def wonders (d : CCG.Derivation String .multimodal quest) :
    CCG.Derivation String .multimodal sent :=
  .bapp (.lex "Sue" np) (.fapp (.lex "wonders" ((sent \ np) / quest)) d)

/-- (82a). -/
def der82a : CCG.Derivation String .multimodal sent := wonders der83

/-- (82b). -/
def der82b : CCG.Derivation String .multimodal sent := wonders der84

/-- (82c). -/
def der82c : CCG.Derivation String .multimodal sent := wonders der85

-- (82a–c)
theorem embedded_questions :
    (der82a.LexIn lexicon ∧ der82a.yield = ["Sue", "wonders", "who", "saw", "Mary"]) ∧
      (der82b.LexIn lexicon ∧ der82b.yield = ["Sue", "wonders", "whom", "John", "saw"]) ∧
      (der82c.LexIn lexicon ∧
        der82c.yield = ["Sue", "wonders", "whom", "John", "talked", "to"]) := by
  decide

/-- The noun phrases each word of the fragment contributes to the count invariant. A verb
consumes its arguments and a pronoun supplies the one it fills. -/
def npCount : String → ℤ
  | "saw" => -2
  | "talked" | "to" | "wonders" => -1
  | _ => 1

/-- *Sue wonders who John saw Mary* (82d) has no derivation, with *who* or *whom*, in any rule
system. -/
theorem no_der82d (R : CCG.RuleSystem Basic) (w : String) (hw : w = "who" ∨ w = "whom") :
    ¬ ∃ d : CCG.Derivation String R sent,
      d.LexIn lexicon ∧ d.yield = ["Sue", "wonders", w, "John", "saw", "Mary"] := by
  rintro ⟨d, hd, hy⟩
  have h := d.count_eq_sum .NP (f := npCount) (by decide) hd
  rw [hy] at h
  rcases hw with rfl | rfl <;> exact absurd h (by decide)

end PickeringBarry1991
