module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Finset.Image
public import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Moraic representations

A moraic representation sets prosodic nodes over a melody, the string of segments in which
segment `i` occupies slot `i`: prosodic words, syllables and morae. Each tier of nodes dominates
the tier below, and a node of any tier may also be linked to segments directly, so that an onset
or a non-moraic nucleus is linked to its syllable and an extrasyllabic consonant to its word. The
mora is the unit of weight ([hyman-1985], [hayes-1989]): the weight of a syllable is its number
of morae. In the one-root theory of length of [hayes-1989] a long segment is one segment with two
association lines, a long vowel under two morae and a geminate under a mora of one syllable and
the onset of the next; in the two-root theory of [selkirk-1990] it is two segments.

Nothing ties a mora to a nucleus. A syllable may have no mora, as a minor syllable has none
([shih-2018]); a coda may share the vowel's mora ([broselow-chen-huffman-1997]) or be linked to
the syllable itself ([selkirk-1990]); a mora may dominate a segment but no syllable
([topintzi-zimmermann-2025]); and in Shiwilu a syllable whose nucleus is the interior vowel has
its coda's mora as its only one ([vasquez-aguilar-etal-2026]).

## Main definitions

* `Prosody.Mora`, `Prosody.MoraicForm`: a mora node, and a moraic representation.
* `MoraicForm.ofLines`: the form given by its lines, with the nodes they join.
* `MoraicForm.head`: the segment that heads a mora.
* `MoraicForm.syllablesOf`, `MoraicForm.moraeOf`: the syllables of a word, the morae of a
  syllable.
* `MoraicForm.moraSpan`, `MoraicForm.yield`, `MoraicForm.wordYield`: the slots a mora, a
  syllable and a word dominate.
* `MoraicForm.weight`, `MoraicForm.onset`, `MoraicForm.coda`: the weight, the onset and the coda
  of a syllable.
* `MoraicForm.moraeAt`, `MoraicForm.lineCount`: the morae linked to a segment, and its number of
  lines.
* `MoraicForm.free`, `MoraicForm.stranded`: the morae no syllable dominates, and those that
  dominate nothing.
* `MoraicForm.WellFormed`, `MoraicForm.NoCrossing`: lines join nodes and slots that are present,
  and do not cross.
* `MoraicForm.delete`, `MoraicForm.linkMora`, `MoraicForm.delinkMora`,
  `MoraicForm.linkSyllable`: erasing and drawing lines.

## Main statements

* `MoraicForm.noCrossing_linkMora_iff`, `MoraicForm.noCrossing_linkSyllable_iff`: a line can be
  drawn without crossing exactly when it ends in its node's window.

## Implementation notes

* Every node is placed at a slot: a mora at the segment that heads it ([zec-1995],
  [broselow-chen-huffman-1997]), a syllable at its nucleus, and a word at the nucleus of its head
  syllable. A syllable and a word are named by their slots, a mora by its slot and an index
  telling apart the morae one segment heads. The head of a syllable in [zec-1995] is its leftmost
  mora, which in Shiwilu is not placed at the nucleus.
* The nodes of every tier stand on the one timeline of the melody, so that a line from a mora
  can cross a line from a syllable, as the vowel-loss asymmetry of [hayes-1989] requires and as
  the reading of association as overlap in time ([sagey-1986]) predicts; a line of domination is
  compared only with lines between the same two tiers. A node keeps its place when its lines are
  erased, so that a mora stranded by deletion is still ordered.
* A form is a candidate for constraints that penalize moraless syllables, shared morae, or
  geminates, so `WellFormed` asks only that lines join nodes and slots that are present.

## TODO

* Correspondence of morae, for faithfulness to underlying morae and for the length of a segment
  under an underlying mora ([topintzi-zimmermann-2025]).

## References

* [hyman-1985]
* [hayes-1989]
* [sagey-1986]
* [selkirk-1990]
* [zec-1995]
* [broselow-chen-huffman-1997]
* [shih-2018]
* [topintzi-zimmermann-2025]
* [vasquez-aguilar-etal-2026]
-/

@[expose] public section

namespace Prosody

open Autosegmental Finset

/-- A mora: the slot of the segment that heads it, and an index telling apart the morae one
segment heads, such as the two of a long vowel. -/
structure Mora where
  /-- The slot of the head segment. -/
  slot : ℕ
  /-- The index among the morae of one head. -/
  idx : ℕ
  deriving DecidableEq, Repr

/-- The `k`-th mora headed by the segment at slot `i`. -/
abbrev Mora.of (i : ℕ) (k : ℕ := 0) : Mora := ⟨i, k⟩

/-- A moraic representation over a melody. -/
@[ext]
structure MoraicForm (α : Type*) where
  /-- The segments, segment `i` at slot `i`. -/
  melody : List α := []
  /-- The prosodic words, each named by its slot. -/
  words : Finset ℕ := ∅
  /-- The syllables, each named by the slot of its nucleus. -/
  syllables : Finset ℕ := ∅
  /-- The morae. -/
  morae : Finset Mora := ∅
  /-- Domination of syllables by words. -/
  wordSyllable : Finset (ℕ × ℕ) := ∅
  /-- Domination of morae by syllables. -/
  syllableMora : Finset (ℕ × Mora) := ∅
  /-- Lines from words to the segments they dominate directly. -/
  wordSegment : Finset (ℕ × ℕ) := ∅
  /-- Lines from syllables to the segments they dominate directly. -/
  syllableSegment : Finset (ℕ × ℕ) := ∅
  /-- Lines from morae to the segments they dominate. -/
  moraSegment : Finset (Mora × ℕ) := ∅

namespace MoraicForm

variable {α : Type*} (X : MoraicForm α)

instance [DecidableEq α] : DecidableEq (MoraicForm α) := fun X Y ↦
  decidable_of_iff (X.melody = Y.melody ∧ X.words = Y.words ∧ X.syllables = Y.syllables ∧
    X.morae = Y.morae ∧ X.wordSyllable = Y.wordSyllable ∧ X.syllableMora = Y.syllableMora ∧
    X.wordSegment = Y.wordSegment ∧ X.syllableSegment = Y.syllableSegment ∧
    X.moraSegment = Y.moraSegment) MoraicForm.ext_iff.symm

/-- The slots of the melody. -/
def slots : Finset ℕ := range X.melody.length

/-- The form over `melody` with the given lines and with the nodes they join, as a graph is
given by its edges. A node joined by no line, such as a stranded mora, is added afterwards. -/
def ofLines (melody : List α) (wordSyllable : Finset (ℕ × ℕ) := ∅)
    (syllableMora : Finset (ℕ × Mora) := ∅) (wordSegment : Finset (ℕ × ℕ) := ∅)
    (syllableSegment : Finset (ℕ × ℕ) := ∅) (moraSegment : Finset (Mora × ℕ) := ∅) :
    MoraicForm α where
  melody := melody
  words := wordSyllable.image Prod.fst ∪ wordSegment.image Prod.fst
  syllables := wordSyllable.image Prod.snd ∪ syllableMora.image Prod.fst ∪
    syllableSegment.image Prod.fst
  morae := syllableMora.image Prod.snd ∪ moraSegment.image Prod.fst
  wordSyllable := wordSyllable
  syllableMora := syllableMora
  wordSegment := wordSegment
  syllableSegment := syllableSegment
  moraSegment := moraSegment

/-- The segment that heads mora `m`. -/
def head (m : Mora) : Option α := X.melody[m.slot]?

/-! ### Domination -/

/-- The syllables of word `w`. -/
def syllablesOf (w : ℕ) : Finset ℕ :=
  X.syllables.bipartiteAbove (fun w s ↦ (w, s) ∈ X.wordSyllable) w

/-- The morae of syllable `s`. -/
def moraeOf (s : ℕ) : Finset Mora := X.morae.bipartiteAbove (fun s m ↦ (s, m) ∈ X.syllableMora) s

/-- The slots word `w` is linked to directly. -/
def wordSpan (w : ℕ) : Finset ℕ := X.slots.bipartiteAbove (fun w i ↦ (w, i) ∈ X.wordSegment) w

/-- The slots syllable `s` is linked to directly. -/
def syllableSpan (s : ℕ) : Finset ℕ :=
  X.slots.bipartiteAbove (fun s i ↦ (s, i) ∈ X.syllableSegment) s

/-- The slots mora `m` is linked to. -/
def moraSpan (m : Mora) : Finset ℕ := X.slots.bipartiteAbove (fun m i ↦ (m, i) ∈ X.moraSegment) m

/-- The slots syllable `s` dominates, through its own lines and those of its morae. -/
def yield (s : ℕ) : Finset ℕ := X.syllableSpan s ∪ (X.moraeOf s).biUnion X.moraSpan

/-- The slots word `w` dominates, through its own lines and through its syllables. -/
def wordYield (w : ℕ) : Finset ℕ := X.wordSpan w ∪ (X.syllablesOf w).biUnion X.yield

/-- The weight of a syllable is its number of morae. -/
def weight (s : ℕ) : ℕ := #(X.moraeOf s)

/-- The onset of syllable `s`: the slots it dominates before its nucleus. -/
def onset (s : ℕ) : Finset ℕ := (X.yield s).filter (· < s)

/-- The coda of syllable `s`: the slots it dominates after its nucleus. -/
def coda (s : ℕ) : Finset ℕ := (X.yield s).filter (s < ·)

/-- The morae linked to the segment at slot `i`. -/
def moraeAt (i : ℕ) : Finset Mora := X.morae.bipartiteBelow (fun m i ↦ (m, i) ∈ X.moraSegment) i

/-- The morae no syllable dominates. -/
def free : Finset Mora := X.morae.filter fun m ↦ ∀ s ∈ X.syllables, (s, m) ∉ X.syllableMora

/-- The morae linked to no segment, such as those stranded by deletion. -/
def stranded : Finset Mora := X.morae.filter (X.moraSpan · = ∅)

/-- The number of association lines at slot `i`: the length of its segment in a one-root theory
of length ([hayes-1989]), one for a short segment and two for a long vowel or a geminate. -/
def lineCount (i : ℕ) : ℕ :=
  #(X.words.bipartiteBelow (fun w i ↦ (w, i) ∈ X.wordSegment) i) +
    #(X.syllables.bipartiteBelow (fun s i ↦ (s, i) ∈ X.syllableSegment) i) + #(X.moraeAt i)

variable {X}

@[simp] theorem mem_slots {i : ℕ} : i ∈ X.slots ↔ i < X.melody.length := mem_range

@[simp] theorem mem_syllablesOf {w s : ℕ} :
    s ∈ X.syllablesOf w ↔ s ∈ X.syllables ∧ (w, s) ∈ X.wordSyllable :=
  mem_bipartiteAbove _

@[simp] theorem mem_moraeOf {s : ℕ} {m : Mora} :
    m ∈ X.moraeOf s ↔ m ∈ X.morae ∧ (s, m) ∈ X.syllableMora :=
  mem_bipartiteAbove _

@[simp] theorem mem_wordSpan {w i : ℕ} : i ∈ X.wordSpan w ↔ i ∈ X.slots ∧ (w, i) ∈ X.wordSegment :=
  mem_bipartiteAbove _

@[simp] theorem mem_syllableSpan {s i : ℕ} :
    i ∈ X.syllableSpan s ↔ i ∈ X.slots ∧ (s, i) ∈ X.syllableSegment :=
  mem_bipartiteAbove _

@[simp] theorem mem_moraSpan {m : Mora} {i : ℕ} :
    i ∈ X.moraSpan m ↔ i ∈ X.slots ∧ (m, i) ∈ X.moraSegment :=
  mem_bipartiteAbove _

@[simp] theorem mem_moraeAt {m : Mora} {i : ℕ} :
    m ∈ X.moraeAt i ↔ m ∈ X.morae ∧ (m, i) ∈ X.moraSegment :=
  mem_bipartiteBelow _

theorem mem_yield {s i : ℕ} :
    i ∈ X.yield s ↔ i ∈ X.syllableSpan s ∨ ∃ m ∈ X.moraeOf s, i ∈ X.moraSpan m := by
  simp only [yield, mem_union, mem_biUnion]

theorem mem_wordYield {w i : ℕ} :
    i ∈ X.wordYield w ↔ i ∈ X.wordSpan w ∨ ∃ s ∈ X.syllablesOf w, i ∈ X.yield s := by
  simp only [wordYield, mem_union, mem_biUnion]

theorem weight_eq_zero_iff {s : ℕ} :
    X.weight s = 0 ↔ ∀ m ∈ X.morae, (s, m) ∉ X.syllableMora := by
  simp [weight, Finset.eq_empty_iff_forall_notMem]

theorem head_eq_some {m : Mora} {x : α} :
    X.head m = some x ↔ ∃ h : m.slot < X.melody.length, X.melody[m.slot] = x :=
  List.getElem?_eq_some_iff

/-! ### Forms given by their lines -/

section OfLines

variable {melody : List α} {wordSyllable syllableSegment wordSegment : Finset (ℕ × ℕ)}
  {syllableMora : Finset (ℕ × Mora)} {moraSegment : Finset (Mora × ℕ)}

@[simp] theorem mem_morae_ofLines {m : Mora} :
    m ∈ (ofLines melody wordSyllable syllableMora wordSegment syllableSegment moraSegment).morae ↔
      (∃ s, (s, m) ∈ syllableMora) ∨ ∃ i, (m, i) ∈ moraSegment := by
  simp [ofLines]

@[simp] theorem mem_syllables_ofLines {s : ℕ} :
    s ∈ (ofLines melody wordSyllable syllableMora wordSegment syllableSegment
      moraSegment).syllables ↔
      (∃ w, (w, s) ∈ wordSyllable) ∨ (∃ m, (s, m) ∈ syllableMora) ∨
        ∃ i, (s, i) ∈ syllableSegment := by
  simp [ofLines]

@[simp] theorem mem_words_ofLines {w : ℕ} :
    w ∈ (ofLines melody wordSyllable syllableMora wordSegment syllableSegment moraSegment).words ↔
      (∃ s, (w, s) ∈ wordSyllable) ∨ ∃ i, (w, i) ∈ wordSegment := by
  simp [ofLines]

end OfLines

/-! ### Well-formedness and crossing -/

variable (X)

/-- Lines join nodes and slots that are present, and every node stands at a slot. -/
@[mk_iff]
structure WellFormed : Prop where
  words_subset : X.words ⊆ X.slots
  syllables_subset : X.syllables ⊆ X.slots
  slot_mem : ∀ m ∈ X.morae, m.slot ∈ X.slots
  wordSyllable_mem : ∀ p ∈ X.wordSyllable, p.1 ∈ X.words ∧ p.2 ∈ X.syllables
  syllableMora_mem : ∀ p ∈ X.syllableMora, p.1 ∈ X.syllables ∧ p.2 ∈ X.morae
  wordSegment_mem : ∀ p ∈ X.wordSegment, p.1 ∈ X.words ∧ p.2 ∈ X.slots
  syllableSegment_mem : ∀ p ∈ X.syllableSegment, p.1 ∈ X.syllables ∧ p.2 ∈ X.slots
  moraSegment_mem : ∀ p ∈ X.moraSegment, p.1 ∈ X.morae ∧ p.2 ∈ X.slots

instance : Decidable X.WellFormed := decidable_of_iff _ (wellFormed_iff X).symm

/-- The association lines, each as the slot of its node and the slot of its segment. -/
def lines : Finset (ℕ × ℕ) :=
  X.wordSegment ∪ X.syllableSegment ∪ X.moraSegment.image (Prod.map Mora.slot id)

/-- The No-Crossing Constraint: no two association lines cross on the timeline of the melody,
nor do two lines of domination between the same two tiers. -/
@[mk_iff]
structure NoCrossing : Prop where
  isNonCrossing_lines : IsNonCrossing (X.lines : SetRel ℕ ℕ)
  isNonCrossing_wordSyllable : IsNonCrossing (X.wordSyllable : SetRel ℕ ℕ)
  isNonCrossing_syllableMora :
    IsNonCrossing ((X.syllableMora.image (Prod.map id Mora.slot) : Finset (ℕ × ℕ)) : SetRel ℕ ℕ)

instance : Decidable X.NoCrossing := decidable_of_iff _ (noCrossing_iff X).symm

variable {X} in
theorem mem_lines {p : ℕ × ℕ} : p ∈ X.lines ↔ p ∈ X.wordSegment ∨ p ∈ X.syllableSegment ∨
    ∃ m : Mora, m.slot = p.1 ∧ (m, p.2) ∈ X.moraSegment := by
  obtain ⟨a, b⟩ := p
  simp only [lines, mem_union, mem_image, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
  constructor
  · rintro ((h | h) | ⟨m, i, h, rfl, rfl⟩)
    exacts [.inl h, .inr (.inl h), .inr (.inr ⟨m, rfl, h⟩)]
  · rintro (h | h | ⟨m, rfl, h⟩)
    exacts [.inl (.inl h), .inl (.inr h), .inr ⟨m, b, h, rfl, rfl⟩]

/-! ### Erasing and drawing lines -/

/-- Deletion on the segmental tier alone erases every line to slot `i` and keeps the nodes and
the melody, so that a mora that dominated `i` alone is stranded. -/
def delete (i : ℕ) : MoraicForm α :=
  { X with wordSegment := X.wordSegment.filter (·.2 ≠ i),
           syllableSegment := X.syllableSegment.filter (·.2 ≠ i),
           moraSegment := X.moraSegment.filter (·.2 ≠ i) }

/-- `linkMora m i` draws a line from mora `m` to slot `i`. -/
def linkMora (m : Mora) (i : ℕ) : MoraicForm α :=
  { X with moraSegment := insert (m, i) X.moraSegment }

/-- `delinkMora m i` erases the line from mora `m` to slot `i`. -/
def delinkMora (m : Mora) (i : ℕ) : MoraicForm α :=
  { X with moraSegment := X.moraSegment.erase (m, i) }

/-- `linkSyllable s i` draws a line from syllable `s` to slot `i`. -/
def linkSyllable (s i : ℕ) : MoraicForm α :=
  { X with syllableSegment := insert (s, i) X.syllableSegment }

variable (i : ℕ) (m : Mora) (s : ℕ)

@[simp] theorem morae_delete : (X.delete i).morae = X.morae := rfl
@[simp] theorem morae_linkMora : (X.linkMora m i).morae = X.morae := rfl
@[simp] theorem morae_delinkMora : (X.delinkMora m i).morae = X.morae := rfl
@[simp] theorem morae_linkSyllable : (X.linkSyllable s i).morae = X.morae := rfl

theorem moraSpan_delete : (X.delete i).moraSpan m = (X.moraSpan m).erase i := by
  ext j
  simp only [mem_moraSpan, delete, mem_slots, mem_filter, mem_erase]
  tauto

theorem stranded_delete :
    (X.delete i).stranded = X.stranded ∪ X.morae.filter (X.moraSpan · = {i}) := by
  ext n
  simp only [stranded, moraSpan_delete, morae_delete, mem_union, mem_filter,
    erase_eq_empty_iff]
  tauto

theorem lines_delete : (X.delete i).lines = X.lines.filter (·.2 ≠ i) := by
  ext ⟨a, b⟩
  simp only [mem_lines, delete, mem_filter]
  constructor
  · rintro (⟨h, hb⟩ | ⟨h, hb⟩ | ⟨m, rfl, h, hb⟩)
    exacts [⟨.inl h, hb⟩, ⟨.inr (.inl h), hb⟩, ⟨.inr (.inr ⟨m, rfl, h⟩), hb⟩]
  · rintro ⟨h | h | ⟨m, rfl, h⟩, hb⟩
    exacts [.inl ⟨h, hb⟩, .inr (.inl ⟨h, hb⟩), .inr (.inr ⟨m, rfl, h, hb⟩)]

theorem lines_linkMora : (X.linkMora m i).lines = insert (m.slot, i) X.lines := by
  simp only [lines, linkMora, image_insert, Prod.map_apply, id_eq, union_insert]

theorem lines_linkSyllable : (X.linkSyllable s i).lines = insert (s, i) X.lines := by
  simp only [lines, linkSyllable, union_insert, insert_union]

theorem lines_delinkMora_subset : (X.delinkMora m i).lines ⊆ X.lines :=
  union_subset_union subset_rfl (image_subset_image (erase_subset _ _))

variable {X i m s}

theorem NoCrossing.delete (h : X.NoCrossing) (i : ℕ) : (X.delete i).NoCrossing :=
  ⟨h.1.subset (by rw [lines_delete]; exact coe_subset.2 (filter_subset _ _)), h.2, h.3⟩

theorem NoCrossing.delinkMora (h : X.NoCrossing) (m : Mora) (i : ℕ) :
    (X.delinkMora m i).NoCrossing :=
  ⟨h.1.subset (coe_subset.2 (lines_delinkMora_subset X i m)), h.2, h.3⟩

theorem noCrossing_linkMora_iff :
    (X.linkMora m i).NoCrossing ↔ X.NoCrossing ∧ i ∈ window (X.lines : SetRel ℕ ℕ) m.slot := by
  simp only [noCrossing_iff, lines_linkMora, coe_insert, isNonCrossing_insert_iff_mem_window]
  exact ⟨fun ⟨⟨h₁, hw⟩, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂, h₃⟩, hw⟩, fun ⟨⟨h₁, h₂, h₃⟩, hw⟩ ↦ ⟨⟨h₁, hw⟩, h₂, h₃⟩⟩

theorem noCrossing_linkSyllable_iff :
    (X.linkSyllable s i).NoCrossing ↔ X.NoCrossing ∧ i ∈ window (X.lines : SetRel ℕ ℕ) s := by
  simp only [noCrossing_iff, lines_linkSyllable, coe_insert, isNonCrossing_insert_iff_mem_window]
  exact ⟨fun ⟨⟨h₁, hw⟩, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂, h₃⟩, hw⟩, fun ⟨⟨h₁, h₂, h₃⟩, hw⟩ ↦ ⟨⟨h₁, hw⟩, h₂, h₃⟩⟩

end MoraicForm

end Prosody
