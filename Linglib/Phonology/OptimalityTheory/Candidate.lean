/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Mora
public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.Prosody.Grid
public import Linglib.Phonology.OptimalityTheory.Correspondence.Coindexation

/-!
# Candidates

A candidate pairs an input with an output, each a *parse*: a moraic form over its own string
([hayes-1989]), prosodic structure above the syllable as trees whose syllable leaves name the
form's syllables, and a metrical grid giving each syllable its stress. The two strings correspond
by a `Coindexation`, and the morae correspond independently of their segments
([broselow-chen-huffman-1997]). The input is parsed like the output, so faithfulness compares
prosody with prosody: identity of corresponding slots under any reading of a parse is the one
counter [`Candidate.identViol`](##OptimalityTheory.Candidate.identViol), read at the morae of a
slot for length, and
[MAX-μ](##OptimalityTheory.Candidate.maxMoraViol) and
[DEP-μ](##OptimalityTheory.Candidate.depMoraViol) count the morae left without correspondents.

## Implementation notes

* A parse adds to the moraic form only what lies above the syllable: the trees' syllable leaves
  are marked with the form's syllable names, and the grid lists the stress of each syllable in
  nucleus order. Words appear both as the form's word tier and as `.om` nodes of a tree; a study
  uses one of the two.
* The input and output strings live in the coindexation, and each parse's melody repeats its
  side's string; a study's constructor builds the parses over `io.string`, as
  `Candidate.ofIO` does.
* The mora correspondence is a field of its own, and `Candidate.orderMoraCorr` pairs the morae
  in order, for candidates printed without one.
* Segmental faithfulness is read off `io` by the `Coindexation` counters; this file adds only
  the counters that need a parse or the mora correspondence.

## TODO

* With morae corresponding in order, MAX-μ is the surplus of input morae over output morae and
  DEP-μ the surplus of output morae; neither is proved.

## References

* [prince-smolensky-1993]
* [hayes-1989]
* [mccarthy-prince-1995]
* [broselow-chen-huffman-1997]
-/

@[expose] public section

namespace OptimalityTheory

open Prosody Finset

/-- A parse: a moraic form, prosodic structure above the syllable as trees whose syllable
leaves name the form's syllables, and a metrical grid over the syllables in nucleus order. -/
structure Parse (α : Type*) where
  /-- The moraic form, up to the syllable. -/
  form : MoraicForm α := {}
  /-- The prosodic structure above the syllable. -/
  above : List (RoseTree (Constituent Level ℕ)) := []
  /-- The stress of each syllable, in nucleus order. -/
  grid : Grid := []

namespace Parse

variable {α : Type*} (P : Parse α)

/-- The syllables in nucleus order. -/
def syllableList : List ℕ := (List.range P.form.melody.length).filter (· ∈ P.form.syllables)

/-- The stress of the syllable named `s`, its column of the grid. -/
def stress (s : ℕ) : ℕ := P.grid.getD (P.syllableList.idxOf s) 0

/-- The stress at a slot: the greatest stress of a syllable that contains it, and `0` for a slot
in no syllable. -/
def stressAt (i : ℕ) : ℕ := (P.form.syllables.filter (i ∈ P.form.yield ·)).sup P.stress

/-- The number of morae at a slot. -/
def weightAt (i : ℕ) : ℕ := #(P.form.moraeAt i)

/-- The feet of the structure above the syllable, each the names of its syllables. -/
def feet : List (List ℕ) := P.above.flatMap Prosody.feet

/-- FT-BIN(μ), minimal binarity: a violation for each foot whose syllables carry fewer than two
morae together, a degenerate foot. A foot of more than two morae is the business of a separate
constraint on maximal binarity. -/
def ftBinViol : ℕ := P.feet.countP fun f ↦ (f.map P.form.weight).sum < 2

/-- ONSET: a violation for each syllable without an onset. -/
def onsetViol : ℕ := #(P.form.syllables.filter fun s ↦ P.form.onset s = ∅)

theorem onsetViol_eq_zero_iff :
    P.onsetViol = 0 ↔ ∀ s ∈ P.form.syllables, (P.form.onset s).Nonempty := by
  simp [onsetViol, Finset.filter_eq_empty_iff, Finset.nonempty_iff_ne_empty]

/-- NOSHAREDMORA ([broselow-chen-huffman-1997]): a violation for each mora linked to more than
one segment. -/
def noSharedMoraViol : ℕ := #(P.form.morae.filter fun m ↦ 1 < #(P.form.moraSpan m))

theorem noSharedMoraViol_eq_zero_iff :
    P.noSharedMoraViol = 0 ↔ ∀ m ∈ P.form.morae, #(P.form.moraSpan m) ≤ 1 := by
  simp [noSharedMoraViol, Finset.filter_eq_empty_iff]

/-- *COMPLEXCODA: a violation for each syllable with more than one coda segment. -/
def complexCodaViol : ℕ := #(P.form.syllables.filter fun s ↦ 2 ≤ #(P.form.coda s))

end Parse

/-- An input–output candidate: the correspondence of the two strings, a parse of each, and an
independent correspondence of their morae. -/
structure Candidate (α : Type*) where
  /-- The input–output correspondence of the segments. -/
  io : Correspondence.Coindexation BinaryRole α
  /-- The parse of the input. -/
  input : Parse α := {}
  /-- The parse of the output. -/
  output : Parse α := {}
  /-- The correspondence of the morae, independent of their segments. -/
  moraCorr : Finset (Mora × Mora) := ∅

namespace Candidate

variable {α : Type*} (c : Candidate α)

/-- The candidate of a correspondence whose input is the bare input string and whose output
form, over the output string, has the given lines. -/
def ofIO (io : Correspondence.Coindexation BinaryRole α)
    (wordSyllable : Finset (ℕ × ℕ) := ∅) (syllableMora : Finset (ℕ × Mora) := ∅)
    (wordSegment : Finset (ℕ × ℕ) := ∅) (syllableSegment : Finset (ℕ × ℕ) := ∅)
    (moraSegment : Finset (Mora × ℕ) := ∅) : Candidate α :=
  { io := io
    input := { form := { melody := io.string .lhs } }
    output := { form := (MoraicForm.ofLines (io.string .rhs) wordSyllable syllableMora
      wordSegment syllableSegment moraSegment) } }

/-- The corresponding slot pairs: an input position and an output position that share an index
of the coindexation. -/
def pairs : List (ℕ × ℕ) :=
  (c.io.form .lhs).zipIdx.flatMap fun x ↦ (c.io.form .rhs).zipIdx.filterMap fun y ↦
    if ∃ k ∈ x.1.2 .rhs, k ∈ y.1.2 .lhs then some (x.2, y.2) else none

/-- The correspondence of morae in order: the `k`-th mora of the input, by head and then by
index, with the `k`-th mora of the output. A mora survives a change of head, as in compensatory
lengthening, and the surplus of either side has no correspondent. -/
def orderMoraCorr : Finset (Mora × Mora) :=
  (c.input.form.moraList.zip c.output.form.moraList).toFinset

/-- The candidate with its morae corresponding in order. -/
def withOrderMoraCorr : Candidate α := { c with moraCorr := c.orderMoraCorr }

@[simp] theorem withOrderMoraCorr_io : c.withOrderMoraCorr.io = c.io := rfl

@[simp] theorem withOrderMoraCorr_input : c.withOrderMoraCorr.input = c.input := rfl

@[simp] theorem withOrderMoraCorr_output : c.withOrderMoraCorr.output = c.output := rfl

@[simp] theorem withOrderMoraCorr_moraCorr : c.withOrderMoraCorr.moraCorr = c.orderMoraCorr := rfl

/-- IDENT under a reading `g` of a parse at a slot: a violation for each corresponding pair
whose readings are both specified and differ. Reading a feature of the melody is
[mccarthy-prince-1995]'s IDENT(F), and reading `Parse.weightAt` is identity of length. -/
def identViol {β : Type*} [DecidableEq β] (g : Parse α → ℕ → Option β) : ℕ :=
  c.pairs.countP fun p ↦ ∃ a ∈ g c.input p.1, ∃ b ∈ g c.output p.2, a ≠ b

/-- A reading on which every corresponding pair agrees is not violated. -/
theorem identViol_eq_zero {β : Type*} [DecidableEq β] {g : Parse α → ℕ → Option β}
    (h : ∀ p ∈ c.pairs, g c.input p.1 = g c.output p.2) : c.identViol g = 0 := by
  refine List.countP_eq_zero.2 fun p hp ↦ ?_
  simp only [decide_eq_true_eq]
  rintro ⟨a, ha, b, hb, hab⟩
  rw [h p hp] at ha
  exact hab (Option.some.inj ((Option.mem_def.1 ha).symm.trans (Option.mem_def.1 hb)))

/-- MAX-μ: a violation for each mora of the input without a correspondent. -/
def maxMoraViol : ℕ :=
  #(c.input.form.morae.filter fun m ↦ ∀ m' ∈ c.output.form.morae, (m, m') ∉ c.moraCorr)

/-- DEP-μ: a violation for each mora of the output without a correspondent. -/
def depMoraViol : ℕ :=
  #(c.output.form.morae.filter fun m' ↦ ∀ m ∈ c.input.form.morae, (m, m') ∉ c.moraCorr)

theorem maxMoraViol_eq_zero_iff :
    c.maxMoraViol = 0 ↔
      ∀ m ∈ c.input.form.morae, ∃ m' ∈ c.output.form.morae, (m, m') ∈ c.moraCorr := by
  simp [maxMoraViol, Finset.filter_eq_empty_iff]

theorem depMoraViol_eq_zero_iff :
    c.depMoraViol = 0 ↔
      ∀ m' ∈ c.output.form.morae, ∃ m ∈ c.input.form.morae, (m, m') ∈ c.moraCorr := by
  simp [depMoraViol, Finset.filter_eq_empty_iff]

theorem maxMoraViol_le : c.maxMoraViol ≤ #c.input.form.morae := Finset.card_filter_le _ _

theorem depMoraViol_le : c.depMoraViol ≤ #c.output.form.morae := Finset.card_filter_le _ _

end Candidate

end OptimalityTheory
