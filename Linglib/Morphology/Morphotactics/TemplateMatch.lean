/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Root.Consonantal
public import Linglib.Phonology.Autosegmental.Multiplanar
public import Linglib.Phonology.Autosegmental.Skeleton

/-!
# Template matches

In the prosodic morphology of [mccarthy-1981], a word is the melodies of its morphemes, a
consonantal root, a vocalism and affixal material, associated with the slots of a CV skeleton.
A match is a multiplanar form over C- and V-slots in which each morpheme's melody lies on its
own plane.

We define `AR.template`, the skeleton of a match, `AR.linesAt` and `AR.linkAt?`, the lines that
reach a slot and the melodic element linked to it, and `AR.spellout`, the surface segments: a
melodic element linked to several slots is geminate, and a slot that no line reaches has no
segment. `AR.NoManyToOne` says that no slot has two lines. Relabelling the melodies relabels the
surface segments (`AR.spellout_mapMelody`).

The conventions that draw the lines are in `Morphology/Morphotactics/Association.lean`.

## References

* [mccarthy-1981]
* [mccarthy-1989]
* [goldsmith-1976]
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {α β M : Type} (f : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)))

/-- The CV skeleton of a match, its slots without their sponsors. -/
def template : Skeleton := (f.word none).map Sponsored.value

@[simp] theorem length_template : f.template.length = (f.word none).length := List.length_map _

@[simp] theorem template_mapMelody (φ : α → β) : (f.mapMelody φ).template = f.template := rfl

/-- The slots of class `b`, which bear the melody of a tier that takes them ([mccarthy-1981],
p. 383). -/
def bearers (b : Slot) : List ℕ := f.template.idxsOf b

@[simp] theorem bearers_mapMelody (φ : α → β) (b : Slot) :
    (f.mapMelody φ).bearers b = f.bearers b := rfl

/-- The number of lines from element `k` of plane `i`; a geminate is an element with two. -/
def linkCount (i : ι) (k : ℕ) : ℕ := (((f.lines (some i) none)).filter (·.1 = k)).card

@[simp] theorem linkCount_mapMelody (φ : α → β) (i : ι) (k : ℕ) :
    (f.mapMelody φ).linkCount i k = f.linkCount i k := rfl

/-- Slot `s` is filled when a line from some plane reaches it. -/
def IsFilled (s : ℕ) : Prop := ∃ i, ∃ l ∈ (f.lines (some i) none), l.2 = s

variable [Fintype ι]

instance (s : ℕ) : Decidable (f.IsFilled s) := inferInstanceAs (Decidable (∃ _, _))

/-- The free slots of class `b`, left to right. A slot with a line from any plane is
unavailable. -/
def freeBearers (b : Slot) : List ℕ := (f.bearers b).filter (¬ f.IsFilled ·)

@[simp] theorem freeBearers_mapMelody (φ : α → β) (b : Slot) :
    (f.mapMelody φ).freeBearers b = f.freeBearers b := rfl

/-- The lines that reach slot `s`, each as its plane and the position on that plane. -/
def linesAt (s : ℕ) : Multiset (ι × ℕ) :=
  Finset.univ.val.bind fun i ↦ (((f.lines (some i) none)).filter (·.2 = s)).val.map fun l ↦ (i, l.1)

@[simp] theorem linesAt_mapMelody (φ : α → β) (s : ℕ) : (f.mapMelody φ).linesAt s = f.linesAt s :=
  rfl

/-- `f.NoManyToOne` says that no slot has two lines: [mccarthy-1981]'s prohibition against
many-to-one associations, which "no segment receive multiple associations" generalizes across
tiers (p. 383). -/
def NoManyToOne : Prop := ∀ s < (f.word none).length, Multiset.card (f.linesAt s) ≤ 1

instance : Decidable f.NoManyToOne := inferInstanceAs (Decidable (∀ _ < _, _))

/-- The melodic element linked to slot `s`, as its plane and position, when one line reaches the
slot: association read as a partial function from the slots. -/
def linkAt? (s : ℕ) : Option (ι × ℕ) :=
  Quot.liftOn (f.linesAt s) (fun | [a] => some a | _ => none) fun l l' h ↦ by
    have h : l.Perm l' := h
    have hl := h.length_eq
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rcases l' with _ | ⟨a', _ | ⟨b', l'⟩⟩ <;> simp_all

@[simp] theorem linkAt?_map (φ : α → β) (s : ℕ) : (f.mapMelody φ).linkAt? s = f.linkAt? s := rfl

/-- The segment slot `s` realizes, that of the melodic element linked to it. -/
def segmentAt (s : ℕ) : Option α :=
  (f.linkAt? s).bind fun e ↦ ((f.word (some e.1)))[e.2]?.map Sponsored.value

/-- The surface segments of the match. A slot realizes the melodic element linked to it, and a
slot with no association line receives no phonetic realization ([mccarthy-1981]). -/
def spellout : List α := (List.range (f.word none).length).filterMap f.segmentAt

theorem segmentAt_mapMelody (φ : α → β) (s : ℕ) :
    (f.mapMelody φ).segmentAt s = (f.segmentAt s).map φ := by
  simp only [segmentAt, linkAt?_map, Option.map_bind]
  congr 1
  funext e
  simp [Option.map_map, Function.comp_def]

/-- Relabeling the melodies relabels the surface segments. -/
theorem spellout_mapMelody (φ : α → β) : (f.mapMelody φ).spellout = f.spellout.map φ := by
  simp only [spellout, word_mapMelody_none, List.map_filterMap, segmentAt_mapMelody]

end Autosegmental.AR
