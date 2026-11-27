/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Root.Consonantal
public import Linglib.Phonology.Autosegmental.KripkeModel.Collapse
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

`AR.NoManyToOne` holds exactly when two lines to one slot are the same line
(`noManyToOne_iff`), and each token then has at most one line to each plane
(`NoManyToOne.isFunctional`). Under it a slot realizes the segment of the autosegment it bears
(`segmentAt_eq_some_iff`), so collapsing a plane, which merges adjacent identical melodic
elements and changes the labels no slot bears, changes no surface segment (`spellout_collapse`).

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

section LinesAt

variable {f} {s q : ℕ} {i : ι}

theorem mem_linesAt : (i, q) ∈ f.linesAt s ↔ f.Link (some i) none q s := by
  simp only [linesAt, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and,
    Multiset.mem_map, Finset.mem_filter, Prod.mk.injEq, Prod.exists, Link]
  exact ⟨fun ⟨_, a, b, ⟨h, hb⟩, hi, ha⟩ ↦ by subst hi ha hb; exact h,
    fun h ↦ ⟨i, q, s, ⟨h, rfl⟩, rfl, rfl⟩⟩

theorem nodup_linesAt (s : ℕ) : (f.linesAt s).Nodup := by
  refine Multiset.nodup_bind.2 ⟨fun i _ ↦ Multiset.Nodup.map_on ?_ (Finset.nodup _),
    (Finset.nodup _).pairwise fun i _ i' _ hne ↦ Multiset.disjoint_left.2 fun {x} hx hx' ↦ ?_⟩
  · intro l hl l' hl' h
    have h₁ := (Finset.mem_filter.1 hl).2
    have h₂ := (Finset.mem_filter.1 hl').2
    exact Prod.ext (Prod.mk.inj h).2 (h₁.trans h₂.symm)
  · obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨l', -, h⟩ := Multiset.mem_map.1 hx'
    exact hne (Prod.mk.inj h).1.symm

/-- No slot has two lines exactly when two lines to one slot are the same line. -/
theorem noManyToOne_iff : f.NoManyToOne ↔ ∀ ⦃i i' : ι⦄ ⦃q q' s : ℕ⦄,
    f.Link (some i) none q s → f.Link (some i') none q' s → i = i' ∧ q = q' := by
  have key (s : ℕ) : Multiset.card (f.linesAt s) ≤ 1 ↔
      ∀ a ∈ f.linesAt s, ∀ b ∈ f.linesAt s, a = b :=
    Finset.card_le_one (s := ⟨f.linesAt s, nodup_linesAt s⟩)
  constructor
  · intro h i i' q q' s hl hl'
    exact Prod.mk.inj ((key s).1 (h s hl.lt_right) _ (mem_linesAt.2 hl) _ (mem_linesAt.2 hl'))
  · intro h s _
    refine (key s).2 fun ⟨i, q⟩ ha ⟨i', q'⟩ hb ↦ ?_
    obtain ⟨rfl, rfl⟩ := h (mem_linesAt.1 ha) (mem_linesAt.1 hb)
    rfl

/-- With no slot bearing two lines, each token has at most one line to each plane. -/
theorem NoManyToOne.isFunctional (h : f.NoManyToOne) : f.IsFunctional planes := by
  rintro (_ | i) p q q' hj hl hl'
  · exact absurd rfl hj
  · exact (noManyToOne_iff.1 h hl.symm hl'.symm).2

end LinesAt

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

section Melody

variable {f} {s : ℕ}

theorem linkAt?_eq_some_iff {e : ι × ℕ} : f.linkAt? s = some e ↔ f.linesAt s = {e} := by
  unfold linkAt?
  induction f.linesAt s using Quot.inductionOn with
  | h l =>
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exact iff_of_false nofun fun h ↦ by simpa using congrArg Multiset.card h
    · exact ⟨fun h ↦ by rw [← Option.some.inj h]; rfl, fun h ↦ congrArg some
        (Multiset.singleton_inj.1 h)⟩
    · exact iff_of_false nofun fun h ↦ by simpa using congrArg Multiset.card h

/-- With no slot bearing two lines, a slot realizes the segment of the autosegment it bears. -/
theorem segmentAt_eq_some_iff [DecidableEq ι] (h : f.NoManyToOne) {x : α} :
    f.segmentAt s = some x ↔ ∃ i a, a ∈ f.melody planes s (some i) ∧ a.value = x := by
  simp only [mem_melody_planes_iff]
  constructor
  · intro hx
    obtain ⟨⟨i, q⟩, he, hv⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hv
    have hl : f.Link (some i) none q s :=
      mem_linesAt.1 (by rw [linkAt?_eq_some_iff.1 he]; exact Multiset.mem_singleton_self _)
    exact ⟨i, a, ⟨q, hl, ha⟩, rfl⟩
  · rintro ⟨i, a, ⟨q, hl', ha⟩, rfl⟩
    have he : f.linkAt? s = some (i, q) := by
      rw [linkAt?_eq_some_iff]
      refine (Multiset.Nodup.ext (nodup_linesAt s) (Multiset.nodup_singleton _)).2 fun ⟨i', q'⟩ ↦ ?_
      rw [Multiset.mem_singleton, mem_linesAt]
      exact ⟨fun h' ↦ by obtain ⟨rfl, rfl⟩ := noManyToOne_iff.1 h h' hl'; rfl,
        fun h' ↦ by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'; exact hl'⟩
    simp only [segmentAt, he, Option.bind_some, Option.map_eq_some_iff]
    exact ⟨a, ha, rfl⟩

section Collapse

open OCP

variable [DecidableEq ι] [DecidableEq α] [DecidableEq M]

/-- Collapsing a plane gives no slot a second line. -/
theorem NoManyToOne.collapse (h : f.NoManyToOne) (i : ι) : (f.collapse (some i)).NoManyToOne := by
  rw [noManyToOne_iff] at h ⊢
  intro j j' q q' s hl hl'
  obtain ⟨p, t, hp, rfl, ht⟩ := link_collapse.1 hl
  obtain ⟨p', t', hp', rfl, ht'⟩ := link_collapse.1 hl'
  rw [repointIdx_of_ne (Option.some_ne_none i).symm] at ht ht'
  obtain rfl := ht
  obtain rfl := ht'
  obtain ⟨rfl, rfl⟩ := h hp hp'
  exact ⟨rfl, rfl⟩

theorem segmentAt_collapse (h : f.NoManyToOne) (i : ι) (s : ℕ) :
    (f.collapse (some i)).segmentAt s = f.segmentAt s :=
  Option.ext fun x ↦ by
    rw [segmentAt_eq_some_iff (h.collapse i), segmentAt_eq_some_iff h]
    exact exists_congr fun j ↦ exists_congr fun a ↦ and_congr_left fun _ ↦
      mem_melody_collapse_iff (fun _ _ ↦ (Option.some_ne_none i).symm) (Option.some_ne_none i)

/-- Collapsing a plane changes no surface segment. -/
theorem spellout_collapse (h : f.NoManyToOne) (i : ι) :
    (f.collapse (some i)).spellout = f.spellout := by
  rw [spellout, spellout, word_collapse_of_ne _ _ (Option.some_ne_none i).symm,
    funext (segmentAt_collapse h i)]

end Collapse

end Melody

end Autosegmental.AR
