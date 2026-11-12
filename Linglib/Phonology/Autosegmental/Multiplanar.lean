/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Linglib.Phonology.Autosegmental.Morph

/-!
# Multiplanar representations

A multiplanar representation is a tier of slots shared by several planes, each plane a tier of
autosegments associated to the slots: McCarthy's morphemic tiers, each a melody on its own plane
around one prosodic skeleton. It is a representation whose tiers are the slots and the planes,
with every line running from a plane to the slots, and `AR.ofPlanes` writes one down from its
slots, the word of each plane and the lines of each plane;
[every such representation arises so](##Autosegmental.AR.ofPlanes_eta). Autosegments on different
planes stand in no order, so the No-Crossing Constraint
[holds plane by plane](##Autosegmental.AR.noCrossing_iff_planes), and morphs on separate planes
commute (`AR.commute_of_disjoint_support`).

## Implementation notes

The operations that edit lines or slots (`AR.addLines`, `AR.filterLines`, `AR.eraseSlot`) rebuild
the representation with `AR.ofPlanes`, so their result has lines from planes to slots only. A
line between two planes, which no multiplanar representation has, is not carried over.

## References

* [mccarthy-1981]
* [mccarthy-1989]
-/

@[expose] public section

namespace Autosegmental

universe u

/-- The alphabets of a multiplanar representation: autosegments in `α` on the tier `some i` of
each plane `i`, and slots in `β` on the tier `none` that the planes share. -/
abbrev Multiplanar (ι : Type*) (α β : Type u) : Option ι → Type u :=
  fun j ↦ j.elim β fun _ ↦ α

instance {ι : Type*} {α β : Type u} [DecidableEq α] [DecidableEq β] :
    ∀ j, DecidableEq (Multiplanar ι α β j)
  | none => inferInstanceAs (DecidableEq β)
  | some _ => inferInstanceAs (DecidableEq α)

namespace AR

variable {ι : Type*} {α β : Type u}

/-! ### Representations from slots and planes -/

section OfPlanes

variable (lo : List β) (up : ι → List α) (L : ι → Finset (ℕ × ℕ))

/-- `ofPlanes lo up L` has the slots `lo`, the autosegments `up i` on plane `i`, and on each plane
a line for each pair in `L i` of a position of the plane and a position of the slots. -/
def ofPlanes : AR (Multiplanar ι α β) where
  word
    | none => lo
    | some i => up i
  lines
    | some i, none => (L i).filter fun x ↦ x.1 < (up i).length ∧ x.2 < lo.length
    | none, some i => ((L i).filter fun x ↦ x.1 < (up i).length ∧ x.2 < lo.length).map
        (Equiv.prodComm ℕ ℕ).toEmbedding
    | _, _ => ∅
  lines_self j := by cases j <;> rfl
  swap_mem_lines i j p q h := by cases i <;> cases j <;> simp_all
  fst_lt_of_mem_lines i j p q h := by rcases i with _ | i <;> rcases j with _ | j <;> simp_all

@[simp] theorem word_ofPlanes_none : (ofPlanes lo up L).word none = lo := rfl

@[simp] theorem word_ofPlanes_some (i : ι) : (ofPlanes lo up L).word (some i) = up i := rfl

/-- The lines of `ofPlanes` on a plane are the given pairs within range. -/
@[simp] theorem lines_ofPlanes (i : ι) : (ofPlanes lo up L).lines (some i) none =
    (L i).filter fun x ↦ x.1 < (up i).length ∧ x.2 < lo.length := rfl

@[simp] theorem lines_ofPlanes_some_some (i i' : ι) :
    (ofPlanes lo up L).lines (some i) (some i') = ∅ := rfl

/-- A representation whose planes are not linked to one another is `ofPlanes` of its slots, its
planes and their lines. -/
theorem ofPlanes_eta (X : AR (Multiplanar ι α β)) (h : ∀ i i', X.lines (some i) (some i') = ∅) :
    ofPlanes (X.word none) (fun i ↦ X.word (some i)) (fun i ↦ X.lines (some i) none) = X := by
  have key (i : ι) (p q : ℕ) : (ofPlanes (X.word none) (fun i ↦ X.word (some i))
      fun i ↦ X.lines (some i) none).Link (some i) none p q ↔ X.Link (some i) none p q :=
    Finset.mem_filter.trans ⟨fun h ↦ h.1, fun h ↦ ⟨h, Link.lt_left h, Link.lt_right h⟩⟩
  refine ext (funext fun j ↦ by cases j <;> rfl) fun i j p q ↦ ?_
  rcases i with _ | i <;> rcases j with _ | j
  · exact iff_of_false (fun h ↦ h.ne rfl) fun h ↦ h.ne rfl
  · exact link_comm.trans ((key j q p).trans link_comm)
  · exact key i p q
  · exact iff_of_false (Finset.notMem_empty _) fun h' ↦ by simp [Link, h i j] at h'

end OfPlanes

variable (X : AR (Multiplanar ι α β))

/-- With no line between two planes, the No-Crossing Constraint holds plane by plane. -/
theorem noCrossing_iff_planes (h : ∀ i i', X.lines (some i) (some i') = ∅) :
    X.NoCrossing ↔ ∀ i, IsNonCrossing (X.lines (some i) none : SetRel ℕ ℕ) := by
  refine ⟨fun hX i ↦ hX _ _, fun hX j k ↦ ?_⟩
  rcases j with _ | i <;> rcases k with _ | i'
  · exact isNonCrossing_lines_self none
  · exact isNonCrossing_lines_comm.1 (hX i')
  · exact hX i
  · simp [h i i']

theorem lines_eq_empty_of_word {i : ι} (h : X.word (some i) = []) :
    X.lines (some i) none = ∅ :=
  Finset.eq_empty_of_forall_notMem fun ⟨p, q⟩ hp ↦ by
    simpa [h] using Link.lt_left (X := X) hp

/-- `X.hostedOn i s` lists, in tier order, the autosegments of plane `i` linked to slot `s`. -/
def hostedOn (i : ι) (s : ℕ) : List α :=
  ((X.word (some i)).zipIdx.filter fun x ↦ (x.2, s) ∈ X.lines (some i) none).map Prod.fst

/-- `X.eraseSlot k` deletes slot `k` with every line it bears, moving the lines of the later
slots one position left. -/
def eraseSlot (k : ℕ) : AR (Multiplanar ι α β) :=
  ofPlanes ((X.word none).eraseIdx k) (fun i ↦ X.word (some i)) fun i ↦
    ((X.lines (some i) none).filter (·.2 ≠ k)).image fun l ↦ if k < l.2 then (l.1, l.2 - 1) else l

@[simp] theorem word_eraseSlot_some (k : ℕ) (i : ι) :
    (X.eraseSlot k).word (some i) = X.word (some i) := rfl

@[simp] theorem word_eraseSlot_none (k : ℕ) :
    (X.eraseSlot k).word none = (X.word none).eraseIdx k := rfl

/-! ### Lines on a plane -/

section Lines

variable [DecidableEq ι] (i : ι)

/-- `X.addLines i L` adds to plane `i` the lines of `L` that are in range, as
`SimpleGraph.fromEdgeSet` drops loops. -/
def addLines (L : Finset (ℕ × ℕ)) : AR (Multiplanar ι α β) :=
  ofPlanes (X.word none) (fun j ↦ X.word (some j)) fun j ↦
    if j = i then X.lines (some j) none ∪ L else X.lines (some j) none

/-- `X.filterLines i P` keeps the lines of plane `i` that satisfy `P`. -/
def filterLines (P : ℕ × ℕ → Prop) [DecidablePred P] : AR (Multiplanar ι α β) :=
  ofPlanes (X.word none) (fun j ↦ X.word (some j)) fun j ↦
    if j = i then (X.lines (some j) none).filter P else X.lines (some j) none

@[simp] theorem word_addLines (L : Finset (ℕ × ℕ)) (j : Option ι) :
    (X.addLines i L).word j = X.word j := by cases j <;> rfl

@[simp] theorem word_filterLines (P : ℕ × ℕ → Prop) [DecidablePred P] (j : Option ι) :
    (X.filterLines i P).word j = X.word j := by cases j <;> rfl

theorem mem_addLines {L : Finset (ℕ × ℕ)} {j : ι} {p : ℕ × ℕ} :
    p ∈ (X.addLines i L).lines (some j) none ↔ p ∈ X.lines (some j) none ∨
      j = i ∧ p ∈ L ∧ p.1 < (X.word (some j)).length ∧ p.2 < (X.word none).length := by
  obtain ⟨p, q⟩ := p
  have hX (h : (p, q) ∈ X.lines (some j) none) :
      p < (X.word (some j)).length ∧ q < (X.word none).length :=
    ⟨Link.lt_left h, Link.lt_right h⟩
  rcases eq_or_ne j i with rfl | hj
  · simp only [addLines, lines_ofPlanes, ite_true, Finset.mem_filter, Finset.mem_union,
      true_and]
    tauto
  · simp only [addLines, lines_ofPlanes, hj, ite_false, Finset.mem_filter, false_and, or_false]
    tauto

/-- Adding no lines leaves the lines of every plane as they were. -/
@[simp] theorem lines_addLines_empty (j : ι) :
    (X.addLines i ∅).lines (some j) none = X.lines (some j) none :=
  Finset.ext fun p ↦ by simp [mem_addLines]

/-- Adding no lines to a representation whose planes are not linked to one another changes
nothing. -/
theorem addLines_empty (h : ∀ j j', X.lines (some j) (some j') = ∅) : X.addLines i ∅ = X :=
  (congrArg (ofPlanes _ _) (funext fun j ↦ by split_ifs <;> simp)).trans (ofPlanes_eta X h)

theorem mem_filterLines {P : ℕ × ℕ → Prop} [DecidablePred P] {j : ι} {p : ℕ × ℕ} :
    p ∈ (X.filterLines i P).lines (some j) none ↔
      p ∈ X.lines (some j) none ∧ (j = i → P p) := by
  obtain ⟨p, q⟩ := p
  have hX (h : (p, q) ∈ X.lines (some j) none) :
      p < (X.word (some j)).length ∧ q < (X.word none).length :=
    ⟨Link.lt_left h, Link.lt_right h⟩
  rcases eq_or_ne j i with rfl | hj
  · simp only [filterLines, lines_ofPlanes, ite_true, Finset.mem_filter, forall_const]
    tauto
  · simp only [filterLines, lines_ofPlanes, hj, ite_false, Finset.mem_filter, false_imp_iff,
      and_true]
    tauto

end Lines

/-! ### Morphs on planes -/

section Sponsor

variable {S T M : Type u} (X : AR (Multiplanar ι (Sponsored T M) (Sponsored S M)))

/-- `ofSlots m t` is the morph of `m` with the slots `t` and nothing on any plane, as a prosodic
template is. -/
def ofSlots (m : M) (t : List S) : AR (Multiplanar ι (Sponsored T M) (Sponsored S M)) :=
  ofPlanes (t.map (⟨·, m⟩)) (fun _ ↦ []) fun _ ↦ ∅

@[simp] theorem word_ofSlots_none (m : M) (t : List S) :
    (ofSlots m t : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).word none =
      t.map (⟨·, m⟩) := rfl

@[simp] theorem word_ofSlots_some (m : M) (t : List S) (i : ι) :
    (ofSlots m t : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).word (some i) = [] := rfl

@[simp] theorem lines_ofSlots (m : M) (t : List S) (i : ι) :
    (ofSlots m t : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).lines (some i) none = ∅ :=
  rfl

/-- `ofMelody i m w` is the morph of `m` with the melody `w` on plane `i`, unlinked, and no
slots. -/
def ofMelody [DecidableEq ι] (i : ι) (m : M) (w : List T) :
    AR (Multiplanar ι (Sponsored T M) (Sponsored S M)) :=
  ofPlanes [] (fun j ↦ if j = i then w.map (⟨·, m⟩) else []) fun _ ↦ ∅

@[simp] theorem word_ofMelody_none [DecidableEq ι] (i : ι) (m : M) (w : List T) :
    (ofMelody i m w : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).word none = [] := rfl

@[simp] theorem word_ofMelody_some [DecidableEq ι] (i : ι) (m : M) (w : List T) (j : ι) :
    (ofMelody i m w : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).word (some j) =
      if j = i then w.map (⟨·, m⟩) else [] := rfl

@[simp] theorem lines_ofMelody [DecidableEq ι] (i : ι) (m : M) (w : List T) (j : ι) :
    (ofMelody i m w : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).lines (some j) none =
      ∅ := rfl

variable {T' : Type u} (φ : T → T')

/-- The representation with each autosegment relabeled by `φ`, with the same sponsors, slots and
lines. -/
def mapMelody : AR (Multiplanar ι (Sponsored T' M) (Sponsored S M)) where
  word
    | none => X.word none
    | some i => (X.word (some i)).map (Sponsored.map φ)
  lines := X.lines
  lines_self := X.lines_self
  swap_mem_lines := X.swap_mem_lines
  fst_lt_of_mem_lines i j p q h := by
    cases i
    · exact X.fst_lt_of_mem_lines h
    · simpa using X.fst_lt_of_mem_lines h

@[simp] theorem word_mapMelody_none : (X.mapMelody φ).word none = X.word none := rfl

@[simp] theorem word_mapMelody_some (i : ι) :
    (X.mapMelody φ).word (some i) = (X.word (some i)).map (Sponsored.map φ) := rfl

@[simp] theorem lines_mapMelody : (X.mapMelody φ).lines = X.lines := rfl

theorem hostedOn_mapMelody (i : ι) (s : ℕ) :
    (X.mapMelody φ).hostedOn i s = (X.hostedOn i s).map (Sponsored.map φ) := by
  simp only [hostedOn, word_mapMelody_some, lines_mapMelody, List.zipIdx_map, List.filter_map,
    List.map_map]
  rfl

/-- Relabeling commutes with concatenation. -/
theorem mapMelody_mul (Y : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))) :
    (X * Y).mapMelody φ = X.mapMelody φ * Y.mapMelody φ :=
  ext (funext fun j ↦ by cases j <;> simp [mapMelody]) fun i j p q ↦ by
    rcases i with _ | i <;> rcases j with _ | j <;> simp [Link, mapMelody]

theorem mapMelody_one :
    (1 : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).mapMelody φ = 1 :=
  ext (funext fun j ↦ by cases j <;> rfl) fun _ _ _ _ ↦ .rfl

theorem mapMelody_ofSlots (m : M) (t : List S) :
    (ofSlots m t : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).mapMelody φ =
      ofSlots m t :=
  ext (funext fun j ↦ by cases j <;> rfl) fun _ _ _ _ ↦ .rfl

theorem mapMelody_ofMelody [DecidableEq ι] (i : ι) (m : M) (w : List T) :
    (ofMelody i m w : AR (Multiplanar ι (Sponsored T M) (Sponsored S M))).mapMelody φ =
      ofMelody i m (w.map φ) :=
  ext (funext fun j ↦ by
    rcases j with _ | j
    · rfl
    · by_cases hj : j = i <;> simp [mapMelody, hj, Sponsored.map]) fun _ _ _ _ ↦ .rfl

theorem mapMelody_eraseSlot (k : ℕ) :
    (X.eraseSlot k).mapMelody φ = (X.mapMelody φ).eraseSlot k :=
  ext (funext fun j ↦ by cases j <;> rfl) fun i j p q ↦ by
    rcases i with _ | i <;> rcases j with _ | j <;> simp [Link, mapMelody, eraseSlot, ofPlanes]

theorem mapMelody_addLines [DecidableEq ι] (i : ι) (L : Finset (ℕ × ℕ)) :
    (X.addLines i L).mapMelody φ = (X.mapMelody φ).addLines i L :=
  ext (funext fun j ↦ by cases j <;> rfl) fun a b p q ↦ by
    rcases a with _ | a <;> rcases b with _ | b <;> simp [Link, mapMelody, addLines, ofPlanes]

theorem mapMelody_filterLines [DecidableEq ι] (i : ι) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (X.filterLines i P).mapMelody φ = (X.mapMelody φ).filterLines i P :=
  ext (funext fun j ↦ by cases j <;> rfl) fun a b p q ↦ by
    rcases a with _ | a <;> rcases b with _ | b <;> simp [Link, mapMelody, filterLines, ofPlanes]

end Sponsor

end AR

end Autosegmental
