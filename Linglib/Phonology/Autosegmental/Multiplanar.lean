/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Linglib.Phonology.Autosegmental.Morph
public import Linglib.Phonology.Autosegmental.Edit
public import Linglib.Phonology.Autosegmental.TierTree.Basic

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

The tiers form a tree, `AR.planes`, with the slots at the root and every plane hanging from
them. A slot dominates the autosegments linked to it (`dominates_planes_iff`), so the melody
it bears on a plane, `X.melody planes s (some i)`, lists those autosegments in the order of the
plane (`mem_melody_planes_iff`).

## Implementation notes

Lines are added to a plane and erased from it by `AR.addLines` and `AR.filterLines` of
`Autosegmental/Edit.lean`, between the plane and the slots (`mem_addLines`, `mem_filterLines`).
`AR.eraseSlot` rebuilds the representation with `AR.ofPlanes`, so its result has lines from
planes to slots only: a line between two planes, which no multiplanar representation has, is
not carried over.

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

/-! ### The tree of tiers -/

section Planes

/-- The tree of tiers of a multiplanar representation: every plane hangs from the slots. -/
def planes : ParentTree (Option ι) := .ofIterate (fun _ ↦ none) none 1 fun _ ↦ rfl

@[simp] theorem planes_root : (planes : ParentTree (Option ι)).root = none := rfl

@[simp] theorem planes_parent (j : Option ι) : (planes : ParentTree (Option ι)).parent j = none :=
  rfl

variable {X} [Fintype ι] [DecidableEq ι] {i : ι} {s q : ℕ} {a : α}

/-- A slot dominates the autosegments linked to it. -/
theorem dominates_planes_iff : X.Dominates planes s (some i) q ↔ X.Link (some i) none q s := by
  rw [dominates_iff_dom]
  refine (dom_root_iff_mem_children (T := planes) (j := some i) rfl).trans ⟨?_, fun h ↦ .inr ?_⟩
  · rintro (⟨h, -⟩ | h)
    · exact absurd h (Option.some_ne_none i)
    · exact (mem_children.1 h).2.2.symm
  · exact mem_children.2 ⟨rfl, Option.some_ne_none i, h.symm⟩

/-- The melody a slot bears on a plane has the autosegments of the plane linked to it. -/
theorem mem_melody_planes_iff : a ∈ X.melody planes s (some i) ↔
    ∃ q, X.Link (some i) none q s ∧ (X.word (some i))[q]? = some a := by
  simp only [mem_melody_iff_exists_dominates, dominates_planes_iff]

end Planes

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

variable [DecidableEq ι] {X} {i j : ι} {p : ℕ × ℕ}

/-- The lines of a plane after `L` is added to plane `i`. -/
theorem mem_addLines {L : Finset (ℕ × ℕ)} :
    p ∈ (X.addLines (some i) none L).lines (some j) none ↔ p ∈ X.lines (some j) none ∨
      j = i ∧ p ∈ L ∧ p.1 < (X.word (some j)).length ∧ p.2 < (X.word none).length := by
  obtain ⟨p, q⟩ := p
  refine (link_addLines (X := X) (i := some i) (j := none) (i' := some j) (j' := none)
    (p := p) (q := q) (L := L)).trans ?_
  constructor
  · rintro (h | ⟨-, ⟨hj, -, hL, hp, hq⟩ | ⟨hj, -⟩⟩)
    · exact .inl h
    · obtain rfl := Option.some.inj hj
      exact .inr ⟨rfl, hL, hp, hq⟩
    · exact absurd hj (Option.some_ne_none j)
  · rintro (h | ⟨rfl, hL, hp, hq⟩)
    · exact .inl h
    · exact .inr ⟨Option.some_ne_none _, .inl ⟨rfl, rfl, hL, hp, hq⟩⟩

/-- The lines of a plane after the lines of plane `i` are filtered by `P`. -/
theorem mem_filterLines {P : ℕ × ℕ → Prop} [DecidablePred P] :
    p ∈ (X.filterLines (some i) none P).lines (some j) none ↔
      p ∈ X.lines (some j) none ∧ (j = i → P p) := by
  obtain ⟨p, q⟩ := p
  refine (link_filterLines (X := X) (i := some i) (j := none) (i' := some j) (j' := none)
    (p := p) (q := q) (P := P)).trans (and_congr_right fun _ ↦ ?_)
  exact ⟨fun h hj ↦ h.1 (congrArg some hj) rfl, fun h ↦ ⟨fun hj _ ↦ h (Option.some.inj hj),
    fun hj ↦ absurd hj (Option.some_ne_none j)⟩⟩

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
    (X.addLines (some i) none L).mapMelody φ = (X.mapMelody φ).addLines (some i) none L :=
  ext (funext fun j ↦ by cases j <;> rfl) fun a b p q ↦ by
    show (X.addLines (some i) none L).Link a b p q ↔ _
    rw [link_addLines, link_addLines]
    simp [Link]

theorem mapMelody_filterLines [DecidableEq ι] (i : ι) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (X.filterLines (some i) none P).mapMelody φ = (X.mapMelody φ).filterLines (some i) none P :=
  ext (funext fun j ↦ by cases j <;> rfl) fun a b p q ↦ by
    show (X.filterLines (some i) none P).Link a b p q ↔ _
    rw [link_filterLines, link_filterLines]
    simp [Link]

end Sponsor

end AR

end Autosegmental
