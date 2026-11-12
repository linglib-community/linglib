/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Form

/-!
# Multiplanar forms

A multiplanar form is a tier of slots shared by several planes, each plane a tier of autosegments
associated with the slots, the planes meeting along the slots as McCarthy's planes meet along the
skeleton. Plane `i` is the two-tier form `plane i`, and the No-Crossing Constraint holds plane by
plane, since autosegments on different planes stand in no order. Multiplanar forms concatenate
plane by plane, presentation as a representation is an injective monoid hom, and forms occupying
disjoint tiers commute: morphs on separate planes are unordered.

## Main definitions

* `Multiplanar ι α β`: the alphabets of a multiplanar representation, with the slots on `none`.
* `MultiplanarForm ι S T M`: slots in `S`, autosegments in `T` on the planes `ι`, sponsors in `M`.
* `MultiplanarForm.plane`, `MultiplanarForm.ofPlane`: a plane as a form, and a form on a plane.
* `MultiplanarForm.addLines`, `MultiplanarForm.filterLines`: lines added to or kept on a plane.
* `MultiplanarForm.hostedOn`: the autosegments of a plane linked to a slot.
* `MultiplanarForm.toAR`: the representation a multiplanar form presents.

## Main results

* `MultiplanarForm.noCrossing_toAR_iff`: the presented representation obeys the NCC iff the lines
  of each plane are non-crossing.
* `MultiplanarForm.toARHom`, `MultiplanarForm.toAR_injective`: presentation is an injective
  monoid hom.
* `MultiplanarForm.commute_of_disjoint_support`: forms on disjoint tiers commute.

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

/-- A `MultiplanarForm ι S T M` is a tier of slots in `S` and, on each plane `i : ι`, a tier of
autosegments in `T` with association lines from its positions to positions of the slots. Every
element is sponsored by a morpheme in `M`. -/
@[ext] structure MultiplanarForm (ι S T M : Type*) where
  /-- The slots, which every plane shares. -/
  lower : List (Sponsored S M)
  /-- The autosegments of each plane, in tier order. -/
  upper : ι → List (Sponsored T M)
  /-- The lines of each plane, from a position of its autosegments to a position of the slots. -/
  lines : ι → Finset (ℕ × ℕ)
  lt_of_mem_lines {i : ι} {p : ℕ × ℕ} :
    p ∈ lines i → p.1 < (upper i).length ∧ p.2 < lower.length

namespace MultiplanarForm

variable {ι S T M : Type*} (f g : MultiplanarForm ι S T M)

instance [Fintype ι] [DecidableEq S] [DecidableEq T] [DecidableEq M] :
    DecidableEq (MultiplanarForm ι S T M) :=
  fun _ _ ↦ decidable_of_iff _ MultiplanarForm.ext_iff.symm

/-- Plane `i`, the form of its autosegments over the slots. -/
def plane (i : ι) : Form (Sponsored T M) (Sponsored S M) :=
  ⟨f.upper i, f.lower, f.lines i, f.lt_of_mem_lines⟩

@[simp] theorem plane_upper (i : ι) : (f.plane i).upper = f.upper i := rfl

@[simp] theorem plane_lower (i : ι) : (f.plane i).lower = f.lower := rfl

@[simp] theorem plane_lines (i : ι) : (f.plane i).lines = f.lines i := rfl

theorem lines_eq_empty_of_upper {i : ι} (h : f.upper i = []) : f.lines i = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hp ↦ by simpa [h] using (f.lt_of_mem_lines hp).1

/-- `f.hostedOn i s` lists, in tier order, the autosegments of plane `i` linked to slot `s`. -/
def hostedOn (i : ι) (s : ℕ) : List (Sponsored T M) :=
  ((f.upper i).zipIdx.filter fun x ↦ (x.2, s) ∈ f.lines i).map Prod.fst

/-- The form with each autosegment relabeled by `φ`, with the same sponsors and lines. -/
def map {T' : Type*} (φ : T → T') : MultiplanarForm ι S T' M where
  lower := f.lower
  upper i := (f.upper i).map (Sponsored.map φ)
  lines := f.lines
  lt_of_mem_lines h := by simpa using f.lt_of_mem_lines h

section Map

variable {T' : Type*} (φ : T → T')

@[simp] theorem map_lower : (f.map φ).lower = f.lower := rfl

@[simp] theorem map_upper (i : ι) : (f.map φ).upper i = (f.upper i).map (Sponsored.map φ) := rfl

@[simp] theorem map_lines : (f.map φ).lines = f.lines := rfl

theorem hostedOn_map (i : ι) (s : ℕ) :
    (f.map φ).hostedOn i s = (f.hostedOn i s).map (Sponsored.map φ) := by
  simp only [hostedOn, map_upper, map_lines, List.zipIdx_map, List.filter_map, List.map_map]
  rfl

end Map

/-- `ofSlots m t` is the morph of `m` with the slots `t` and nothing on any plane, as a prosodic
template is. -/
def ofSlots (m : M) (t : List S) : MultiplanarForm ι S T M :=
  ⟨t.map (⟨·, m⟩), fun _ ↦ [], fun _ ↦ ∅, fun h ↦ by simp at h⟩

@[simp] theorem ofSlots_lower (m : M) (t : List S) :
    (ofSlots m t : MultiplanarForm ι S T M).lower = t.map (⟨·, m⟩) := rfl

@[simp] theorem ofSlots_upper (m : M) (t : List S) (i : ι) :
    (ofSlots m t : MultiplanarForm ι S T M).upper i = [] := rfl

@[simp] theorem ofSlots_lines (m : M) (t : List S) (i : ι) :
    (ofSlots m t : MultiplanarForm ι S T M).lines i = ∅ := rfl

theorem map_ofSlots {T' : Type*} (φ : T → T') (m : M) (t : List S) :
    (ofSlots m t : MultiplanarForm ι S T M).map φ = ofSlots m t := rfl

/-- `f.eraseSlot k` deletes slot `k` with every line it bears, moving the lines of the later
slots one position left. -/
def eraseSlot (k : ℕ) : MultiplanarForm ι S T M where
  lower := f.lower.eraseIdx k
  upper := f.upper
  lines i := ((f.lines i).filter (·.2 ≠ k)).image fun l ↦ if k < l.2 then (l.1, l.2 - 1) else l
  lt_of_mem_lines {i} {_} h := by
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨hl, hne⟩ := Finset.mem_filter.1 hl
    have := f.lt_of_mem_lines hl
    rw [List.length_eraseIdx]
    by_cases hk : k < l.2 <;> by_cases hk' : k < f.lower.length <;> simp [hk, hk'] <;> omega

@[simp] theorem eraseSlot_upper (k : ℕ) : (f.eraseSlot k).upper = f.upper := rfl

@[simp] theorem eraseSlot_lower (k : ℕ) : (f.eraseSlot k).lower = f.lower.eraseIdx k := rfl

theorem map_eraseSlot {T' : Type*} (φ : T → T') (k : ℕ) :
    (f.eraseSlot k).map φ = (f.map φ).eraseSlot k := rfl

/-! ### Planes and lines -/

section Lines

variable [DecidableEq ι]

/-- `ofPlane i x` puts the form `x` on plane `i`, with every other plane empty. -/
def ofPlane (i : ι) (x : Form (Sponsored T M) (Sponsored S M)) : MultiplanarForm ι S T M where
  lower := x.lower
  upper j := if j = i then x.upper else []
  lines j := if j = i then x.lines else ∅
  lt_of_mem_lines {j} {_} h := by
    by_cases hj : j = i
    · subst hj
      simpa using x.lt_of_mem_lines (by simpa using h)
    · simp [hj] at h

variable (i : ι) (x : Form (Sponsored T M) (Sponsored S M))

@[simp] theorem ofPlane_lower : (ofPlane i x).lower = x.lower := rfl

@[simp] theorem ofPlane_upper (j : ι) :
    (ofPlane i x).upper j = if j = i then x.upper else [] := rfl

@[simp] theorem ofPlane_lines (j : ι) :
    (ofPlane i x).lines j = if j = i then x.lines else ∅ := rfl

@[simp] theorem plane_ofPlane : (ofPlane i x).plane i = x := by
  ext <;> simp

/-- `ofMelody i m w` is the morph of `m` with the melody `w` on plane `i`, unlinked, and no
slots. -/
def ofMelody (m : M) (w : List T) : MultiplanarForm ι S T M := ofPlane i (Form.morph m w [] ∅)

@[simp] theorem ofMelody_lower (m : M) (w : List T) : (ofMelody i m w : MultiplanarForm ι S T M).lower = [] := rfl

@[simp] theorem ofMelody_upper (m : M) (w : List T) (j : ι) :
    (ofMelody i m w : MultiplanarForm ι S T M).upper j = if j = i then w.map (⟨·, m⟩) else [] :=
  rfl

@[simp] theorem ofMelody_lines (m : M) (w : List T) (j : ι) :
    (ofMelody i m w : MultiplanarForm ι S T M).lines j = ∅ := by
  by_cases hj : j = i <;> simp [ofMelody, hj]

theorem map_ofMelody {T' : Type*} (φ : T → T') (m : M) (w : List T) :
    (ofMelody i m w : MultiplanarForm ι S T M).map φ = ofMelody i m (w.map φ) := by
  ext j
  · rfl
  · by_cases hj : j = i <;> simp [hj, Sponsored.map]
  · rfl

/-- `f.addLines i L` adds to plane `i` the lines of `L` that are in range, as
`SimpleGraph.fromEdgeSet` drops loops. -/
def addLines (L : Finset (ℕ × ℕ)) : MultiplanarForm ι S T M where
  lower := f.lower
  upper := f.upper
  lines j := if j = i then
    f.lines j ∪ L.filter fun p ↦ p.1 < (f.upper j).length ∧ p.2 < f.lower.length else f.lines j
  lt_of_mem_lines {j} {_} h := by
    split_ifs at h
    · rcases Finset.mem_union.1 h with h | h
      exacts [f.lt_of_mem_lines h, (Finset.mem_filter.1 h).2]
    · exact f.lt_of_mem_lines h

/-- `f.filterLines i P` keeps the lines of plane `i` that satisfy `P`. -/
def filterLines (P : ℕ × ℕ → Prop) [DecidablePred P] : MultiplanarForm ι S T M where
  lower := f.lower
  upper := f.upper
  lines j := if j = i then (f.lines j).filter P else f.lines j
  lt_of_mem_lines {j} {_} h := by
    split_ifs at h
    · exact f.lt_of_mem_lines (Finset.mem_filter.1 h).1
    · exact f.lt_of_mem_lines h

@[simp] theorem addLines_lower (L : Finset (ℕ × ℕ)) : (f.addLines i L).lower = f.lower := rfl

@[simp] theorem addLines_upper (L : Finset (ℕ × ℕ)) : (f.addLines i L).upper = f.upper := rfl

@[simp] theorem filterLines_lower (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (f.filterLines i P).lower = f.lower := rfl

@[simp] theorem filterLines_upper (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (f.filterLines i P).upper = f.upper := rfl

@[simp] theorem addLines_empty : f.addLines i ∅ = f :=
  MultiplanarForm.ext rfl rfl (funext fun j ↦ by by_cases hj : j = i <;> simp [addLines, hj])

theorem mem_addLines {L : Finset (ℕ × ℕ)} {j : ι} {p : ℕ × ℕ} :
    p ∈ (f.addLines i L).lines j ↔
      p ∈ f.lines j ∨ j = i ∧ p ∈ L ∧ p.1 < (f.upper j).length ∧ p.2 < f.lower.length := by
  by_cases hj : j = i <;> simp [addLines, hj]

theorem map_addLines {T' : Type*} (φ : T → T') (L : Finset (ℕ × ℕ)) :
    (f.addLines i L).map φ = (f.map φ).addLines i L := by
  ext <;> simp [addLines]

theorem map_filterLines {T' : Type*} (φ : T → T') (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (f.filterLines i P).map φ = (f.map φ).filterLines i P := rfl

end Lines

/-! ### Concatenation -/

/-- `concat f g` juxtaposes the slots of `f` and `g` and the autosegments of each plane, and shifts
the lines of `g` past the tiers of `f`, plane by plane as `Form.concat`. -/
def concat : MultiplanarForm ι S T M where
  lower := f.lower ++ g.lower
  upper i := f.upper i ++ g.upper i
  lines i := f.lines i ∪ (g.lines i).map (Form.shift (f.upper i).length f.lower.length)
  lt_of_mem_lines {i} {_} hp := ((f.plane i).concat (g.plane i)).lt_of_mem_lines hp

/-- The empty form has no slots, no autosegments, and no lines. -/
def empty : MultiplanarForm ι S T M := ⟨[], fun _ ↦ [], fun _ ↦ ∅, fun h ↦ by simp at h⟩

@[simp] theorem concat_lower : (f.concat g).lower = f.lower ++ g.lower := rfl

@[simp] theorem concat_upper (i : ι) : (f.concat g).upper i = f.upper i ++ g.upper i := rfl

@[simp] theorem concat_lines (i : ι) :
    (f.concat g).lines i =
      f.lines i ∪ (g.lines i).map (Form.shift (f.upper i).length f.lower.length) := rfl

theorem plane_concat (i : ι) : (f.concat g).plane i = (f.plane i).concat (g.plane i) := rfl

@[simp] theorem empty_lower : (empty : MultiplanarForm ι S T M).lower = [] := rfl

@[simp] theorem empty_upper (i : ι) : (empty : MultiplanarForm ι S T M).upper i = [] := rfl

@[simp] theorem empty_lines (i : ι) : (empty : MultiplanarForm ι S T M).lines i = ∅ := rfl

theorem concat_assoc (h : MultiplanarForm ι S T M) :
    (f.concat g).concat h = f.concat (g.concat h) :=
  MultiplanarForm.ext (List.append_assoc ..) (funext fun _ ↦ List.append_assoc ..)
    (funext fun i ↦ congrArg Form.lines (Form.concat_assoc (f.plane i) (g.plane i) (h.plane i)))

theorem empty_concat : empty.concat f = f :=
  MultiplanarForm.ext rfl rfl (funext fun i ↦ congrArg Form.lines (Form.empty_concat (f.plane i)))

theorem concat_empty : f.concat empty = f :=
  MultiplanarForm.ext (List.append_nil _) (funext fun _ ↦ List.append_nil _)
    (funext fun i ↦ congrArg Form.lines (Form.concat_empty (f.plane i)))

/-- Multiplanar forms are a monoid under concatenation, with the empty form as unit. -/
instance instMonoid : Monoid (MultiplanarForm ι S T M) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

@[simp] theorem mul_eq_concat : f * g = f.concat g := rfl

/-- Relabeling commutes with concatenation. -/
theorem map_concat {T' : Type*} (φ : T → T') : (f.concat g).map φ = (f.map φ).concat (g.map φ) := by
  ext i <;> simp

@[simp] theorem one_eq_empty : (1 : MultiplanarForm ι S T M) = empty := rfl

theorem map_mul {T' : Type*} (φ : T → T') : (f * g).map φ = f.map φ * g.map φ :=
  map_concat f g φ

theorem map_one {T' : Type*} (φ : T → T') : (1 : MultiplanarForm ι S T M).map φ = 1 := rfl

end MultiplanarForm

/-! ### Presentation -/

section Presentation

variable {ι : Type*} {S T M : Type u}

namespace MultiplanarForm

section Word

variable (f g : MultiplanarForm ι S T M)

/-- Concatenation preserves the No-Crossing Constraint on each plane. -/
theorem isNonCrossing_lines_concat {i : ι} (h₁ : IsNonCrossing (f.lines i : SetRel ℕ ℕ))
    (h₂ : IsNonCrossing (g.lines i : SetRel ℕ ℕ)) :
    IsNonCrossing ((f.concat g).lines i : SetRel ℕ ℕ) :=
  Form.isNonCrossing_lines_concat (f.plane i) (g.plane i) h₁ h₂

/-- The words of the presented representation: the slots on tier `none`, and the autosegments of
plane `i` on tier `some i`. -/
def word : ∀ j : Option ι, List (Multiplanar ι (Sponsored T M) (Sponsored S M) j)
  | none => f.lower
  | some i => f.upper i

@[simp] theorem word_none : f.word none = f.lower := rfl

@[simp] theorem word_some (i : ι) : f.word (some i) = f.upper i := rfl

/-- The presented lines: those of plane `i`, from tier `some i` to the slots' tier `none`. -/
def presentedLines : Option ι → Option ι → ℕ → ℕ → Prop
  | some i, none, p, q => (p, q) ∈ f.lines i
  | _, _, _, _ => False

instance : ∀ j k, DecidableRel (f.presentedLines j k)
  | some i, none => fun p q ↦ inferInstanceAs (Decidable ((p, q) ∈ f.lines i))
  | none, _ => fun _ _ ↦ inferInstanceAs (Decidable False)
  | some _, some _ => fun _ _ ↦ inferInstanceAs (Decidable False)

end Word

variable [DecidableEq ι] (f g : MultiplanarForm ι S T M)

/-- The representation a multiplanar form presents, with the sponsors on its labels. -/
def toAR : AR (Multiplanar ι (Sponsored T M) (Sponsored S M)) :=
  AR.fromRel f.word f.presentedLines

@[simp] theorem word_toAR : f.toAR.word = f.word := rfl

@[simp] theorem link_toAR {i : ι} {p q : ℕ} :
    f.toAR.Link (some i) none p q ↔ (p, q) ∈ f.lines i := by
  rw [toAR, AR.link_fromRel]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, word_some, word_none, presentedLines,
    or_false, true_and]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨(f.lt_of_mem_lines h).1, (f.lt_of_mem_lines h).2, h⟩⟩

theorem not_link_toAR_none_none {p q : ℕ} : ¬ f.toAR.Link none none p q :=
  fun h ↦ h.ne rfl

theorem not_link_toAR_some_some {i i' : ι} {p q : ℕ} : ¬ f.toAR.Link (some i) (some i') p q := by
  rw [toAR, AR.link_fromRel]
  simp [presentedLines]

@[simp] theorem none_mem_support_toAR : none ∈ f.toAR.support ↔ f.lower ≠ [] := .rfl

@[simp] theorem some_mem_support_toAR {i : ι} : some i ∈ f.toAR.support ↔ f.upper i ≠ [] := .rfl

/-- The presented representation obeys the NCC iff the lines of each plane are non-crossing. -/
theorem noCrossing_toAR_iff :
    f.toAR.NoCrossing ↔ ∀ i, IsNonCrossing (f.lines i : SetRel ℕ ℕ) := by
  have key (i : ι) :
      IsNonCrossing (f.toAR.lines (some i) none) ↔ IsNonCrossing (f.lines i : SetRel ℕ ℕ) := by
    rw [AR.isNonCrossing_lines_iff_link]
    congr! 1
    ext ⟨p, q⟩
    exact f.link_toAR
  refine ⟨fun h i ↦ (key i).1 (h _ _), fun h j k ↦ ?_⟩
  rcases j with _ | i <;> rcases k with _ | i'
  · exact AR.isNonCrossing_lines_self none
  · exact AR.isNonCrossing_lines_comm.2 ((key i').2 (h i'))
  · exact (key i).2 (h i)
  · exact AR.isNonCrossing_lines_iff.2 fun _ _ _ _ hl ↦ absurd hl f.not_link_toAR_some_some

instance [Fintype ι] : Decidable f.toAR.NoCrossing :=
  decidable_of_iff _ f.noCrossing_toAR_iff.symm

theorem toAR_concat : (f.concat g).toAR = f.toAR * g.toAR := by
  have main (i : ι) (p q : ℕ) :
      (f.concat g).toAR.Link (some i) none p q ↔ (f.toAR * g.toAR).Link (some i) none p q := by
    rw [AR.link_mul]
    simp only [link_toAR, word_toAR, word_some, word_none, concat_lines, Finset.mem_union,
      Finset.mem_map, Form.shift_apply, Prod.ext_iff]
    constructor
    · rintro (h | ⟨⟨a, b⟩, h, rfl, rfl⟩)
      · exact .inl h
      · exact .inr ⟨by omega, by omega, by simpa using h⟩
    · rintro (h | ⟨hp, hq, h⟩)
      · exact .inl h
      · exact .inr ⟨_, h, by omega, by omega⟩
  refine AR.ext (funext fun j ↦ ?_) fun j k p q ↦ ?_
  · cases j <;> rfl
  · rcases j with _ | i <;> rcases k with _ | i'
    · exact iff_of_false (not_link_toAR_none_none _) fun h ↦ h.ne rfl
    · rw [AR.link_comm, main, AR.link_comm]
    · exact main i p q
    · refine iff_of_false (not_link_toAR_some_some _) fun h ↦ ?_
      rcases (AR.link_mul _ _ _ _).1 h with h | ⟨-, -, h⟩
      exacts [f.not_link_toAR_some_some h, g.not_link_toAR_some_some h]

theorem toAR_empty : (empty : MultiplanarForm ι S T M).toAR = 1 :=
  AR.ext (funext fun j ↦ by cases j <;> rfl) fun j k p q ↦
    iff_of_false (fun h ↦ by cases j <;> simpa using h.lt_left) (AR.not_link_one _ _ _ _)

/-- Presentation is a monoid hom from multiplanar forms to representations. -/
@[simps] def toARHom : MultiplanarForm ι S T M →* AR (Multiplanar ι (Sponsored T M) (Sponsored S M))
    where
  toFun := toAR
  map_one' := toAR_empty
  map_mul' := toAR_concat

theorem toAR_injective : Function.Injective (toAR (ι := ι) (S := S) (T := T) (M := M)) := by
  intro f g h
  have hw := congrArg AR.word h
  refine MultiplanarForm.ext (congrFun hw none) (funext fun i ↦ congrFun hw (some i))
    (funext fun i ↦ Finset.ext fun ⟨p, q⟩ ↦ ?_)
  rw [← link_toAR, ← link_toAR, h]

/-- Multiplanar forms with disjoint supports commute: morphs on separate planes are unordered
([mccarthy-1989], p. 73). -/
theorem commute_of_disjoint_support (h : Disjoint f.toAR.support g.toAR.support) :
    Commute f g :=
  toAR_injective (by
    rw [mul_eq_concat, mul_eq_concat, toAR_concat, toAR_concat]
    exact AR.commute_of_disjoint_support h)

end MultiplanarForm

end Presentation

end Autosegmental
