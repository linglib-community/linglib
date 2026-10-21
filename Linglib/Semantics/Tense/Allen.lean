module

public import Linglib.Core.Order.Compare
public import Linglib.Core.Order.Interval.Basic
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# Allen's interval relations

This file defines the relations between closed intervals of a linear order that [allen-1983]
takes as the atoms of temporal reasoning, extended to intervals that are points. One interval
stands to another as their endpoints compare: each endpoint of the first with each endpoint of
the second, and the endpoints of each with each other, which tells a point from a proper interval
(`Allen.Relation`, `Allen.relation`). Twenty-six such relations are realizable (`Allen.card_atoms`):
Allen's thirteen between proper intervals, five between a point and a proper interval, five
between a proper interval and a point, and three between points.

A cell is a set of relations, the disjunction a temporal expression imposes, and `Allen.toSetRel`
reads it as a relation between intervals. Cells have converses and composites (`Allen.inv`,
`Allen.comp`), the composite read off configurations of endpoints, and on dense time without
endpoints the composite of two cells relates exactly the intervals that the composite of their
relations does (`Allen.toSetRel_comp`). That a relation records which intervals are points is what
makes the composite exact: a point and a proper interval can stand alike to one interval and
unlike to another.

The cells of the tense and aspect literature are named here, each read as one of the relations of
`Core/Order/Interval/Basic.lean`: precedence, precedence or abutment, the subinterval order and its
strict part, overlap, and the first interval's starting within the second. The position of one
interval relative to another is a function of their relation (`Allen.position_relation`), so a
cell of positions, as the comparison cells of the tenses are read on intervals, is a cell
(`Allen.ofPosition`).

## Main definitions

* `Allen.Relation`, `Allen.relation`: how one interval stands to another.
* `Allen.atoms`: the realizable relations.
* `Allen.toSetRel`: a cell as a relation between intervals.
* `Allen.inv`, `Allen.comp`: the converse and the composite of cells.
* `Allen.precedes`, `Allen.isBefore`, `Allen.le`, `Allen.lt`, `Allen.overlaps`,
  `Allen.startsWithin`, `Allen.ofPosition`: the named cells.

## Main results

* `Allen.card_atoms`: twenty-six relations are realizable.
* `Allen.toSetRel_inv`: the converse of a cell's relation is the relation of its converse.
* `Allen.toSetRel_comp_subset`, `Allen.toSetRel_comp`: the composite of two cells' relations lies
  in the relation of their composite, and is it on dense time without endpoints.
* `Allen.position_relation`: the position of two intervals is read off their relation.
* `Allen.relation_mem_precedes` and its siblings: the named cells relate the intervals that the
  relations of `Core/Order/Interval/Basic.lean` do.

## References

* [allen-1983]
-/

@[expose] public section

namespace Allen

open SetRel

/-- How one interval stands to another: the comparisons of the first interval's start and end with
the second's start and end, and of each interval's start with its own end, `lt` for a proper
interval and `eq` for a point. -/
structure Relation where
  /-- The first interval's start against the second's start. -/
  fstFst : Ordering
  /-- The first interval's start against the second's end. -/
  fstSnd : Ordering
  /-- The first interval's end against the second's start. -/
  sndFst : Ordering
  /-- The first interval's end against the second's end. -/
  sndSnd : Ordering
  /-- The first interval's start against its end. -/
  firstShape : Ordering
  /-- The second interval's start against its end. -/
  secondShape : Ordering
  deriving DecidableEq, Repr, Fintype

/-- The relation of an interval with endpoints `a` and `b` to one with endpoints `c` and `d`. -/
def ofEndpoints {α : Type*} [LinearOrder α] (a b c d : α) : Relation :=
  ⟨compare a c, compare a d, compare b c, compare b d, compare a b, compare c d⟩

/-- Points of two linear orders that compare alike give their intervals the same relations. -/
theorem ofEndpoints_eq {α β : Type*} [LinearOrder α] [LinearOrder β] {n : ℕ} {f : Fin n → α}
    {g : Fin n → β} (h : ∀ x y, compare (f x) (f y) = compare (g x) (g y)) (a b c d : Fin n) :
    ofEndpoints (f a) (f b) (f c) (f d) = ofEndpoints (g a) (g b) (g c) (g d) := by
  simp [ofEndpoints, h]

/-- The realizable relations, those of two intervals with endpoints among four points. -/
def atoms : Finset Relation :=
  ((Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter
      fun x ↦ x.1 ≤ x.2.1 ∧ x.2.2.1 ≤ x.2.2.2).image
    fun x ↦ ofEndpoints x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Twenty-six relations are realizable: Allen's thirteen between proper intervals, five between
a point and a proper interval, five between a proper interval and a point, and three between
points. -/
theorem card_atoms : atoms.card = 26 := by decide +kernel

/-! ### The relation of two intervals -/

section LinearOrder

variable {T : Type*} [LinearOrder T]

/-- The relation of the interval `i` to the interval `j`. -/
def relation (i j : NonemptyInterval T) : Relation := ofEndpoints i.fst i.snd j.fst j.snd

/-- Every relation of two intervals is realizable. -/
theorem relation_mem_atoms (i j : NonemptyInterval T) : relation i j ∈ atoms := by
  obtain ⟨g, hg⟩ := Ordering.exists_fin_compare_eq ![i.fst, i.snd, j.fst, j.snd]
  refine Finset.mem_image.2 ⟨(g 0, g 1, g 2, g 3), Finset.mem_filter.2
    ⟨Finset.mem_univ _, compare_le_iff_le.1 ?_, compare_le_iff_le.1 ?_⟩, ?_⟩
  · rw [hg 0 1]; exact compare_le_iff_le.2 i.fst_le_snd
  · rw [hg 2 3]; exact compare_le_iff_le.2 j.fst_le_snd
  · exact ofEndpoints_eq (f := g) (g := ![i.fst, i.snd, j.fst, j.snd]) hg 0 1 2 3

/-- The relation a cell imposes between intervals. -/
def toSetRel (C : Finset Relation) : SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  {p | relation p.1 p.2 ∈ C}

variable {C D : Finset Relation} {i j : NonemptyInterval T}

@[simp] theorem mem_toSetRel : (i, j) ∈ toSetRel C ↔ relation i j ∈ C := .rfl

theorem toSetRel_mono (h : C ⊆ D) : (toSetRel C : SetRel (NonemptyInterval T) _) ⊆ toSetRel D :=
  fun _ hp ↦ h hp

end LinearOrder

/-! ### Converse -/

/-- The converse of a relation: how the second interval stands to the first. -/
def Relation.inv (r : Relation) : Relation :=
  ⟨r.fstFst.swap, r.sndFst.swap, r.fstSnd.swap, r.sndSnd.swap, r.secondShape, r.firstShape⟩

@[simp] theorem Relation.inv_inv (r : Relation) : r.inv.inv = r := by
  simp [Relation.inv]

/-- The converse of a cell. -/
def inv (C : Finset Relation) : Finset Relation := C.image Relation.inv

@[simp] theorem mem_inv {C : Finset Relation} {r : Relation} : r ∈ inv C ↔ r.inv ∈ C :=
  ⟨fun h ↦ by obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h; simpa using hs,
    fun h ↦ Finset.mem_image.2 ⟨r.inv, h, r.inv_inv⟩⟩

@[simp] theorem inv_inv (C : Finset Relation) : inv (inv C) = C := by
  ext r; simp

section LinearOrder

variable {T : Type*} [LinearOrder T]

private theorem swap_compare (a b : T) : (compare a b).swap = compare b a :=
  Std.OrientedOrd.eq_swap.symm

@[simp] theorem inv_relation (i j : NonemptyInterval T) : (relation i j).inv = relation j i := by
  simp [relation, ofEndpoints, Relation.inv, swap_compare]

/-- The converse of a cell's relation is the relation of its converse. -/
@[simp] theorem toSetRel_inv (C : Finset Relation) :
    (toSetRel (inv C) : SetRel (NonemptyInterval T) _) = (toSetRel C).inv := by
  ext ⟨i, j⟩
  simp

end LinearOrder

/-! ### Composition -/

/-- The composite of two cells: the relations of an interval to a third compatible with its
standing in `C` to a second that stands in `D` to the third, read off configurations of the three
intervals' endpoints among six points. -/
def comp (C D : Finset Relation) : Finset Relation :=
  atoms.filter fun t ↦ ∃ e : Fin 6 → Fin 6, e 0 ≤ e 1 ∧ e 2 ≤ e 3 ∧ e 4 ≤ e 5 ∧
    ofEndpoints (e 0) (e 1) (e 2) (e 3) ∈ C ∧ ofEndpoints (e 2) (e 3) (e 4) (e 5) ∈ D ∧
    ofEndpoints (e 0) (e 1) (e 4) (e 5) = t

/-- A relation is in the composite of two cells when it is realizable and some configuration of
three intervals' endpoints among six points realizes it with the two cells. -/
theorem mem_comp {C D : Finset Relation} {t : Relation} :
    t ∈ comp C D ↔ t ∈ atoms ∧ ∃ e : Fin 6 → Fin 6, e 0 ≤ e 1 ∧ e 2 ≤ e 3 ∧ e 4 ≤ e 5 ∧
      ofEndpoints (e 0) (e 1) (e 2) (e 3) ∈ C ∧ ofEndpoints (e 2) (e 3) (e 4) (e 5) ∈ D ∧
      ofEndpoints (e 0) (e 1) (e 4) (e 5) = t :=
  Finset.mem_filter

section LinearOrder

variable {T : Type*} [LinearOrder T] {C D : Finset Relation}

/-- The composite of two cells' relations lies in the relation of their composite. -/
theorem toSetRel_comp_subset :
    (toSetRel C ○ toSetRel D : SetRel (NonemptyInterval T) _) ⊆ toSetRel (comp C D) := by
  rintro ⟨i, k⟩ ⟨j, hij, hjk⟩
  let f : Fin 6 → T := ![i.fst, i.snd, j.fst, j.snd, k.fst, k.snd]
  obtain ⟨g, hg⟩ := Ordering.exists_fin_compare_eq f
  have hle (a b : Fin 6) (h : f a ≤ f b) : g a ≤ g b :=
    compare_le_iff_le.1 (by rw [hg]; exact compare_le_iff_le.2 h)
  refine mem_toSetRel.2 <| mem_comp.2 ⟨relation_mem_atoms i k, g, hle 0 1 i.fst_le_snd,
    hle 2 3 j.fst_le_snd, hle 4 5 k.fst_le_snd, ?_, ?_, ?_⟩
  · rw [ofEndpoints_eq hg 0 1 2 3]; exact mem_toSetRel.1 hij
  · rw [ofEndpoints_eq hg 2 3 4 5]; exact mem_toSetRel.1 hjk
  · exact ofEndpoints_eq hg 0 1 4 5

/-- On dense time without endpoints, the relation of the composite of two cells is the composite
of their relations: the second interval of a configuration of endpoints can be placed between
any two intervals that stand as its first and third do. -/
theorem toSetRel_comp [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] :
    (toSetRel (comp C D) : SetRel (NonemptyInterval T) _) = toSetRel C ○ toSetRel D := by
  refine le_antisymm (fun ⟨i, k⟩ h ↦ ?_) toSetRel_comp_subset
  have : Nonempty T := ⟨i.fst⟩
  obtain ⟨-, e, -, h23, -, hC, hD, hik⟩ := mem_comp.1 (mem_toSetRel.1 h)
  -- the endpoints of `i` and `k`, then those of the interval to be placed
  let q : Fin 6 → Fin 6 := ![e 0, e 1, e 4, e 5, e 2, e 3]
  have hq : ∀ x y : Fin 4, compare (![i.fst, i.snd, k.fst, k.snd] x) (![i.fst, i.snd, k.fst,
      k.snd] y) = compare (q (x.castSucc.castSucc)) (q (y.castSucc.castSucc)) := by
    simp only [relation, ofEndpoints, Relation.mk.injEq] at hik
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hik
    have r {a b : Fin 6} {c d : T} (h : compare a b = compare c d) :
        compare b a = compare d c := by rw [← swap_compare, h, swap_compare]
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [q, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← r h1, ← r h2, ← r h3, ← r h4, ← r h5,
        ← r h6]
  obtain ⟨a, ha⟩ := Ordering.exists_snoc_compare_eq (q := fun x : Fin 5 ↦ q x.castSucc) hq
  obtain ⟨b, hb⟩ := Ordering.exists_snoc_compare_eq (q := q) (p := Fin.snoc
    (α := fun _ ↦ T) ![i.fst, i.snd, k.fst, k.snd] a) ha
  have hab : a ≤ b := compare_le_iff_le.1 (by
    have := hb 4 5
    simp [Fin.snoc, q] at this
    simpa [this] using compare_le_iff_le.2 h23)
  refine ⟨⟨(a, b), hab⟩, mem_toSetRel.2 ?_, mem_toSetRel.2 ?_⟩
  · have := ofEndpoints_eq hb 0 1 4 5
    simp [Fin.snoc, q] at this
    simpa [relation, this] using hC
  · have := ofEndpoints_eq hb 4 5 2 3
    simp [Fin.snoc, q] at this
    rw [← this] at hD
    exact hD

end LinearOrder

/-! ### Named cells -/

/-- The first interval ends before the second starts. -/
def precedes : Finset Relation := atoms.filter (·.sndFst = .lt)

/-- The first interval ends no later than the second starts. -/
def isBefore : Finset Relation := atoms.filter (·.sndFst ≠ .gt)

/-- The first interval lies within the second. -/
def le : Finset Relation := atoms.filter fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd ≠ .gt

/-- The first interval lies within the second and is not the whole of it. -/
def lt : Finset Relation := le.filter fun r ↦ r.fstFst = .gt ∨ r.sndSnd = .lt

/-- The two intervals overlap. -/
def overlaps : Finset Relation := atoms.filter fun r ↦ r.fstSnd ≠ .gt ∧ r.sndFst ≠ .lt

/-- The first interval starts within the second. -/
def startsWithin : Finset Relation := atoms.filter fun r ↦ r.fstFst ≠ .lt ∧ r.fstSnd ≠ .gt

/-- The position of the first interval relative to the second: before it, after it, or
overlapping it. -/
def Relation.position (r : Relation) : Ordering :=
  if r.sndFst = .lt then .lt else if r.fstSnd = .gt then .gt else .eq

/-- The cell of the relations whose position is one of `C`. -/
def ofPosition (C : Finset Ordering) : Finset Relation := atoms.filter (·.position ∈ C)

/-- Overlap is the position between precedence either way, so that a cell of positions lumps
abutment with overlap. -/
theorem ofPosition_eq : ofPosition {.eq} = overlaps := by decide +kernel

section LinearOrder

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

/-- The relation of two intervals is among the realizable relations satisfying `p` iff it
satisfies `p`. -/
theorem relation_mem_filter {p : Relation → Prop} [DecidablePred p] :
    relation i j ∈ atoms.filter p ↔ p (relation i j) := by
  simp [relation_mem_atoms]

@[simp] theorem relation_mem_precedes : relation i j ∈ precedes ↔ i.Precedes j := by
  rw [precedes, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.Precedes, compare_lt_iff_lt]

@[simp] theorem relation_mem_isBefore : relation i j ∈ isBefore ↔ i.IsBefore j := by
  rw [isBefore, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.IsBefore, compare_le_iff_le]

@[simp] theorem relation_mem_le : relation i j ∈ le ↔ i ≤ j := by
  rw [le, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.le_def, compare_le_iff_le, compare_ge_iff_ge]

@[simp] theorem relation_mem_lt : relation i j ∈ lt ↔ i < j := by
  rw [NonemptyInterval.lt_def, ← relation_mem_le, lt, Finset.mem_filter]
  simp [relation, ofEndpoints, compare_gt_iff_gt, compare_lt_iff_lt]

@[simp] theorem relation_mem_overlaps : relation i j ∈ overlaps ↔ i.Overlaps j := by
  rw [overlaps, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.Overlaps, compare_le_iff_le, compare_ge_iff_ge]

@[simp] theorem relation_mem_startsWithin : relation i j ∈ startsWithin ↔ i.fst ∈ j := by
  rw [startsWithin, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.mem_def, compare_le_iff_le, compare_ge_iff_ge]

/-- The position of two intervals is read off their relation. -/
theorem position_relation (i j : NonemptyInterval T) : i.position j = (relation i j).position := by
  simp [NonemptyInterval.position, Relation.position, relation, ofEndpoints,
    NonemptyInterval.Precedes, compare_gt_iff_gt, compare_lt_iff_lt]
  split_ifs <;> rfl

@[simp] theorem relation_mem_ofPosition {C : Finset Ordering} :
    relation i j ∈ ofPosition C ↔ i.position j ∈ C := by
  rw [ofPosition, relation_mem_filter, position_relation]

end LinearOrder

end Allen
