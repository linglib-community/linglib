module

public import Linglib.Core.Order.Compare
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Core.Order.Interval.Fintype
public import Linglib.Semantics.Tense.Defs
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# Allen's interval relations

This file defines the relations between closed intervals of a linear order [allen-1983], extended
to point intervals. How one interval stands to another is the order type of their four endpoints,
recorded as the comparisons among them, and the relations are the comparisons that two intervals
realize, twenty-six in all. A cell is a set of relations, and cells have converses, composites and
chains.

## Main definitions

* `Allen.Comparisons`, `Allen.realizable`: the comparisons among the endpoints of two intervals,
  and those that two intervals realize.
* `Allen.Relation`, `Allen.relation`: the relations, and the relation of two intervals.
* `Allen.toSetRel`, `Allen.inv`, `Allen.comp`: a cell as a relation, its converse and composite.
* `Allen.precedes`, `Allen.isBefore`, `Allen.le`, `Allen.lt`, `Allen.overlaps`,
  `Allen.startsWithin`, `Allen.finalSubinterval`, `Allen.nonfinalSubinterval`, `Allen.eq`,
  `Allen.pure`, `Allen.ofPosition`: named cells.
* `Allen.HoldsAlong`, `Allen.compAlong`: chains of cells and their composites.

## Main results

* `Allen.card_relation`: there are twenty-six relations.
* `Allen.forall_toSetRel_subset_iff`: one cell's relation lies in another's on every linear order
  exactly when the cell lies in the other.
* `Allen.relation_map`: the relation of two intervals survives an order embedding.
* `Allen.toSetRel_comp`: composition is exact on dense time without endpoints, and so are the
  operators the cells induce on sets of intervals (`Allen.image_toSetRel_comp`).
* `Allen.comp_precedes_precedes`: precedence is transitive, an entry of Allen's table that the
  kernel decides.
* `Allen.comp_pure`: on points, Allen composition is the composition of comparison cells.
* `Allen.mem_compAlong_iff`: on dense time, the composite of a chain is exactly realized.

## Implementation notes

A relation records whether each interval is a point; with the four cross comparisons alone
composition is not exact. The composite of two cells is read off the intervals among six points,
placing a second interval only beside first intervals that stand to it in the first cell, which
keeps it small enough for `decide +kernel`. It and the named cells are irreducible, so that
elaboration, which never needs their values, does not compute them.

## References

* [allen-1983]
-/

@[expose] public section

namespace Allen

open SetRel

/-- The comparisons among the endpoints of two intervals: the first interval's start and end
against the second's start and end, and each interval's start against its own end, `lt` for a
proper interval and `eq` for a point. -/
structure Comparisons where
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
  deriving DecidableEq, Repr

/-- The comparisons among the endpoints of an interval from `a` to `b` and one from `c` to `d`. -/
def ofEndpoints {α : Type*} [LinearOrder α] (a b c d : α) : Comparisons :=
  ⟨compare a c, compare a d, compare b c, compare b d, compare a b, compare c d⟩

theorem ofEndpoints_eq {α β : Type*} [LinearOrder α] [LinearOrder β] {n : ℕ} {f : Fin n → α}
    {g : Fin n → β} (h : ∀ x y, compare (f x) (f y) = compare (g x) (g y)) (a b c d : Fin n) :
    ofEndpoints (f a) (f b) (f c) (f d) = ofEndpoints (g a) (g b) (g c) (g d) := by
  simp [ofEndpoints, h]

/-- The comparisons read the other way, from the second interval to the first. -/
def Comparisons.swap (c : Comparisons) : Comparisons :=
  ⟨c.fstFst.swap, c.sndFst.swap, c.fstSnd.swap, c.sndSnd.swap, c.secondShape, c.firstShape⟩

@[simp] theorem Comparisons.swap_swap (c : Comparisons) : c.swap.swap = c := by
  simp [Comparisons.swap]

private theorem swap_compare {α : Type*} [LinearOrder α] (a b : α) :
    (compare a b).swap = compare b a :=
  Std.OrientedOrd.eq_swap.symm

@[simp] theorem swap_ofEndpoints {α : Type*} [LinearOrder α] (a b c d : α) :
    (ofEndpoints a b c d).swap = ofEndpoints c d a b := by
  simp [ofEndpoints, Comparisons.swap, swap_compare]

/-- The comparisons that two intervals realize, those of two intervals among four points. -/
def realizable : Finset Comparisons :=
  (Finset.univ : Finset (NonemptyInterval (Fin 4) × NonemptyInterval (Fin 4))).image
    fun p ↦ ofEndpoints p.1.fst p.1.snd p.2.fst p.2.snd

theorem ofEndpoints_mem_realizable {α : Type*} [LinearOrder α] {a b c d : α} (hab : a ≤ b)
    (hcd : c ≤ d) : ofEndpoints a b c d ∈ realizable := by
  obtain ⟨g, hg⟩ := Ordering.exists_fin_compare_eq ![a, b, c, d]
  have hle (x y : Fin 4) (h : ![a, b, c, d] x ≤ ![a, b, c, d] y) : g x ≤ g y :=
    compare_le_iff_le.1 (by rw [hg]; exact compare_le_iff_le.2 h)
  exact Finset.mem_image.2 ⟨(⟨(g 0, g 1), hle 0 1 hab⟩, ⟨(g 2, g 3), hle 2 3 hcd⟩),
    Finset.mem_univ _, ofEndpoints_eq hg 0 1 2 3⟩

theorem Comparisons.swap_mem_realizable {c : Comparisons} (h : c ∈ realizable) :
    c.swap ∈ realizable := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h
  rw [swap_ofEndpoints]
  exact ofEndpoints_mem_realizable p.2.fst_le_snd p.1.fst_le_snd

/-- A relation is how one interval of a linear order stands to another: comparisons among the
endpoints of two intervals that some two intervals realize. -/
structure Relation extends Comparisons where
  /-- Two intervals realize the comparisons. -/
  mem_realizable : toComparisons ∈ realizable

namespace Relation

@[ext] theorem ext {r s : Relation} (h : r.toComparisons = s.toComparisons) : r = s := by
  cases r; cases s; congr

instance : DecidableEq Relation := fun r s ↦
  decidable_of_iff (r.toComparisons = s.toComparisons) ⟨ext, congrArg _⟩

/-- The relations are the realizable comparisons. -/
def equivRealizable : Relation ≃ { c // c ∈ realizable } where
  toFun r := ⟨r.toComparisons, r.mem_realizable⟩
  invFun c := ⟨c.1, c.2⟩

instance : Fintype Relation := Fintype.ofEquiv _ equivRealizable.symm

/-- The converse of a relation: how the second interval stands to the first. -/
def inv (r : Relation) : Relation := ⟨r.swap, Comparisons.swap_mem_realizable r.mem_realizable⟩

@[simp] theorem inv_inv (r : Relation) : r.inv.inv = r := ext (Comparisons.swap_swap _)

end Relation

/-- There are twenty-six relations: Allen's thirteen between proper intervals, five between a
point and a proper interval, five between a proper interval and a point, and three between
points. -/
theorem card_relation : Fintype.card Relation = 26 := by decide +kernel

/-! ### The relation of two intervals -/

section LinearOrder

variable {T : Type*} [LinearOrder T]

/-- The relation of the interval `i` to the interval `j`. -/
def relation (i j : NonemptyInterval T) : Relation :=
  ⟨ofEndpoints i.fst i.snd j.fst j.snd, ofEndpoints_mem_realizable i.fst_le_snd j.fst_le_snd⟩

@[simp] theorem toComparisons_relation (i j : NonemptyInterval T) :
    (relation i j).toComparisons = ofEndpoints i.fst i.snd j.fst j.snd := rfl

/-- The relation of two intervals survives an order embedding. -/
theorem relation_map {β : Type*} [LinearOrder β] (f : T ↪o β) (i j : NonemptyInterval T) :
    relation (i.map f.toOrderHom) (j.map f.toOrderHom) = relation i j := by
  have hf (a b : T) : compare (f a) (f b) = compare a b := by
    rcases lt_trichotomy a b with h | rfl | h
    · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2 (f.lt_iff_lt.2 h)]
    · rw [compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
    · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2 (f.lt_iff_lt.2 h)]
  exact Relation.ext (by simp [ofEndpoints, hf])

/-- The relation of a cell relates an interval to the intervals that stand to it in one of the
cell's relations, as the relation of a comparison cell relates a perspective time to the
reference times its tense allows. -/
def toSetRel (C : Finset Relation) : SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  {p | relation p.2 p.1 ∈ C}

variable {C D : Finset Relation} {i j : NonemptyInterval T}

@[simp] theorem mem_toSetRel : (j, i) ∈ toSetRel C ↔ relation i j ∈ C := .rfl

instance : Decidable ((j, i) ∈ toSetRel C) := inferInstanceAs (Decidable (relation i j ∈ C))

theorem toSetRel_mono (h : C ⊆ D) : (toSetRel C : SetRel (NonemptyInterval T) _) ⊆ toSetRel D :=
  fun _ hp ↦ h hp

end LinearOrder

/-- Every relation is that of two intervals among four points. -/
theorem exists_relation_eq (r : Relation) :
    ∃ i j : NonemptyInterval (Fin 4), relation i j = r := by
  obtain ⟨p, -, h⟩ := Finset.mem_image.1 r.mem_realizable
  exact ⟨p.1, p.2, Relation.ext h⟩

theorem forall_toSetRel_subset_iff {C D : Finset Relation} :
    (∀ (T : Type) [LinearOrder T], (toSetRel C : SetRel (NonemptyInterval T) _) ⊆ toSetRel D) ↔
      C ⊆ D := by
  refine ⟨fun h r hr ↦ ?_, fun h _ _ ↦ toSetRel_mono h⟩
  obtain ⟨i, j, rfl⟩ := exists_relation_eq r
  exact h (Fin 4) (a := (j, i)) hr

/-! ### Converse -/

/-- The converse of a cell. -/
def inv (C : Finset Relation) : Finset Relation := C.image Relation.inv

@[simp] theorem mem_inv {C : Finset Relation} {r : Relation} : r ∈ inv C ↔ r.inv ∈ C :=
  ⟨fun h ↦ by obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h; simpa using hs,
    fun h ↦ Finset.mem_image.2 ⟨r.inv, h, r.inv_inv⟩⟩

@[simp] theorem inv_inv (C : Finset Relation) : inv (inv C) = C := by
  ext r; simp

section LinearOrder

variable {T : Type*} [LinearOrder T]

@[simp] theorem inv_relation (i j : NonemptyInterval T) : (relation i j).inv = relation j i :=
  Relation.ext (swap_ofEndpoints _ _ _ _)

@[simp] theorem toSetRel_inv (C : Finset Relation) :
    (toSetRel (inv C) : SetRel (NonemptyInterval T) _) = (toSetRel C).inv := by
  ext ⟨i, j⟩
  simp

end LinearOrder

/-! ### Composition -/

/-- The composite of two cells: the relations of an interval to a third compatible with its
standing in `C` to a second that stands in `D` to the third, read off the intervals among six
points. The second interval is placed only beside a first that stands in `C` to it, so the kernel
decides composites of the named cells. -/
@[irreducible] def comp (C D : Finset Relation) : Finset Relation :=
  ((Finset.univ : Finset (NonemptyInterval (Fin 6) × NonemptyInterval (Fin 6))).filter
      fun x ↦ relation x.1 x.2 ∈ C).biUnion fun x ↦
    ((Finset.univ : Finset (NonemptyInterval (Fin 6))).filter fun y ↦ relation x.2 y ∈ D).image
      (relation x.1)

theorem mem_comp {C D : Finset Relation} {t : Relation} :
    t ∈ comp C D ↔ ∃ i j k : NonemptyInterval (Fin 6),
      relation i j ∈ C ∧ relation j k ∈ D ∧ relation i k = t := by
  simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists]
  exact ⟨fun ⟨i, j, hC, k, hD, h⟩ ↦ ⟨i, j, k, hC, hD, h⟩,
    fun ⟨i, j, k, hC, hD, h⟩ ↦ ⟨i, j, hC, k, hD, h⟩⟩

section LinearOrder

variable {T : Type*} [LinearOrder T] {C D : Finset Relation}

theorem toSetRel_comp_subset :
    (toSetRel C ○ toSetRel D : SetRel (NonemptyInterval T) _) ⊆ toSetRel (comp D C) := by
  rintro ⟨k, i⟩ ⟨j, hkj, hji⟩
  let f : Fin 6 → T := ![i.fst, i.snd, j.fst, j.snd, k.fst, k.snd]
  obtain ⟨g, hg⟩ := Ordering.exists_fin_compare_eq f
  have hle (a b : Fin 6) (h : f a ≤ f b) : g a ≤ g b :=
    compare_le_iff_le.1 (by rw [hg]; exact compare_le_iff_le.2 h)
  have hr (a b c d : Fin 6) (hab : f a ≤ f b) (hcd : f c ≤ f d) :
      relation ⟨(g a, g b), hle a b hab⟩ ⟨(g c, g d), hle c d hcd⟩ =
        relation ⟨(f a, f b), hab⟩ ⟨(f c, f d), hcd⟩ :=
    Relation.ext (ofEndpoints_eq hg a b c d)
  refine mem_toSetRel.2 <| mem_comp.2 ⟨⟨(g 0, g 1), hle 0 1 i.fst_le_snd⟩,
    ⟨(g 2, g 3), hle 2 3 j.fst_le_snd⟩, ⟨(g 4, g 5), hle 4 5 k.fst_le_snd⟩, ?_, ?_,
    hr 0 1 4 5 i.fst_le_snd k.fst_le_snd⟩
  · rw [hr 0 1 2 3 i.fst_le_snd j.fst_le_snd]; exact mem_toSetRel.1 hji
  · rw [hr 2 3 4 5 j.fst_le_snd k.fst_le_snd]; exact mem_toSetRel.1 hkj

/-- On dense time without endpoints, the composite of two cells' relations is the relation of
the composite cell: the middle interval of a configuration of endpoints can be placed between any
two intervals that stand as its outer ones do. -/
theorem toSetRel_comp [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] :
    (toSetRel C ○ toSetRel D : SetRel (NonemptyInterval T) _) = toSetRel (comp D C) := by
  refine le_antisymm toSetRel_comp_subset (fun ⟨k, i⟩ h ↦ ?_)
  have : Nonempty T := ⟨i.fst⟩
  obtain ⟨I, J, K, hD, hC, hik⟩ := mem_comp.1 (mem_toSetRel.1 h)
  -- the endpoints of `i` and `k`, then those of the interval to be placed
  let q : Fin 6 → Fin 6 := ![I.fst, I.snd, K.fst, K.snd, J.fst, J.snd]
  have hq : ∀ x y : Fin 4, compare (![i.fst, i.snd, k.fst, k.snd] x) (![i.fst, i.snd, k.fst,
      k.snd] y) = compare (q (x.castSucc.castSucc)) (q (y.castSucc.castSucc)) := by
    have hik' := congrArg Relation.toComparisons hik
    simp only [toComparisons_relation, ofEndpoints, Comparisons.mk.injEq] at hik'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hik'
    have r {a b : Fin 6} {c d : T} (h : compare a b = compare c d) :
        compare b a = compare d c := by rw [← swap_compare, h, swap_compare]
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [q, h1, h2, h3, h4, h5, h6, r h1, r h2, r h3, r h4, r h5, r h6]
  obtain ⟨a, ha⟩ := Ordering.exists_snoc_compare_eq (q := fun x : Fin 5 ↦ q x.castSucc) hq
  obtain ⟨b, hb⟩ := Ordering.exists_snoc_compare_eq (q := q) (p := Fin.snoc
    (α := fun _ ↦ T) ![i.fst, i.snd, k.fst, k.snd] a) ha
  have hab : a ≤ b := compare_le_iff_le.1 (by
    have := hb 4 5
    simp [Fin.snoc, q] at this
    simpa [this] using compare_le_iff_le.2 J.fst_le_snd)
  refine ⟨⟨(a, b), hab⟩, mem_toSetRel.2 ?_, mem_toSetRel.2 ?_⟩
  · have := ofEndpoints_eq hb 4 5 2 3
    simp [Fin.snoc, q] at this
    exact (Relation.ext this : relation ⟨(a, b), hab⟩ k = relation J K) ▸ hC
  · have := ofEndpoints_eq hb 0 1 4 5
    simp [Fin.snoc, q] at this
    exact (Relation.ext this : relation i ⟨(a, b), hab⟩ = relation I J) ▸ hD

/-- The image under one cell of the image under another lies in the image under their composite,
so a complex aspect relates its outer interval to the run time as the composite cell says. -/
theorem image_toSetRel_subset_comp (s : Set (NonemptyInterval T)) :
    (toSetRel C).image ((toSetRel D).image s) ⊆ (toSetRel (comp C D)).image s := by
  rw [← SetRel.image_comp]
  exact fun _ ⟨k, hk, hik⟩ ↦ ⟨k, hk, toSetRel_comp_subset hik⟩

theorem image_toSetRel_comp [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T]
    (s : Set (NonemptyInterval T)) :
    (toSetRel C).image ((toSetRel D).image s) = (toSetRel (comp C D)).image s := by
  rw [← SetRel.image_comp, toSetRel_comp]

end LinearOrder

/-! ### Named cells -/

/-- The first interval ends before the second starts. -/
@[irreducible]
def precedes : Finset Relation := Finset.univ.filter (·.sndFst = .lt)

/-- The first interval ends no later than the second starts. -/
@[irreducible]
def isBefore : Finset Relation := Finset.univ.filter (·.sndFst ≠ .gt)

/-- The first interval lies within the second. -/
@[irreducible]
def le : Finset Relation := Finset.univ.filter fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd ≠ .gt

/-- The first interval lies within the second and is not the whole of it. -/
@[irreducible]
def lt : Finset Relation := le.filter fun r ↦ r.fstFst = .gt ∨ r.sndSnd = .lt

/-- The two intervals overlap. -/
@[irreducible]
def overlaps : Finset Relation := Finset.univ.filter fun r ↦ r.fstSnd ≠ .gt ∧ r.sndFst ≠ .lt

/-- The first interval starts within the second. -/
@[irreducible]
def startsWithin : Finset Relation := Finset.univ.filter fun r ↦ r.fstFst ≠ .lt ∧ r.fstSnd ≠ .gt

/-- The first interval lies within the second and ends with it. -/
@[irreducible]
def finalSubinterval : Finset Relation := Finset.univ.filter fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd = .eq

/-- The first interval lies within the second and ends before it. -/
@[irreducible]
def nonfinalSubinterval : Finset Relation :=
  Finset.univ.filter fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd = .lt

theorem comp_precedes_precedes : comp precedes precedes = precedes := by decide +kernel

/-- The position of the first interval relative to the second: before it, after it, or
overlapping it. -/
def Relation.position (r : Relation) : Ordering :=
  if r.sndFst = .lt then .lt else if r.fstSnd = .gt then .gt else .eq

section LinearOrder

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

theorem position_relation (i j : NonemptyInterval T) :
    i.position j = (relation i j).position := by
  simp only [NonemptyInterval.position, Relation.position, relation, ofEndpoints,
    NonemptyInterval.Precedes, compare_lt_iff_lt, compare_gt_iff_gt]
  split_ifs <;> rfl

end LinearOrder

/-- The cell of the relations whose position is one of `C`. -/
@[irreducible]
def ofPosition (C : Finset Ordering) : Finset Relation := Finset.univ.filter (·.position ∈ C)

theorem ofPosition_eq : ofPosition {.eq} = overlaps := by decide +kernel

theorem ofPosition_lt : ofPosition {.lt} = precedes := by decide +kernel

section LinearOrder

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

theorem relation_mem_filter {p : Relation → Prop} [DecidablePred p] :
    relation i j ∈ Finset.univ.filter p ↔ p (relation i j) := by
  simp

@[simp] theorem relation_mem_precedes : relation i j ∈ precedes ↔ i.Precedes j := by
  rw [precedes, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.Precedes, compare_lt_iff_lt]

@[simp] theorem relation_mem_isBefore : relation i j ∈ isBefore ↔ i.snd ≤ j.fst := by
  rw [isBefore, relation_mem_filter]
  simp [relation, ofEndpoints, compare_le_iff_le]

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

@[simp] theorem relation_mem_finalSubinterval :
    relation i j ∈ finalSubinterval ↔ i.FinalSubinterval j := by
  rw [finalSubinterval, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.FinalSubinterval, compare_lt_iff_lt]

@[simp] theorem relation_mem_nonfinalSubinterval :
    relation i j ∈ nonfinalSubinterval ↔ i.NonfinalSubinterval j := by
  rw [nonfinalSubinterval, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.NonfinalSubinterval, compare_lt_iff_lt]

@[simp] theorem relation_mem_ofPosition {C : Finset Ordering} :
    relation i j ∈ ofPosition C ↔ i.position j ∈ C := by
  rw [ofPosition, relation_mem_filter, position_relation]

/-- On dense time the precedence of a precedence is a precedence. -/
theorem toSetRel_precedes_comp_self [DenselyOrdered T] :
    (toSetRel precedes ○ toSetRel precedes : SetRel (NonemptyInterval T) _) =
      toSetRel precedes := by
  ext ⟨π, r⟩
  simp only [SetRel.mem_comp, mem_toSetRel, relation_mem_precedes]
  exact ⟨fun ⟨_, h₁, h₂⟩ ↦ NonemptyInterval.precedes_trans h₂ h₁,
    fun h ↦ let ⟨u, hu, hu'⟩ := exists_between h; ⟨.pure u, hu', hu⟩⟩

end LinearOrder

/-! ### Points

The comparison cells of the tenses are the cells of point intervals. -/

/-- The two intervals are the same. -/
@[irreducible]
def eq : Finset Relation := Finset.univ.filter fun r ↦ r.fstFst = .eq ∧ r.sndSnd = .eq

/-- The cell of point intervals whose points compare as `C` allows. -/
@[irreducible]
def pure (C : Finset Ordering) : Finset Relation :=
  Finset.univ.filter fun r ↦ r.firstShape = .eq ∧ r.secondShape = .eq ∧ r.fstFst ∈ C

section LinearOrder

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

@[simp] theorem relation_mem_eq : relation i j ∈ eq ↔ i = j := by
  rw [eq, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.ext_iff, Prod.ext_iff]

@[simp] theorem relation_mem_pure {C : Finset Ordering} :
    relation i j ∈ pure C ↔ i.IsPoint ∧ j.IsPoint ∧ compare i.fst j.fst ∈ C := by
  rw [pure, relation_mem_filter]
  simp [relation, ofEndpoints, NonemptyInterval.IsPoint]

end LinearOrder

private theorem exists_fin_of_mem_comp :
    ∀ r s o : Ordering, o ∈ r.comp s →
      ∃ x y z : Fin 6, compare x y = r ∧ compare y z = s ∧ compare x z = o := by
  decide

private theorem toComparisons_eq_of_shapes :
    ∀ t : Relation, t.firstShape = .eq → t.secondShape = .eq →
      t.toComparisons = ⟨t.fstFst, t.fstFst, t.fstFst, t.fstFst, .eq, .eq⟩ := by
  decide +kernel

/-- On points, Allen composition is the composition of comparison cells. -/
theorem comp_pure (R S : Finset Ordering) : comp (pure R) (pure S) = pure (Tense.comp R S) := by
  ext t
  simp only [mem_comp, pure, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, j, k, ⟨h1, -, hR⟩, ⟨-, h2, hS⟩, rfl⟩
    exact ⟨h1, h2, Tense.compare_mem_comp hR hS⟩
  · rintro ⟨h1, h2, hc⟩
    obtain ⟨r, hr, s, hs, ho⟩ := Tense.mem_comp.1 hc
    obtain ⟨x, y, z, hxy, hyz, hxz⟩ := exists_fin_of_mem_comp r s _ ho
    have hself (a : Fin 6) : compare a a = .eq := compare_eq_iff_eq.2 rfl
    refine ⟨.pure x, .pure y, .pure z, ⟨hself x, hself y, show compare x y ∈ R from hxy ▸ hr⟩,
      ⟨hself y, hself z, show compare y z ∈ S from hyz ▸ hs⟩, Relation.ext ?_⟩
    rw [toComparisons_eq_of_shapes t h1 h2]
    simp [ofEndpoints, hxz]

/-! ### Chains

A clause's times form a chain, each related to the one before it by a head's cell. -/

section LinearOrder

variable {T : Type*} [LinearOrder T]

/-- The intervals `tos` stand along the cells `cs` from `b`: the first stands to `b` as the first
cell says, and each later one to the one before it as the next cell says. -/
def HoldsAlong : List (Finset Relation) → NonemptyInterval T → List (NonemptyInterval T) → Prop
  | [], _, [] => True
  | C :: cs, y, x :: xs => (y, x) ∈ toSetRel C ∧ HoldsAlong cs x xs
  | _, _, _ => False

instance instDecidableHoldsAlong :
    ∀ (cs : List (Finset Relation)) (b : NonemptyInterval T) tos,
      Decidable (HoldsAlong cs b tos)
  | [], _, [] => isTrue trivial
  | [], _, _ :: _ => isFalse id
  | _ :: _, _, [] => isFalse id
  | C :: cs, y, x :: xs =>
    have := instDecidableHoldsAlong cs x xs
    inferInstanceAs (Decidable ((y, x) ∈ toSetRel C ∧ HoldsAlong cs x xs))

end LinearOrder

/-- The composite of a chain of cells, how its last time stands to its first. -/
def compAlong : List (Finset Relation) → Finset Relation
  | [] => eq
  | C :: cs => comp (compAlong cs) C

section LinearOrder

variable {T : Type*} [LinearOrder T]

theorem HoldsAlong.mem_compAlong :
    ∀ {cs : List (Finset Relation)} {b : NonemptyInterval T} {tos : List (NonemptyInterval T)},
      HoldsAlong cs b tos →
        (b, (b :: tos).getLast (List.cons_ne_nil _ _)) ∈ toSetRel (compAlong cs)
  | [], b, [], _ => by simp [compAlong]
  | C :: cs, b, x :: xs, ⟨hx, h⟩ => by
    rw [compAlong, List.getLast_cons (List.cons_ne_nil _ _)]
    exact toSetRel_comp_subset (SetRel.mem_comp.2 ⟨x, hx, h.mem_compAlong⟩)

/-- On dense time without endpoints, two times stand in a chain's composite exactly when the chain
can be realized from the first to the second. -/
theorem mem_compAlong_iff [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] :
    ∀ {cs : List (Finset Relation)} {b x : NonemptyInterval T},
      (b, x) ∈ toSetRel (compAlong cs) ↔
        ∃ tos, HoldsAlong cs b tos ∧ (b :: tos).getLast (List.cons_ne_nil _ _) = x
  | [], b, x => by
    rw [compAlong, mem_toSetRel, relation_mem_eq]
    refine ⟨fun h ↦ ⟨[], trivial, h.symm⟩, ?_⟩
    rintro ⟨_ | _, h, rfl⟩
    · rfl
    · exact absurd h id
  | C :: cs, b, x => by
    refine ⟨fun h ↦ ?_, fun ⟨tos, h, hx⟩ ↦ hx ▸ h.mem_compAlong⟩
    rw [compAlong, ← toSetRel_comp] at h
    obtain ⟨j, hbj, hjx⟩ := h
    obtain ⟨tos, htos, rfl⟩ := mem_compAlong_iff.1 hjx
    exact ⟨j :: tos, ⟨hbj, htos⟩, by simp⟩

end LinearOrder

end Allen
