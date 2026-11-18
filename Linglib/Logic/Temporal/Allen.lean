module

public import Linglib.Core.Order.Compare
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Core.Order.Interval.Fintype
public import Mathlib.Order.CountableDenseLinearOrder
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
recorded as the [comparisons](##Allen.Comparisons) among them, and the
[relations](##Allen.Relation) are the comparisons that two intervals realize,
[twenty-six](##Allen.card_relation) in all. The [relation of two intervals](##Allen.relation)
[survives an order embedding](##Allen.relation_map), and two pairs of intervals stand in the same
relation exactly when a partial isomorphism pairs their endpoints.

## Implementation notes

A relation records whether each interval is a point; with the four cross comparisons alone
composition is not exact.

## References

* [allen-1983]
-/

@[expose] public section

namespace Allen


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

/-- The comparisons on reversed time, where each interval's end is its start. -/
def Comparisons.dual (c : Comparisons) : Comparisons :=
  ⟨c.sndSnd.swap, c.sndFst.swap, c.fstSnd.swap, c.fstFst.swap, c.firstShape, c.secondShape⟩

@[simp] theorem Comparisons.dual_dual (c : Comparisons) : c.dual.dual = c := by
  simp [Comparisons.dual]

private theorem compare_toDual {α : Type*} [LinearOrder α] (a b : α) :
    compare (OrderDual.toDual a) (OrderDual.toDual b) = compare b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact (compare_gt_iff_gt.2 (OrderDual.toDual_lt_toDual.2 h)).trans (compare_gt_iff_gt.2 h).symm
  · rw [compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
  · exact (compare_lt_iff_lt.2 (OrderDual.toDual_lt_toDual.2 h)).trans (compare_lt_iff_lt.2 h).symm

@[simp] theorem dual_ofEndpoints {α : Type*} [LinearOrder α] (a b c d : α) :
    (ofEndpoints a b c d).dual =
      ofEndpoints (OrderDual.toDual b) (OrderDual.toDual a) (OrderDual.toDual d)
        (OrderDual.toDual c) := by
  simp [ofEndpoints, Comparisons.dual, swap_compare, compare_toDual]

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

theorem Comparisons.dual_mem_realizable {c : Comparisons} (h : c ∈ realizable) :
    c.dual ∈ realizable := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h
  rw [dual_ofEndpoints]
  exact ofEndpoints_mem_realizable (OrderDual.toDual_le_toDual.2 p.1.fst_le_snd)
    (OrderDual.toDual_le_toDual.2 p.2.fst_le_snd)

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

/-- The relation on reversed time: how the first interval stands to the second when earlier and
later are exchanged. -/
def dual (r : Relation) : Relation := ⟨r.toComparisons.dual, r.dual_mem_realizable r.mem_realizable⟩

@[simp] theorem dual_dual (r : Relation) : r.dual.dual = r := ext (Comparisons.dual_dual _)

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

end LinearOrder

/-- Every relation is that of two intervals among four points. -/
theorem exists_relation_eq (r : Relation) :
    ∃ i j : NonemptyInterval (Fin 4), relation i j = r := by
  obtain ⟨p, -, h⟩ := Finset.mem_image.1 r.mem_realizable
  exact ⟨p.1, p.2, Relation.ext h⟩


section LinearOrder

variable {T : Type*} [LinearOrder T]

@[simp] theorem inv_relation (i j : NonemptyInterval T) : (relation i j).inv = relation j i :=
  Relation.ext (swap_ofEndpoints _ _ _ _)

@[simp] theorem dual_relation (i j : NonemptyInterval T) :
    (relation i j).dual = relation i.dual j.dual :=
  Relation.ext (dual_ofEndpoints _ _ _ _)

end LinearOrder

/-! ### Partial isomorphisms

Mathlib's `Order.PartialIso` pairs finitely many points of two linear orders that compare alike,
so intervals whose endpoints it pairs stand in the same relation. -/

section PartialIso

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Intervals whose endpoints a partial isomorphism pairs stand in the same relation. -/
theorem relation_eq_of_mem_partialIso (f : Order.PartialIso α β) {I J : NonemptyInterval α}
    {i j : NonemptyInterval β} (h₁ : (I.fst, i.fst) ∈ f.val) (h₂ : (I.snd, i.snd) ∈ f.val)
    (h₃ : (J.fst, j.fst) ∈ f.val) (h₄ : (J.snd, j.snd) ∈ f.val) : relation I J = relation i j := by
  have h {a c : α} {b d : β} (hp : (a, b) ∈ f.val) (hq : (c, d) ∈ f.val) :
      compare a c = compare b d := by
    simpa only [cmp_eq_compare] using f.prop _ hp _ hq
  exact Relation.ext (by
    simp only [toComparisons_relation, ofEndpoints, h h₁ h₃, h h₁ h₄, h h₂ h₃, h h₂ h₄, h h₁ h₂,
      h h₃ h₄])

/-- Two pairs of intervals in the same relation have their endpoints paired by a partial
isomorphism. -/
theorem exists_partialIso_of_relation_eq {I K : NonemptyInterval α} {i k : NonemptyInterval β}
    (h : relation I K = relation i k) :
    ∃ f : Order.PartialIso α β, (I.fst, i.fst) ∈ f.val ∧ (I.snd, i.snd) ∈ f.val ∧
      (K.fst, k.fst) ∈ f.val ∧ (K.snd, k.snd) ∈ f.val := by
  have h' := congrArg Relation.toComparisons h
  simp only [toComparisons_relation, ofEndpoints, Comparisons.mk.injEq, ← cmp_eq_compare] at h'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h'
  have r {a b : α} {c d : β} (h : cmp a b = cmp c d) : cmp b a = cmp d c := by
    rw [← cmp_swap, h, cmp_swap]
  refine ⟨⟨{(I.fst, i.fst), (I.snd, i.snd), (K.fst, k.fst), (K.snd, k.snd)}, ?_⟩,
    by simp, by simp, by simp, by simp⟩
  intro p hp q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    simp [h1, h2, h3, h4, h5, h6, r h1, r h2, r h3, r h4, r h5, r h6]

end PartialIso

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

end Allen
