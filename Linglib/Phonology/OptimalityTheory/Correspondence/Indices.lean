/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Fin.Basic

/-!
# Correspondence by coindexation

Correspondent segments are written with matching subscripted indices: /p₁a₂t₃/ and [p₁a₂t₃],
a coalesced segment bearing the indices of both its sources. Here a segment carries its
indices, and two segments [correspond](##OptimalityTheory.Correspondence.Segment.Corresponds)
when they share one. The positions of two strings that correspond form
[a correspondence](##OptimalityTheory.Correspondence.ofIndices), whose converse is that of the
two strings [exchanged](##OptimalityTheory.Correspondence.inv_ofIndices), and each faithfulness
constraint is a count over the two strings
[equal to that on the correspondence](##OptimalityTheory.Correspondence.Segment.maxViolOn_eq).

## Implementation notes

* In the sources a candidate comes with a correspondence relation, and indices notate it. Here
  the indices are the data and the relation is derived, so that one indexing of the strings of a
  candidate gives the relation between every two of them, symmetric by construction.
* A correspondence index is a natural number and has nothing to do with the position of a
  segment in its string.
* MAX, DEP, IDENT, INTEGRITY and UNIFORMITY are counts over lists. The constraints that read the
  order of positions (LINEARITY, CONTIGUITY, ANCHOR) are those of the derived correspondence.

## TODO

* Within one string a segment shares its own indices, so a constraint on the correspondence of a
  string with itself must set aside each segment's correspondence with itself.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [benua-1997]
* [rose-walker-2004]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

/-- A segment with the correspondence indices it bears. -/
structure Segment (α : Type*) where
  seg : α
  indices : List ℕ
  deriving DecidableEq, Repr

variable {α F : Type*}

namespace Segment

/-- Two segments *correspond* when they share an index. -/
def Corresponds (x y : Segment α) : Prop := ∃ k ∈ x.indices, k ∈ y.indices

instance (x y : Segment α) : Decidable (x.Corresponds y) :=
  inferInstanceAs (Decidable (∃ k ∈ x.indices, k ∈ y.indices))

theorem Corresponds.symm {x y : Segment α} (h : x.Corresponds y) : y.Corresponds x :=
  let ⟨k, hx, hy⟩ := h; ⟨k, hy, hx⟩

theorem corresponds_comm {x y : Segment α} : x.Corresponds y ↔ y.Corresponds x :=
  ⟨.symm, .symm⟩

end Segment

/-- The correspondence between the positions of two strings. -/
def ofIndices (s t : List (Segment α)) : Correspondence (Fin s.length) (Fin t.length) :=
  Finset.univ.filter fun p ↦ s[p.1].Corresponds t[p.2]

variable {s t : List (Segment α)}

@[simp] theorem mem_ofIndices {i : Fin s.length} {j : Fin t.length} :
    (i, j) ∈ ofIndices s t ↔ s[i].Corresponds t[j] := by
  simp [ofIndices]

@[simp] theorem inv_ofIndices (s t : List (Segment α)) :
    (ofIndices s t).inv = ofIndices t s := by
  ext ⟨j, i⟩
  simp [Segment.corresponds_comm]

end OptimalityTheory.Correspondence

namespace OptimalityTheory.Correspondence.Segment

variable {α F : Type*}

variable (P : α → Prop) [DecidablePred P] (s t : List (Segment α))

/-! ### MAX and DEP -/

/-- MAX restricted to the segments satisfying `P` counts those of `s` without a correspondent
in `t`. -/
def maxViolOn : ℕ := s.countP fun x ↦ P x.seg ∧ ∀ y ∈ t, ¬ x.Corresponds y

/-- MAX counts the segments of `s` without a correspondent in `t`. -/
def maxViol : ℕ := s.countP fun x ↦ ∀ y ∈ t, ¬ x.Corresponds y

/-- MAX restricted to the positions satisfying `P` counts those of `s` whose segment has no
correspondent in `t`, the form of a positional faithfulness constraint. -/
def maxViolAt (P : ℕ → Prop) [DecidablePred P] (s t : List (Segment α)) : ℕ :=
  s.zipIdx.countP fun x ↦ P x.2 ∧ ∀ y ∈ t, ¬ x.1.Corresponds y

/-- DEP restricted to the positions of `t` satisfying `P`. -/
def depViolAt (P : ℕ → Prop) [DecidablePred P] (s t : List (Segment α)) : ℕ := maxViolAt P t s

theorem maxViolAt_true : maxViolAt (fun _ ↦ True) s t = maxViol s t := by
  rw [maxViol, maxViolAt]
  conv_rhs => rw [← List.zipIdx_map_fst 0 s, List.countP_map]
  exact List.countP_congr fun x _ ↦ by simp

/-- DEP restricted to the segments satisfying `P` counts those of `t` without a correspondent
in `s`. -/
def depViolOn : ℕ := maxViolOn P t s

/-- DEP counts the segments of `t` without a correspondent in `s`. -/
def depViol : ℕ := maxViol t s

/-! ### IDENT -/

/-- IDENT for the feature `f` counts the corresponding pairs that differ under `f`. -/
def identViol [DecidableEq F] (f : α → F) (s t : List (Segment α)) : ℕ :=
  (s.map fun x ↦ t.countP fun y ↦ x.Corresponds y ∧ f x.seg ≠ f y.seg).sum

/-- MAX of a privative property counts the corresponding pairs whose first member has it and
whose second lacks it. -/
def maxViolFeature : ℕ :=
  (s.map fun x ↦ t.countP fun y ↦ x.Corresponds y ∧ P x.seg ∧ ¬ P y.seg).sum

/-- DEP of a privative property counts the corresponding pairs whose second member has it and
whose first lacks it. -/
def depViolFeature : ℕ := maxViolFeature P t s

/-! ### INTEGRITY and UNIFORMITY -/

/-- INTEGRITY counts the segments of `s` with more than one correspondent in `t`. -/
def integrityViol : ℕ := s.countP fun x ↦ 1 < t.countP (x.Corresponds ·)

/-- UNIFORMITY counts the segments of `t` with more than one correspondent in `s`. -/
def uniformityViol : ℕ := integrityViol t s

/-! ### The counts on the derived correspondence -/

/-- A count over a list is the number of its positions whose element is counted. -/
private theorem countP_eq_card_filter_getElem {β : Type*} (l : List β) (p : β → Prop)
    [DecidablePred p] :
    l.countP (p ·) = (Finset.univ.filter fun i : Fin l.length ↦ p l[i]).card := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [← Multiset.coe_countP, ← Fin.univ_val_map, Multiset.countP_map, Finset.card_def,
    Finset.filter_val]
  rfl

/-- A sum of counts over two lists is the number of pairs of positions counted. -/
private theorem sum_map_countP_eq_card_filter {β γ : Type*} (l₁ : List β) (l₂ : List γ)
    (q : β → γ → Prop) [∀ x y, Decidable (q x y)] :
    (l₁.map fun x ↦ l₂.countP fun y ↦ q x y).sum =
      (Finset.univ.filter fun p : Fin l₁.length × Fin l₂.length ↦ q l₁[p.1] l₂[p.2]).card := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (countP_eq_card_filter_getElem l₂ fun y ↦ q l₁[(i : ℕ)] y).trans (Finset.card_filter _ _)

private theorem mem_image_fst_ofIndices {i : Fin s.length} :
    i ∈ (ofIndices s t).image Prod.fst ↔ ∃ y ∈ t, s[i].Corresponds y := by
  simp only [Finset.mem_image, Prod.exists, mem_ofIndices, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨j, h⟩ ↦ ⟨t[j], List.getElem_mem _, h⟩,
    fun ⟨y, hy, h⟩ ↦ let ⟨j, hj, e⟩ := List.getElem_of_mem hy; ⟨⟨j, hj⟩, e ▸ h⟩⟩

theorem maxViolOn_eq :
    maxViolOn P s t = (ofIndices s t).maxViolOn fun i ↦ P s[i].seg := by
  rw [maxViolOn, Correspondence.maxViolOn,
    countP_eq_card_filter_getElem s fun x ↦ P x.seg ∧ ∀ y ∈ t, ¬ x.Corresponds y]
  congr 1
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_image_fst_ofIndices, not_exists, not_and]

theorem maxViol_eq : maxViol s t = (ofIndices s t).maxViol := by
  rw [maxViol, Correspondence.maxViol,
    countP_eq_card_filter_getElem s fun x ↦ ∀ y ∈ t, ¬ x.Corresponds y]
  congr 1
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_image_fst_ofIndices, not_exists, not_and]

theorem depViolOn_eq :
    depViolOn P s t = (ofIndices s t).depViolOn fun j ↦ P t[j].seg := by
  rw [depViolOn, maxViolOn_eq, ← inv_ofIndices, Correspondence.depViolOn]

theorem depViol_eq : depViol s t = (ofIndices s t).depViol := by
  rw [depViol, maxViol_eq, ← inv_ofIndices, Correspondence.depViol]

theorem identViol_eq [DecidableEq F] (f : α → F) :
    identViol f s t =
      (ofIndices s t).identViol (fun i ↦ f s[i].seg) fun j ↦ f t[j].seg := by
  rw [identViol, Correspondence.identViol, ofIndices, Finset.filter_filter]
  exact sum_map_countP_eq_card_filter s t fun x y ↦ x.Corresponds y ∧ f x.seg ≠ f y.seg

theorem maxViolFeature_eq :
    maxViolFeature P s t =
      (ofIndices s t).maxViolFeature (fun i ↦ P s[i].seg) fun j ↦ P t[j].seg := by
  rw [maxViolFeature, Correspondence.maxViolFeature, ofIndices, Finset.filter_filter]
  exact sum_map_countP_eq_card_filter s t fun x y ↦ x.Corresponds y ∧ P x.seg ∧ ¬ P y.seg

theorem integrityViol_eq : integrityViol s t = (ofIndices s t).integrityViol := by
  rw [integrityViol, Correspondence.integrityViol,
    countP_eq_card_filter_getElem s fun x ↦ 1 < t.countP (x.Corresponds ·)]
  congr 1
  ext i
  have h : (ofIndices s t).filter (fun x ↦ x.1 = i) =
      (Finset.univ.filter fun j : Fin t.length ↦ s[i].Corresponds t[j]).map
        ⟨fun j ↦ (i, j), fun _ _ h ↦ congrArg Prod.snd h⟩ := by
    ext ⟨a, j⟩
    simp only [Finset.mem_filter, mem_ofIndices, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨h, e⟩ ↦ ⟨j, e ▸ h, e.symm, rfl⟩, fun ⟨_, h, e, e'⟩ ↦ e ▸ e' ▸ ⟨h, rfl⟩⟩
  rw [Finset.mem_filter, Finset.mem_filter, h, Finset.card_map,
    countP_eq_card_filter_getElem t fun y ↦ s[i].Corresponds y]

theorem uniformityViol_eq : uniformityViol s t = (ofIndices s t).uniformityViol := by
  rw [uniformityViol, integrityViol_eq, ← inv_ofIndices, Correspondence.uniformityViol]

end OptimalityTheory.Correspondence.Segment

namespace OptimalityTheory.Correspondence

variable {α F : Type*}

/-! ### Indexings -/

/-- The segment `a` bearing the index `k`. -/
def Segment.ofIndex (a : α) (k : ℕ) : Segment α := ⟨a, [k]⟩

/-- The string `l` with each segment indexed by its position. -/
def indexed (l : List α) : List (Segment α) :=
  l.zipIdx.map fun x ↦ .ofIndex x.1 x.2

@[simp] theorem map_seg_indexed (l : List α) : (indexed l).map (·.seg) = l := by
  rw [indexed, List.map_map]
  conv_rhs => rw [← List.zipIdx_map_fst 0 l]
  rfl

@[simp] theorem length_indexed (l : List α) : (indexed l).length = l.length := by
  simp [indexed]

@[simp] theorem Segment.seg_ofIndex (a : α) (k : ℕ) : (Segment.ofIndex a k).seg = a := rfl

@[simp] theorem Segment.corresponds_ofIndex {a b : α} {i j : ℕ} :
    (Segment.ofIndex a i).Corresponds (.ofIndex b j) ↔ i = j := by
  simp [Segment.Corresponds, Segment.ofIndex]

/-- The pairs of corresponding segments of two strings indexed from `k` that stand in `q` are
the pairs of the two strings zipped that do. -/
private theorem sum_countP_zipIdx (q : α → α → Prop) [∀ a b, Decidable (q a b)] (s t : List α)
    (k : ℕ) :
    (((s.zipIdx k).map fun x ↦ Segment.ofIndex x.1 x.2).map fun x ↦
      ((t.zipIdx k).map fun y ↦ Segment.ofIndex y.1 y.2).countP fun y ↦
        x.Corresponds y ∧ q x.seg y.seg).sum = (s.zip t).countP fun p ↦ q p.1 p.2 := by
  induction s generalizing t k with
  | nil => simp
  | cons a s ih =>
    cases t with
    | nil =>
      rw [List.zip_nil_right]
      exact List.sum_eq_zero fun n hn ↦ by
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hn
        simp
    | cons b t =>
      have h₁ : ((t.zipIdx (k + 1)).map fun y ↦ Segment.ofIndex y.1 y.2).countP
          (fun y ↦ (Segment.ofIndex a k).Corresponds y ∧ q (Segment.ofIndex a k).seg y.seg) = 0 :=
        List.countP_eq_zero.2 fun y hy ↦ by
          obtain ⟨⟨c, j⟩, hj, rfl⟩ := List.mem_map.1 hy
          have := (List.mem_zipIdx hj).1
          simp only [Segment.corresponds_ofIndex, decide_eq_true_eq, not_and]
          omega
      have h₂ : ∀ x ∈ (s.zipIdx (k + 1)).map fun x ↦ Segment.ofIndex x.1 x.2,
          ((Segment.ofIndex b k :: (t.zipIdx (k + 1)).map fun y ↦ Segment.ofIndex y.1 y.2).countP
            fun y ↦ x.Corresponds y ∧ q x.seg y.seg) =
          ((t.zipIdx (k + 1)).map fun y ↦ Segment.ofIndex y.1 y.2).countP
            fun y ↦ x.Corresponds y ∧ q x.seg y.seg := fun x hx ↦ by
        obtain ⟨⟨c, j⟩, hj, rfl⟩ := List.mem_map.1 hx
        have := (List.mem_zipIdx hj).1
        rw [List.countP_cons_of_neg]
        simp only [Segment.corresponds_ofIndex, decide_eq_true_eq, not_and]
        omega
      simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.zip_cons_cons]
      rw [List.map_congr_left h₂, ih t (k + 1), List.countP_cons, List.countP_cons, h₁]
      simp [add_comm]

theorem maxViolFeature_indexed (P : α → Prop) [DecidablePred P] (s t : List α) :
    Segment.maxViolFeature P (indexed s) (indexed t) =
      (s.zip t).countP fun p ↦ P p.1 ∧ ¬ P p.2 :=
  sum_countP_zipIdx (fun a b ↦ P a ∧ ¬ P b) s t 0

theorem depViolFeature_indexed (P : α → Prop) [DecidablePred P] (s t : List α) :
    Segment.depViolFeature P (indexed s) (indexed t) =
      (s.zip t).countP fun p ↦ ¬ P p.1 ∧ P p.2 := by
  rw [Segment.depViolFeature, maxViolFeature_indexed, ← List.zip_swap, List.countP_map]
  exact List.countP_congr fun p _ ↦ by simp [and_comm]

theorem identViol_indexed [DecidableEq F] (f : α → F) (s t : List α) :
    Segment.identViol f (indexed s) (indexed t) = (s.zip t).countP fun p ↦ f p.1 ≠ f p.2 :=
  sum_countP_zipIdx (fun a b ↦ f a ≠ f b) s t 0

/-- In a string indexed by position a segment corresponds with itself alone. -/
theorem eq_of_corresponds_indexed {l : List α} {x y : Segment α} (hx : x ∈ indexed l)
    (hy : y ∈ indexed l) (h : x.Corresponds y) : x = y := by
  obtain ⟨⟨a, i⟩, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨⟨b, j⟩, hb, rfl⟩ := List.mem_map.1 hy
  obtain rfl : i = j := by simpa [Segment.Corresponds, Segment.ofIndex] using h
  rw [List.mem_zipIdx_iff_getElem?] at ha hb
  rw [Option.some.inj (ha.symm.trans hb)]

/-- A string indexed by position is identical to itself in every feature. -/
theorem identViol_indexed_self [DecidableEq F] (f : α → F) (l : List α) :
    Segment.identViol f (indexed l) (indexed l) = 0 := by
  refine List.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
  exact List.countP_eq_zero.2 fun y hy ↦ by
    simpa using fun h ↦ congrArg (fun z ↦ f z.seg) (eq_of_corresponds_indexed hx hy h)

theorem maxViolFeature_indexed_self (P : α → Prop) [DecidablePred P] (l : List α) :
    Segment.maxViolFeature P (indexed l) (indexed l) = 0 := by
  refine List.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
  exact List.countP_eq_zero.2 fun y hy ↦ by
    simpa using fun h hP ↦ eq_of_corresponds_indexed hx hy h ▸ hP

/-- A string corresponds with itself, indexed by position, without a MAX violation. -/
theorem maxViol_indexed_self (l : List α) : Segment.maxViol (indexed l) (indexed l) = 0 := by
  rw [Segment.maxViol, List.countP_eq_zero]
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  simpa using ⟨_, hx, a.2, List.mem_singleton_self _, List.mem_singleton_self _⟩

end OptimalityTheory.Correspondence
