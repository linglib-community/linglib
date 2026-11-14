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
a coalesced segment bearing the indices of both its sources, and each correspondence relation
(input–output, base–reduplicant, output–output, the correspondence among the consonants of an
output) its own set of subscripts. Here a segment carries its indices on each relation, and two
segments [correspond](##OptimalityTheory.Correspondence.Segment.Corresponds) on a relation when
they share an index there. The positions of two strings that correspond form
[a correspondence](##OptimalityTheory.Correspondence.ofIndices), whose converse is that of the
two strings [exchanged](##OptimalityTheory.Correspondence.inv_ofIndices), and each faithfulness
constraint is a count over the two strings that
[agrees with the count on that correspondence](##OptimalityTheory.Correspondence.Segment.maxViolOn_eq).

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

/-- A segment with the indices it bears on each correspondence relation `r : ρ`. -/
structure Segment (ρ α : Type*) where
  seg : α
  indices : ρ → List ℕ

variable {ρ α F : Type*} (r : ρ)

namespace Segment

/-- Two segments *correspond* on `r` when they share an index there. -/
def Corresponds (x y : Segment ρ α) : Prop := ∃ k ∈ x.indices r, k ∈ y.indices r

instance (x y : Segment ρ α) : Decidable (x.Corresponds r y) :=
  inferInstanceAs (Decidable (∃ k ∈ x.indices r, k ∈ y.indices r))

variable {r}

theorem Corresponds.symm {x y : Segment ρ α} (h : x.Corresponds r y) : y.Corresponds r x :=
  let ⟨k, hx, hy⟩ := h; ⟨k, hy, hx⟩

theorem corresponds_comm {x y : Segment ρ α} : x.Corresponds r y ↔ y.Corresponds r x :=
  ⟨.symm, .symm⟩

end Segment

/-- The correspondence between the positions of two strings on `r`. -/
def ofIndices (s t : List (Segment ρ α)) : Correspondence (Fin s.length) (Fin t.length) :=
  Finset.univ.filter fun p ↦ s[p.1].Corresponds r t[p.2]

variable {r} {s t : List (Segment ρ α)}

@[simp] theorem mem_ofIndices {i : Fin s.length} {j : Fin t.length} :
    (i, j) ∈ ofIndices r s t ↔ s[i].Corresponds r t[j] := by
  simp [ofIndices]

@[simp] theorem inv_ofIndices (r : ρ) (s t : List (Segment ρ α)) :
    (ofIndices r s t).inv = ofIndices r t s := by
  ext ⟨j, i⟩
  simp [Segment.corresponds_comm]

end OptimalityTheory.Correspondence

namespace OptimalityTheory.Correspondence.Segment

variable {ρ α F : Type*}

variable (P : α → Prop) [DecidablePred P] (r : ρ) (s t : List (Segment ρ α))

/-! ### MAX and DEP -/

/-- MAX restricted to the segments satisfying `P` counts those of `s` without a correspondent
in `t`. -/
def maxViolOn : ℕ := s.countP fun x ↦ P x.seg ∧ ∀ y ∈ t, ¬ x.Corresponds r y

/-- MAX counts the segments of `s` without a correspondent in `t`. -/
def maxViol : ℕ := s.countP fun x ↦ ∀ y ∈ t, ¬ x.Corresponds r y

/-- DEP restricted to the segments satisfying `P` counts those of `t` without a correspondent
in `s`. -/
def depViolOn : ℕ := maxViolOn P r t s

/-- DEP counts the segments of `t` without a correspondent in `s`. -/
def depViol : ℕ := maxViol r t s

/-! ### IDENT -/

/-- IDENT for the feature `f` counts the corresponding pairs that differ under `f`. -/
def identViol [DecidableEq F] (f : α → F) (r : ρ) (s t : List (Segment ρ α)) : ℕ :=
  (s.map fun x ↦ t.countP fun y ↦ x.Corresponds r y ∧ f x.seg ≠ f y.seg).sum

/-- MAX of a privative property counts the corresponding pairs whose first member has it and
whose second lacks it. -/
def maxViolFeature : ℕ :=
  (s.map fun x ↦ t.countP fun y ↦ x.Corresponds r y ∧ P x.seg ∧ ¬ P y.seg).sum

/-- DEP of a privative property counts the corresponding pairs whose second member has it and
whose first lacks it. -/
def depViolFeature : ℕ := maxViolFeature P r t s

/-! ### INTEGRITY and UNIFORMITY -/

/-- INTEGRITY counts the segments of `s` with more than one correspondent in `t`. -/
def integrityViol : ℕ := s.countP fun x ↦ 1 < t.countP (x.Corresponds r ·)

/-- UNIFORMITY counts the segments of `t` with more than one correspondent in `s`. -/
def uniformityViol : ℕ := integrityViol r t s

/-! ### The counts on the derived correspondence -/

/-- A count over a list is the number of its positions whose element is counted. -/
private theorem countP_eq_card_filter_getElem {β : Type*} (l : List β) (p : β → Prop)
    [DecidablePred p] : l.countP (p ·) = (Finset.univ.filter fun i : Fin l.length ↦ p l[i]).card := by
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
    i ∈ (ofIndices r s t).image Prod.fst ↔ ∃ y ∈ t, s[i].Corresponds r y := by
  simp only [Finset.mem_image, Prod.exists, mem_ofIndices, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨j, h⟩ ↦ ⟨t[j], List.getElem_mem _, h⟩,
    fun ⟨y, hy, h⟩ ↦ let ⟨j, hj, e⟩ := List.getElem_of_mem hy; ⟨⟨j, hj⟩, e ▸ h⟩⟩

theorem maxViolOn_eq :
    maxViolOn P r s t = (ofIndices r s t).maxViolOn fun i ↦ P s[i].seg := by
  rw [maxViolOn, Correspondence.maxViolOn,
    countP_eq_card_filter_getElem s fun x ↦ P x.seg ∧ ∀ y ∈ t, ¬ x.Corresponds r y]
  congr 1
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_image_fst_ofIndices, not_exists, not_and]

theorem maxViol_eq : maxViol r s t = (ofIndices r s t).maxViol := by
  rw [maxViol, Correspondence.maxViol,
    countP_eq_card_filter_getElem s fun x ↦ ∀ y ∈ t, ¬ x.Corresponds r y]
  congr 1
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_image_fst_ofIndices, not_exists, not_and]

theorem depViolOn_eq :
    depViolOn P r s t = (ofIndices r s t).depViolOn fun j ↦ P t[j].seg := by
  rw [depViolOn, maxViolOn_eq, ← inv_ofIndices, Correspondence.depViolOn]

theorem depViol_eq : depViol r s t = (ofIndices r s t).depViol := by
  rw [depViol, maxViol_eq, ← inv_ofIndices, Correspondence.depViol]

theorem identViol_eq [DecidableEq F] (f : α → F) :
    identViol f r s t =
      (ofIndices r s t).identViol (fun i ↦ f s[i].seg) fun j ↦ f t[j].seg := by
  rw [identViol, Correspondence.identViol, ofIndices, Finset.filter_filter]
  exact sum_map_countP_eq_card_filter s t fun x y ↦ x.Corresponds r y ∧ f x.seg ≠ f y.seg

theorem maxViolFeature_eq :
    maxViolFeature P r s t =
      (ofIndices r s t).maxViolFeature (fun i ↦ P s[i].seg) fun j ↦ P t[j].seg := by
  rw [maxViolFeature, Correspondence.maxViolFeature, ofIndices, Finset.filter_filter]
  exact sum_map_countP_eq_card_filter s t fun x y ↦ x.Corresponds r y ∧ P x.seg ∧ ¬ P y.seg

theorem integrityViol_eq : integrityViol r s t = (ofIndices r s t).integrityViol := by
  rw [integrityViol, Correspondence.integrityViol,
    countP_eq_card_filter_getElem s fun x ↦ 1 < t.countP (x.Corresponds r ·)]
  congr 1
  ext i
  have h : (ofIndices r s t).filter (fun x ↦ x.1 = i) =
      (Finset.univ.filter fun j : Fin t.length ↦ s[i].Corresponds r t[j]).map
        ⟨fun j ↦ (i, j), fun _ _ h ↦ congrArg Prod.snd h⟩ := by
    ext ⟨a, j⟩
    simp only [Finset.mem_filter, mem_ofIndices, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨h, e⟩ ↦ ⟨j, e ▸ h, e.symm, rfl⟩, fun ⟨_, h, e, e'⟩ ↦ e ▸ e' ▸ ⟨h, rfl⟩⟩
  rw [Finset.mem_filter, Finset.mem_filter, h, Finset.card_map,
    countP_eq_card_filter_getElem t fun y ↦ s[i].Corresponds r y]

theorem uniformityViol_eq : uniformityViol r s t = (ofIndices r s t).uniformityViol := by
  rw [uniformityViol, integrityViol_eq, ← inv_ofIndices, Correspondence.uniformityViol]

end OptimalityTheory.Correspondence.Segment

namespace OptimalityTheory.Correspondence

variable {ρ α : Type*}

/-! ### Indexings -/

/-- The string `l` with each segment indexed by its position, on every relation. -/
def indexed (l : List α) : List (Segment ρ α) :=
  l.zipIdx.map fun x ↦ ⟨x.1, fun _ ↦ [x.2]⟩

@[simp] theorem length_indexed (l : List α) : (indexed (ρ := ρ) l).length = l.length := by
  simp [indexed]

/-- A string corresponds with itself, indexed by position, without a MAX violation. -/
theorem maxViol_indexed_self (r : ρ) (l : List α) :
    Segment.maxViol r (indexed l) (indexed l) = 0 := by
  rw [Segment.maxViol, List.countP_eq_zero]
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  simpa using ⟨_, hx, a.2, List.mem_singleton_self _, List.mem_singleton_self _⟩

end OptimalityTheory.Correspondence
