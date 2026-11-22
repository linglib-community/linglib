/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# LINEARITY, CONTIGUITY and ANCHORING

The faithfulness constraints that read the order of the positions. LINEARITY requires a
correspondence to preserve precedence (`Correspondence.linearityViol_eq_zero_iff`), CONTIGUITY
that its domain or its range be an interval (`Correspondence.contigIViol_eq_zero_iff`,
`Correspondence.contigOViol_eq_zero_iff`), and ANCHORING that the first or the last positions of
the two structures correspond. A correspondence that violates none of MAX, DEP, INTEGRITY,
UNIFORMITY and LINEARITY is the graph of an order isomorphism
(`Correspondence.isFaithful_iff_exists_orderIso`).

## Implementation notes

LINEARITY counts inversions, the pairs of correspondences $x ℜ x'$ and $y ℜ y'$ with $x < y$
and $y' < x'$, so that coalescence and breaking violate UNIFORMITY and INTEGRITY alone. O-CONTIG
is I-CONTIG of the converse.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [A. Payne, M. H. Vu and J. Heinz, *A Formal Analysis of Correspondence Theory*
  (2017)][payne-vu-heinz-2017]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

open scoped SetRel

variable {ι κ μ : Type*}

/-! ### LINEARITY -/

section Linearity

variable [LinearOrder ι] [LinearOrder κ]

/-- LINEARITY counts the pairs of correspondences `(i₁, j₁)` and `(i₂, j₂)` with `i₁ < i₂` but
`j₂ < j₁`. -/
def linearityViol (R : Correspondence ι κ) : ℕ :=
  ((R ×ˢ R).filter fun xy ↦ xy.1.1 < xy.2.1 ∧ xy.2.2 < xy.1.2).card

theorem linearityViol_eq_zero_iff (R : Correspondence ι κ) :
    R.linearityViol = 0 ↔ ∀ ⦃i j⦄, i ~[R.rel] j → ∀ ⦃i' j'⦄, i' ~[R.rel] j' → i < i' → j ≤ j' := by
  simp only [linearityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_product,
    and_imp, not_and, not_lt, Prod.forall, mem_rel]
  exact ⟨fun h i j hij i' j' hij' ↦ h i j i' j' hij hij', fun h i j i' j' hij hij' ↦ h hij hij'⟩

theorem linearityViol_eq_zero_of_graph {R : Correspondence ι κ} {f : ι → κ}
    (hf : R.rel = Function.graph f) (hmono : Monotone f) : R.linearityViol = 0 :=
  R.linearityViol_eq_zero_iff.2 <| hf ▸ fun _ _ h _ _ h' hlt ↦ h ▸ h' ▸ hmono hlt.le

end Linearity

/-! ### CONTIGUITY -/

section ContigI

variable [Fintype ι] [LinearOrder ι]

/-- I-CONTIG is violated once unless the domain of the relation is a contiguous substring of
the first string. -/
def contigIViol (R : Correspondence ι κ) : ℕ :=
  if ∀ i ∈ R.image Prod.fst, ∀ k ∈ R.image Prod.fst, ∀ j, i ≤ j → j ≤ k → j ∈ R.image Prod.fst
  then 0 else 1

theorem contigIViol_eq_zero_iff (R : Correspondence ι κ) :
    R.contigIViol = 0 ↔ R.rel.dom.OrdConnected := by
  rw [Set.ordConnected_def, dom_rel, contigIViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not, Finset.mem_coe, Set.subset_def, Set.mem_Icc, and_imp]

/-- A relation that deletes nothing skips nothing. -/
theorem contigIViol_eq_zero_of_maxViol_eq_zero {R : Correspondence ι κ} (h : R.maxViol = 0) :
    R.contigIViol = 0 :=
  R.contigIViol_eq_zero_iff.2 <| R.maxViol_eq_zero_iff.1 h ▸ Set.ordConnected_univ

end ContigI

section ContigO

variable [Fintype κ] [LinearOrder κ]

/-- O-CONTIG is violated once unless the range of the relation is a contiguous substring of the
second string. -/
def contigOViol (R : Correspondence ι κ) : ℕ :=
  R.inv.contigIViol

@[simp] theorem contigIViol_inv (R : Correspondence ι κ) : R.inv.contigIViol = R.contigOViol := rfl

@[simp] theorem contigOViol_inv (S : Correspondence κ ι) : S.inv.contigOViol = S.contigIViol := by
  rw [contigOViol, inv_inv]

theorem contigOViol_eq_zero_iff (R : Correspondence ι κ) :
    R.contigOViol = 0 ↔ R.rel.cod.OrdConnected := by
  rw [contigOViol, contigIViol_eq_zero_iff, rel_inv, SetRel.dom_inv]

/-- A relation that inserts nothing intrudes nowhere. -/
theorem contigOViol_eq_zero_of_depViol_eq_zero {R : Correspondence ι κ} (h : R.depViol = 0) :
    R.contigOViol = 0 :=
  contigIViol_eq_zero_of_maxViol_eq_zero h

end ContigO

variable [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] {R : Correspondence ι κ}

/-! ### ANCHORING -/

/-- L-ANCHOR is violated once unless the leftmost positions of the two strings correspond. -/
def anchorLViol (R : Correspondence ι κ) : ℕ :=
  if ∀ i j, (∀ k, i ≤ k) → (∀ k, j ≤ k) → (i, j) ∈ R then 0 else 1

/-- R-ANCHOR is violated once unless the rightmost positions of the two strings correspond. -/
def anchorRViol (R : Correspondence ι κ) : ℕ :=
  if ∀ i j, (∀ k, k ≤ i) → (∀ k, k ≤ j) → (i, j) ∈ R then 0 else 1

variable (R) in
theorem anchorLViol_eq_zero_iff :
    R.anchorLViol = 0 ↔ ∀ ⦃i j⦄, IsBot i → IsBot j → i ~[R.rel] j := by
  rw [anchorLViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not]
  exact ⟨fun h i j ↦ h i j, fun h i j ↦ @h i j⟩

variable (R) in
theorem anchorRViol_eq_zero_iff :
    R.anchorRViol = 0 ↔ ∀ ⦃i j⦄, IsTop i → IsTop j → i ~[R.rel] j := by
  rw [anchorRViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not]
  exact ⟨fun h i j ↦ h i j, fun h i j ↦ @h i j⟩

/-! ### Faithfulness as order isomorphism -/

variable (R) in
/-- A correspondence is *faithful* when it has no MAX, DEP, INTEGRITY, UNIFORMITY, or LINEARITY
violation. -/
structure IsFaithful : Prop where
  max : R.maxViol = 0
  dep : R.depViol = 0
  integrity : R.integrityViol = 0
  uniformity : R.uniformityViol = 0
  linearity : R.linearityViol = 0

/-- With no UNIFORMITY or LINEARITY violation either, the map is an order embedding: UNIFORMITY
rules out collisions and LINEARITY inversions. -/
theorem exists_orderEmbedding_rel_eq_graph (hmax : R.maxViol = 0) (hint : R.integrityViol = 0)
    (huni : R.uniformityViol = 0) (hlin : R.linearityViol = 0) :
    ∃ f : ι ↪o κ, R.rel = Function.graph f := by
  obtain ⟨f, hf⟩ := exists_rel_eq_graph hmax hint
  rw [uniformityViol_eq_zero_iff, hf] at huni
  rw [linearityViol_eq_zero_iff, hf] at hlin
  exact ⟨.ofStrictMono f fun a b hab ↦
    (hlin rfl rfl hab).lt_of_ne fun h ↦ hab.ne (huni h rfl), hf⟩

/-- A correspondence is faithful exactly when it is the graph of an order isomorphism between
the positions of the two strings. -/
theorem isFaithful_iff_exists_orderIso :
    R.IsFaithful ↔ ∃ e : ι ≃o κ, R.rel = Function.graph e := by
  constructor
  · rintro ⟨hmax, hdep, hint, huni, hlin⟩
    obtain ⟨f, hf⟩ := exists_orderEmbedding_rel_eq_graph hmax hint huni hlin
    rw [depViol_eq_zero_iff, hf] at hdep
    exact ⟨StrictMono.orderIsoOfSurjective f f.strictMono (Set.eq_univ_iff_forall.1 hdep), hf⟩
  · rintro ⟨e, he⟩
    exact ⟨maxViol_eq_zero_of_graph he, depViol_eq_zero_of_graph he e.surjective,
      integrityViol_eq_zero_of_graph he, uniformityViol_eq_zero_of_graph he e.injective,
      linearityViol_eq_zero_of_graph he e.monotone⟩

theorem IsFaithful.inv (h : R.IsFaithful) : R.inv.IsFaithful :=
  ⟨h.dep, by simpa using h.max, h.uniformity, by simpa using h.integrity, by
    obtain ⟨e, he⟩ := isFaithful_iff_exists_orderIso.1 h
    exact linearityViol_eq_zero_of_graph (f := e.symm)
      (by rw [rel_inv, he]; ext ⟨j, i⟩; simp [e.symm_apply_eq, eq_comm]) e.symm.monotone⟩

theorem IsFaithful.contigIViol_eq_zero (h : R.IsFaithful) : R.contigIViol = 0 :=
  contigIViol_eq_zero_of_maxViol_eq_zero h.max

theorem IsFaithful.contigOViol_eq_zero (h : R.IsFaithful) : R.contigOViol = 0 :=
  contigOViol_eq_zero_of_depViol_eq_zero h.dep

theorem IsFaithful.anchorLViol_eq_zero (h : R.IsFaithful) : R.anchorLViol = 0 := by
  obtain ⟨e, he⟩ := isFaithful_iff_exists_orderIso.1 h
  exact R.anchorLViol_eq_zero_iff.2 fun i j hi hj ↦
    he ▸ le_antisymm (e.le_symm_apply.1 (hi _)) (hj _)

theorem IsFaithful.anchorRViol_eq_zero (h : R.IsFaithful) : R.anchorRViol = 0 := by
  obtain ⟨e, he⟩ := isFaithful_iff_exists_orderIso.1 h
  exact R.anchorRViol_eq_zero_iff.2 fun i j hi hj ↦
    he ▸ le_antisymm (hj _) (e.symm_apply_le.1 (hi _))

end OptimalityTheory.Correspondence
