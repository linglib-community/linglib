/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relator
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Correspondence theory

A correspondence between two strings is a finite relation $ℜ$ between their positions, and a
faithfulness constraint is a condition on it. MAX and DEP hold when
[the domain](##OptimalityTheory.Correspondence.maxViol_eq_zero_iff) and
[the range](##OptimalityTheory.Correspondence.depViol_eq_zero_iff) of $ℜ$ are everything,
INTEGRITY and UNIFORMITY when $ℜ$ is
[right-unique](##OptimalityTheory.Correspondence.integrityViol_eq_zero_iff) and
[left-unique](##OptimalityTheory.Correspondence.uniformityViol_eq_zero_iff), LINEARITY when it
[preserves precedence](##OptimalityTheory.Correspondence.linearityViol_eq_zero_iff), and
CONTIGUITY when its domain or range is
[an interval](##OptimalityTheory.Correspondence.contigIViol_eq_zero_iff). A correspondence
satisfying the first five is the graph of
[an order isomorphism](##OptimalityTheory.Correspondence.isFaithful_iff_exists_orderIso).
Correspondences compose, and a composite of a correspondence without coalescence
[deletes no more than its two factors](##OptimalityTheory.Correspondence.maxViol_comp_le).

## Implementation notes

* A `Correspondence ι κ` is a `Finset (ι × κ)` for any two position types, as mathlib's `SetRel`
  is a `Set`, so that violation counts compute; `Correspondence.rel` is the same relation as a
  `SetRel`, in whose vocabulary the characterizations are stated. The positions of a list are
  `Fin` of its length.
* Each constraint on the range is the constraint on the domain of the converse: DEP is MAX of
  `Correspondence.inv`, UNIFORMITY is INTEGRITY, and O-CONTIG is I-CONTIG.
* Only the IDENT family reads segments, through a labelling of each position type.
* LINEARITY counts inversions, the pairs of correspondences $x ℜ x'$ and $y ℜ y'$ with $x < y$
  and $y' < x'$, so that coalescence and breaking violate UNIFORMITY and INTEGRITY alone.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [A. Payne, M. H. Vu and J. Heinz, *A Formal Analysis of Correspondence Theory*
  (2017)][payne-vu-heinz-2017]
-/

@[expose] public section

namespace OptimalityTheory

/-- A *correspondence* between two position types is a finite relation between them. -/
abbrev Correspondence (ι κ : Type*) := Finset (ι × κ)

namespace Correspondence

open scoped SetRel

variable {ι κ μ : Type*}

/-! ### The relation, its converse, and composition -/

/-- `R.rel` is the correspondence `R` as a `SetRel`. -/
def rel (R : Correspondence ι κ) : SetRel ι κ := (↑R : Set (ι × κ))

@[simp] theorem mem_rel {R : Correspondence ι κ} {i : ι} {j : κ} : i ~[R.rel] j ↔ (i, j) ∈ R :=
  Iff.rfl

theorem rel_injective : Function.Injective (rel : Correspondence ι κ → SetRel ι κ) :=
  Finset.coe_injective

/-- `R.inv` is the converse of the correspondence `R`. -/
def inv (R : Correspondence ι κ) : Correspondence κ ι := R.map (Equiv.prodComm ι κ).toEmbedding

@[simp] theorem mem_inv {R : Correspondence ι κ} {i : ι} {j : κ} : (j, i) ∈ R.inv ↔ (i, j) ∈ R := by
  simp [inv]

@[simp] theorem inv_inv (R : Correspondence ι κ) : R.inv.inv = R := by
  ext ⟨i, j⟩; simp

@[simp] theorem inv_empty : (∅ : Correspondence ι κ).inv = ∅ := rfl

theorem inv_injective : Function.Injective (inv : Correspondence ι κ → Correspondence κ ι) :=
  Function.LeftInverse.injective inv_inv

@[simp] theorem rel_inv (R : Correspondence ι κ) : R.inv.rel = R.rel.inv := by
  ext ⟨j, i⟩; simp

theorem card_filter_inv (R : Correspondence ι κ) (q : κ × ι → Prop) [DecidablePred q] :
    (R.inv.filter q).card = (R.filter fun p ↦ q p.swap).card := by
  rw [inv, Finset.filter_map, Finset.card_map]
  rfl

theorem image_fst_inv [DecidableEq κ] (R : Correspondence ι κ) :
    R.inv.image Prod.fst = R.image Prod.snd := by
  ext j; simp

theorem dom_rel [DecidableEq ι] (R : Correspondence ι κ) : R.rel.dom = ↑(R.image Prod.fst) := by
  ext i; simp

theorem cod_rel [DecidableEq κ] (R : Correspondence ι κ) : R.rel.cod = ↑(R.image Prod.snd) := by
  ext j; simp

section comp

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

/-- `R.comp S` relates `i` to `k` when `R` relates `i` to some `j` that `S` relates to `k`. -/
def comp (R : Correspondence ι κ) (S : Correspondence κ μ) : Correspondence ι μ :=
  ((R ×ˢ S).filter fun p ↦ p.1.2 = p.2.1).image fun p ↦ (p.1.1, p.2.2)

@[simp] theorem mem_comp {R : Correspondence ι κ} {S : Correspondence κ μ} {i : ι} {k : μ} :
    (i, k) ∈ R.comp S ↔ ∃ j, (i, j) ∈ R ∧ (j, k) ∈ S := by
  simp only [comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, b', c, ⟨⟨h₁, h₂⟩, rfl⟩, rfl, rfl⟩
    exact ⟨_, h₁, h₂⟩
  · rintro ⟨j, h₁, h₂⟩
    exact ⟨i, j, j, k, ⟨⟨h₁, h₂⟩, rfl⟩, rfl, rfl⟩

@[simp] theorem rel_comp (R : Correspondence ι κ) (S : Correspondence κ μ) :
    (R.comp S).rel = R.rel ○ S.rel := by
  ext ⟨i, k⟩; simp

theorem inv_comp (R : Correspondence ι κ) (S : Correspondence κ μ) :
    (R.comp S).inv = S.inv.comp R.inv :=
  rel_injective <| by simp [SetRel.inv_comp]

theorem comp_assoc {ν : Type*} [DecidableEq ν] (R : Correspondence ι κ) (S : Correspondence κ μ)
    (T : Correspondence μ ν) : (R.comp S).comp T = R.comp (S.comp T) :=
  rel_injective <| by simp [SetRel.comp_assoc]

end comp

/-- `graph f` is the correspondence in which each position `i` has the single correspondent
`f i`. -/
def graph [Fintype ι] (f : ι → κ) : Correspondence ι κ :=
  Finset.univ.map ⟨fun i ↦ (i, f i), fun _ _ h ↦ congrArg Prod.fst h⟩

@[simp] theorem mem_graph [Fintype ι] {f : ι → κ} {i : ι} {j : κ} : (i, j) ∈ graph f ↔ f i = j := by
  simp [graph, eq_comm]

@[simp] theorem rel_graph [Fintype ι] (f : ι → κ) : (graph f).rel = Function.graph f :=
  Set.ext fun _ ↦ mem_graph

theorem mem_iff_of_graph {R : Correspondence ι κ} {f : ι → κ} (hf : R.rel = Function.graph f)
    {i : ι} {j : κ} : (i, j) ∈ R ↔ f i = j := by
  rw [← mem_rel, hf, Function.mem_graph]

/-! ### IDENT

Only this family reads segments, through a labelling of each position type. -/

section Ident

variable {F : Type*} [DecidableEq F]

/-- IDENT counts the corresponding pairs that differ under the labellings `s` and `t`, which
give each position its segment or the value of one of its features. -/
def identViol (s : ι → F) (t : κ → F) (R : Correspondence ι κ) : ℕ :=
  (R.filter fun x ↦ s x.1 ≠ t x.2).card

@[simp] theorem identViol_empty (s : ι → F) (t : κ → F) : identViol s t ∅ = 0 := rfl

@[simp] theorem identViol_inv (R : Correspondence ι κ) (s : ι → F) (t : κ → F) :
    R.inv.identViol t s = R.identViol s t := by
  rw [identViol, card_filter_inv]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ ne_comm)

theorem identViol_eq_zero_iff_of_graph {R : Correspondence ι κ} {f : ι → κ}
    (hf : R.rel = Function.graph f) (s : ι → F) (t : κ → F) :
    R.identViol s t = 0 ↔ ∀ i, s i = t (f i) := by
  simp only [identViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
  refine ⟨fun H i ↦ H ((mem_iff_of_graph hf).2 rfl), ?_⟩
  rintro H ⟨i, j⟩ hij
  rw [← (mem_iff_of_graph hf).1 hij]
  exact H i

end Ident

section Feature

variable (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q]

/-- MAX of a privative property counts the corresponding pairs whose first member has it and
whose second lacks it, the autosegment being lost. -/
def maxViolFeature (R : Correspondence ι κ) : ℕ :=
  (R.filter fun x ↦ p x.1 ∧ ¬ q x.2).card

/-- DEP of a privative property counts the corresponding pairs whose second member has it and
whose first lacks it, the autosegment being inserted. -/
def depViolFeature (R : Correspondence ι κ) : ℕ :=
  (R.filter fun x ↦ ¬ p x.1 ∧ q x.2).card

@[simp] theorem maxViolFeature_empty : maxViolFeature p q ∅ = 0 := rfl

@[simp] theorem depViolFeature_empty : depViolFeature p q ∅ = 0 := rfl

@[simp] theorem maxViolFeature_inv (R : Correspondence ι κ) :
    R.inv.maxViolFeature q p = R.depViolFeature p q := by
  rw [maxViolFeature, card_filter_inv]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ and_comm)

@[simp] theorem depViolFeature_inv (R : Correspondence ι κ) :
    R.inv.depViolFeature q p = R.maxViolFeature p q := by
  rw [depViolFeature, card_filter_inv]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ and_comm)

theorem maxViolFeature_pos_iff (R : Correspondence ι κ) :
    0 < R.maxViolFeature p q ↔ ∃ x ∈ R, p x.1 ∧ ¬ q x.2 := by
  simp [maxViolFeature, Finset.card_pos, Finset.filter_nonempty_iff]

end Feature

/-! ### MAX and INTEGRITY

The constraints on the domain: MAX vanishes iff the domain is everything, and INTEGRITY iff the
relation is right-unique. -/

section Domain

variable [Fintype ι] [DecidableEq ι]

/-- MAX restricted to the positions satisfying `P` counts those without a correspondent, as in
MAX-V, MAX-C, and the positional faithfulness constraints. -/
def maxViolOn (P : ι → Prop) [DecidablePred P] (R : Correspondence ι κ) : ℕ :=
  (Finset.univ.filter P \ R.image Prod.fst).card

/-- MAX counts the positions of the first string without a correspondent in the second. -/
def maxViol (R : Correspondence ι κ) : ℕ :=
  (Finset.univ \ R.image Prod.fst).card

/-- INTEGRITY counts the positions of the first string with more than one correspondent. -/
def integrityViol (R : Correspondence ι κ) : ℕ :=
  (Finset.univ.filter fun i ↦ 1 < (R.filter fun x ↦ x.1 = i).card).card

@[simp] theorem maxViolOn_true (R : Correspondence ι κ) : R.maxViolOn (fun _ ↦ True) = R.maxViol := by
  simp [maxViolOn, maxViol]

theorem maxViol_eq_zero_iff (R : Correspondence ι κ) : R.maxViol = 0 ↔ R.rel.dom = Set.univ := by
  rw [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff,
    dom_rel, Finset.coe_eq_univ]

theorem integrityViol_eq_zero_iff (R : Correspondence ι κ) :
    R.integrityViol = 0 ↔ Relator.RightUnique (· ~[R.rel] ·) := by
  simp only [integrityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_const, not_lt, Finset.card_le_one, Finset.mem_filter, and_imp, Prod.forall,
    Prod.mk.injEq]
  exact ⟨fun h i j j' hj hj' ↦ (h i j hj rfl i j' hj' rfl).2,
    fun h i a j hj ha a' j' hj' ha' ↦ by subst ha ha'; exact ⟨rfl, h hj hj'⟩⟩

variable {R : Correspondence ι κ} {f : ι → κ}

theorem maxViol_eq_zero_of_graph (hf : R.rel = Function.graph f) : R.maxViol = 0 :=
  R.maxViol_eq_zero_iff.2 <| hf ▸ Set.eq_univ_of_forall fun i ↦ ⟨f i, rfl⟩

theorem integrityViol_eq_zero_of_graph (hf : R.rel = Function.graph f) : R.integrityViol = 0 :=
  R.integrityViol_eq_zero_iff.2 <| hf ▸ fun _ _ _ h h' ↦ h.symm.trans h'

/-- A relation with no MAX or INTEGRITY violation is the graph of a map of positions. -/
theorem exists_rel_eq_graph (hmax : R.maxViol = 0) (hint : R.integrityViol = 0) :
    ∃ f : ι → κ, R.rel = Function.graph f := by
  rw [maxViol_eq_zero_iff] at hmax
  rw [integrityViol_eq_zero_iff] at hint
  choose f hf using Set.eq_univ_iff_forall.1 hmax
  exact ⟨f, Set.ext fun ⟨i, j⟩ ↦ ⟨fun h ↦ hint (hf i) h, fun (h : f i = j) ↦ h ▸ hf i⟩⟩

end Domain

/-! ### DEP and UNIFORMITY

Each constraint on the range is the constraint on the domain of the converse. -/

section Range

variable [Fintype κ] [DecidableEq κ]

/-- DEP restricted to the positions of the second string satisfying `P`. -/
def depViolOn (P : κ → Prop) [DecidablePred P] (R : Correspondence ι κ) : ℕ :=
  R.inv.maxViolOn P

/-- DEP counts the positions of the second string without a correspondent in the first. -/
def depViol (R : Correspondence ι κ) : ℕ :=
  R.inv.maxViol

/-- UNIFORMITY counts the positions of the second string with more than one correspondent. -/
def uniformityViol (R : Correspondence ι κ) : ℕ :=
  R.inv.integrityViol

variable (R : Correspondence ι κ) (S : Correspondence κ ι)

@[simp] theorem maxViol_inv : R.inv.maxViol = R.depViol := rfl

@[simp] theorem depViol_inv : S.inv.depViol = S.maxViol := by rw [depViol, inv_inv]

@[simp] theorem maxViolOn_inv (P : κ → Prop) [DecidablePred P] :
    R.inv.maxViolOn P = R.depViolOn P := rfl

@[simp] theorem depViolOn_inv (P : κ → Prop) [DecidablePred P] :
    S.inv.depViolOn P = S.maxViolOn P := by rw [depViolOn, inv_inv]

@[simp] theorem integrityViol_inv : R.inv.integrityViol = R.uniformityViol := rfl

@[simp] theorem uniformityViol_inv : S.inv.uniformityViol = S.integrityViol := by
  rw [uniformityViol, inv_inv]

theorem depViolOn_eq (P : κ → Prop) [DecidablePred P] :
    R.depViolOn P = (Finset.univ.filter P \ R.image Prod.snd).card := by
  rw [depViolOn, maxViolOn, image_fst_inv]

theorem depViol_eq : R.depViol = (Finset.univ \ R.image Prod.snd).card := by
  rw [depViol, maxViol, image_fst_inv]

@[simp] theorem depViolOn_true : R.depViolOn (fun _ ↦ True) = R.depViol :=
  maxViolOn_true R.inv

theorem depViol_eq_zero_iff : R.depViol = 0 ↔ R.rel.cod = Set.univ := by
  rw [depViol, maxViol_eq_zero_iff, rel_inv, SetRel.dom_inv]

theorem uniformityViol_eq_zero_iff :
    R.uniformityViol = 0 ↔ Relator.LeftUnique (· ~[R.rel] ·) := by
  rw [uniformityViol, integrityViol_eq_zero_iff, rel_inv]
  exact ⟨fun h _ _ _ h₁ h₂ ↦ h h₁ h₂, fun h _ _ _ h₁ h₂ ↦ h h₁ h₂⟩

variable {R} {f : ι → κ}

theorem depViol_eq_zero_of_graph (hf : R.rel = Function.graph f) (hsurj : Function.Surjective f) :
    R.depViol = 0 :=
  R.depViol_eq_zero_iff.2 <| hf ▸ Set.eq_univ_of_forall hsurj

theorem depViolOn_of_graph [Fintype ι] (hf : R.rel = Function.graph f) (P : κ → Prop)
    [DecidablePred P] : R.depViolOn P = (Finset.univ.filter P \ Finset.univ.image f).card := by
  rw [depViolOn_eq]
  congr 2
  ext j
  simp [mem_iff_of_graph hf]

theorem uniformityViol_eq_zero_of_graph (hf : R.rel = Function.graph f)
    (hinj : Function.Injective f) : R.uniformityViol = 0 :=
  R.uniformityViol_eq_zero_iff.2 <| hf ▸ fun _ _ _ h h' ↦ hinj (h.trans h'.symm)

end Range

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

/-! ### Composition -/

/-- A composite deletes no more than its two factors, provided the first does not coalesce: a
position the composite deletes is deleted by the first factor, or its one correspondent is
deleted by the second. -/
theorem maxViol_comp_le [Fintype μ] [LinearOrder μ] {S : Correspondence κ μ}
    (hR : R.uniformityViol = 0) : (R.comp S).maxViol ≤ R.maxViol + S.maxViol := by
  rw [uniformityViol_eq_zero_iff] at hR
  have hsub : Finset.univ \ (R.comp S).image Prod.fst ⊆
      (Finset.univ \ R.image Prod.fst) ∪
        ((R.image Prod.fst) \ (R.comp S).image Prod.fst) := fun i hi ↦ by
    by_cases h : i ∈ R.image Prod.fst
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, (Finset.mem_sdiff.1 hi).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left ?_ _))
  refine Finset.card_le_card_of_forall_subsingleton (fun i j ↦ (i, j) ∈ R) (fun i hi ↦ ?_)
    fun j _ i hi i' hi' ↦ hR hi.2 hi'.2
  obtain ⟨hi, hi'⟩ := Finset.mem_sdiff.1 hi
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.1 hi
  refine ⟨j, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hj ↦ hi' ?_⟩, hij⟩
  obtain ⟨⟨j, k⟩, hjk, rfl⟩ := Finset.mem_image.1 hj
  exact Finset.mem_image.2 ⟨(i, k), mem_comp.2 ⟨j, hij, hjk⟩, rfl⟩

end Correspondence

end OptimalityTheory
