/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relator
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.Fintype.Fin

/-!
# Correspondence theory

A correspondence between two strings is a relation $ℜ$ between their positions, and a faithfulness
constraint is a condition on it. MAX and DEP hold when [the domain](##maxViol_eq_zero_iff) and
[the range](##depViol_eq_zero_iff) of $ℜ$ are the whole strings, INTEGRITY and UNIFORMITY when
$ℜ$ is [right-unique](##integrityViol_eq_zero_iff) and [left-unique](##uniformityViol_eq_zero_iff),
LINEARITY when it [preserves precedence](##linearityViol_eq_zero_iff), and CONTIGUITY when its
domain or range is [an interval](##contigIViol_eq_zero_iff). An edge satisfying the first five is
[the graph of an order isomorphism](##isFaithful_iff_exists_orderIso), and there is only one:
[the diagonal between strings of equal length](##isFaithful_iff_edge_eq_diagonal), which also
satisfies CONTIGUITY and ANCHORING. A candidate that violates IDENT nowhere either
[is the fully faithful one](##isFaithful_and_identViol_eq_zero_iff).

## Implementation notes

* A `Correspondence Role α` carries one string per role and a relation between the positions of
  each ordered pair of roles, so that the input, base, and reduplicant of a reduplicative
  candidate form one diagram. A named constraint is a partial application of a family to a pair
  of roles: MAX-IO is `(·.maxViol .input .output)`.
* The relation `edge r₁ r₂` is a `Finset` of pairs of `Fin` positions, so that violation counts
  compute and every pair is in range by type; `rel r₁ r₂` is the same relation as a mathlib
  `SetRel`, in whose vocabulary the characterizations are stated. `Correspondence.ofPairs` reads
  a relation from index pairs and drops those out of range.
* LINEARITY counts inversions, the pairs of correspondences $x ℜ x'$ and $y ℜ y'$ with $x < y$
  and $y' < x'$, so that coalescence and breaking violate UNIFORMITY and INTEGRITY alone.
* A constraint over binary correspondences is faithfulness when the fully faithful candidate
  satisfies it, and markedness when it reads only the output string.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [A. Payne, M. H. Vu and J. Heinz, *A Formal Analysis of Correspondence Theory*
  (2017)][payne-vu-heinz-2017]
-/

@[expose] public section

namespace OptimalityTheory

/-- A *correspondence diagram*: a string for each role and, for each ordered pair of roles, a
directed relation between their positions. -/
structure Correspondence (Role : Type*) (α : Type*) where
  form : Role → List α
  edge : (r₁ r₂ : Role) → Finset (Fin (form r₁).length × Fin (form r₂).length)

/-- The roles of a binary correspondence are its two strings, as in `Correspondence.parallel`
and `Correspondence.identity`. -/
inductive BinaryRole where
  | lhs
  | rhs
  deriving DecidableEq, Repr

/-- `r.swap` is the other role of a binary correspondence. -/
def BinaryRole.swap : BinaryRole → BinaryRole
  | .lhs => .rhs
  | .rhs => .lhs

@[simp] theorem BinaryRole.swap_lhs : BinaryRole.lhs.swap = .rhs := rfl

@[simp] theorem BinaryRole.swap_rhs : BinaryRole.rhs.swap = .lhs := rfl

/-- The roles of the basic model of reduplication are the input, the base and the
reduplicant. -/
inductive ReduplicationRole where
  | input
  | base
  | reduplicant
  deriving DecidableEq, Repr

namespace Correspondence

open scoped SetRel

variable {Role : Type*} {α : Type*}

/-- `c.rel r₁ r₂` is the correspondence relation between the positions of `form r₁` and those of
`form r₂`. -/
def rel (c : Correspondence Role α) (r₁ r₂ : Role) :
    SetRel (Fin (c.form r₁).length) (Fin (c.form r₂).length) :=
  ↑(c.edge r₁ r₂)

@[simp] theorem mem_rel {c : Correspondence Role α} {r₁ r₂ : Role} {i : Fin (c.form r₁).length}
    {j : Fin (c.form r₂).length} : i ~[c.rel r₁ r₂] j ↔ (i, j) ∈ c.edge r₁ r₂ :=
  Iff.rfl

theorem dom_rel (c : Correspondence Role α) (r₁ r₂ : Role) :
    (c.rel r₁ r₂).dom = ↑((c.edge r₁ r₂).image Prod.fst) := by
  ext i; simp

theorem cod_rel (c : Correspondence Role α) (r₁ r₂ : Role) :
    (c.rel r₁ r₂).cod = ↑((c.edge r₁ r₂).image Prod.snd) := by
  ext j; simp

/-- A correspondence is *symmetric* when each relation is the converse of the reverse one. -/
def IsSymmetric (c : Correspondence Role α) : Prop :=
  ∀ r₁ r₂, c.edge r₂ r₁ = (c.edge r₁ r₂).image Prod.swap

/-! ### Constraint families -/

/-- MAX counts the positions of `form r₁` without a correspondent in `form r₂`. -/
def maxViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.fst).card

/-- DEP counts the positions of `form r₂` without a correspondent in `form r₁`. -/
def depViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.snd).card

/-- MAX restricted to the positions of `form r₁` whose segment satisfies `P`, as in MAX-V and
MAX-C. -/
def maxViolOn (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((Finset.univ.filter fun i : Fin (c.form r₁).length ↦ P (c.form r₁)[i]) \
    (c.edge r₁ r₂).image Prod.fst).card

/-- DEP restricted to the positions of `form r₂` whose segment satisfies `P`, as in DEP-V and
DEP-C. -/
def depViolOn (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((Finset.univ.filter fun j : Fin (c.form r₂).length ↦ P (c.form r₂)[j]) \
    (c.edge r₁ r₂).image Prod.snd).card

/-- MAX restricted to the positions of `form r₁` that satisfy `P`, which is the form of a
positional faithfulness constraint. -/
def maxViolAt (P : ℕ → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ.filter fun i : Fin (c.form r₁).length ↦ P i) \
    (c.edge r₁ r₂).image Prod.fst).card

/-- DEP restricted to the positions of `form r₂` that satisfy `P`. -/
def depViolAt (P : ℕ → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ.filter fun j : Fin (c.form r₂).length ↦ P j) \
    (c.edge r₁ r₂).image Prod.snd).card

/-- IDENT on whole segments counts the corresponding pairs whose segments differ. -/
def identViol [DecidableEq α] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p ↦ (c.form r₁)[p.1] ≠ (c.form r₂)[p.2]).card

/-- IDENT(F) for the feature `proj` counts the corresponding pairs that differ under `proj`. -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p ↦ proj (c.form r₁)[p.1] ≠ proj (c.form r₂)[p.2]).card

/-- MAX of a privative property along a segmental correspondence counts the corresponding
pairs whose first member has `P` and whose second lacks it, the autosegment being lost. -/
def maxViolFeature (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((c.edge r₁ r₂).filter fun p ↦ P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2]).card

/-- DEP of a privative property along a segmental correspondence counts the corresponding pairs
whose second member has `P` and whose first lacks it, the autosegment being inserted. -/
def depViolFeature (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((c.edge r₁ r₂).filter fun p ↦ ¬ P (c.form r₁)[p.1] ∧ P (c.form r₂)[p.2]).card

theorem maxViolFeature_pos_iff (P : α → Prop) [DecidablePred P] (c : Correspondence Role α)
    (r₁ r₂ : Role) :
    0 < maxViolFeature P c r₁ r₂ ↔
      ∃ p ∈ c.edge r₁ r₂, P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2] := by
  simp [maxViolFeature, Finset.card_pos, Finset.filter_nonempty_iff]

/-- I-CONTIG is violated once unless the domain of the relation is a contiguous substring of
`form r₁`. -/
def contigIViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ∀ i ∈ (c.edge r₁ r₂).image Prod.fst, ∀ k ∈ (c.edge r₁ r₂).image Prod.fst,
      ∀ j, i ≤ j → j ≤ k → j ∈ (c.edge r₁ r₂).image Prod.fst then 0 else 1

/-- O-CONTIG is violated once unless the range of the relation is a contiguous substring of
`form r₂`. -/
def contigOViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ∀ i ∈ (c.edge r₁ r₂).image Prod.snd, ∀ k ∈ (c.edge r₁ r₂).image Prod.snd,
      ∀ j, i ≤ j → j ≤ k → j ∈ (c.edge r₁ r₂).image Prod.snd then 0 else 1

/-- L-ANCHOR is violated once unless the leftmost positions of the two strings correspond. -/
def anchorLViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ∀ i j, (∀ k, i ≤ k) → (∀ k, j ≤ k) → (i, j) ∈ c.edge r₁ r₂ then 0 else 1

/-- R-ANCHOR is violated once unless the rightmost positions of the two strings correspond. -/
def anchorRViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ∀ i j, (∀ k, k ≤ i) → (∀ k, k ≤ j) → (i, j) ∈ c.edge r₁ r₂ then 0 else 1

/-- LINEARITY counts the pairs of correspondences `(i₁, j₁)` and `(i₂, j₂)` with `i₁ < i₂` but
`j₂ < j₁`. -/
def linearityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂ ×ˢ c.edge r₁ r₂).filter fun pq ↦ pq.1.1 < pq.2.1 ∧ pq.2.2 < pq.1.2).card

/-- UNIFORMITY counts the positions of `form r₂` with more than one correspondent in
`form r₁`. -/
def uniformityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₂).length)).filter fun j ↦
    1 < ((c.edge r₁ r₂).filter fun p ↦ p.2 = j).card).card

/-- INTEGRITY counts the positions of `form r₁` with more than one correspondent in
`form r₂`. -/
def integrityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₁).length)).filter fun i ↦
    1 < ((c.edge r₁ r₂).filter fun p ↦ p.1 = i).card).card

/-! ### Vanishing characterizations

Each constraint vanishes iff the relation has the corresponding property: its domain or range is
everything, it is right-unique or left-unique, it preserves precedence, its domain or range is an
interval, the leftmost or rightmost positions correspond. -/

variable (c : Correspondence Role α) (r₁ r₂ : Role)

theorem maxViol_eq_zero_iff : c.maxViol r₁ r₂ = 0 ↔ (c.rel r₁ r₂).dom = Set.univ := by
  rw [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff,
    dom_rel, Finset.coe_eq_univ]

theorem depViol_eq_zero_iff : c.depViol r₁ r₂ = 0 ↔ (c.rel r₁ r₂).cod = Set.univ := by
  rw [depViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff,
    cod_rel, Finset.coe_eq_univ]

theorem maxViolOn_true : maxViolOn (fun _ ↦ True) c r₁ r₂ = c.maxViol r₁ r₂ := by
  simp [maxViolOn, maxViol]

theorem depViolOn_true : depViolOn (fun _ ↦ True) c r₁ r₂ = c.depViol r₁ r₂ := by
  simp [depViolOn, depViol]

theorem maxViolAt_true : maxViolAt (fun _ ↦ True) c r₁ r₂ = c.maxViol r₁ r₂ := by
  simp [maxViolAt, maxViol]

theorem depViolAt_true : depViolAt (fun _ ↦ True) c r₁ r₂ = c.depViol r₁ r₂ := by
  simp [depViolAt, depViol]

theorem integrityViol_eq_zero_iff :
    c.integrityViol r₁ r₂ = 0 ↔ Relator.RightUnique (· ~[c.rel r₁ r₂] ·) := by
  simp only [integrityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_const, not_lt, Finset.card_le_one, Finset.mem_filter, and_imp, Prod.forall,
    Prod.mk.injEq]
  exact ⟨fun h i j j' hj hj' ↦ (h i j hj rfl i j' hj' rfl).2,
    fun h i a j hj ha a' j' hj' ha' ↦ by subst ha ha'; exact ⟨rfl, h hj hj'⟩⟩

theorem uniformityViol_eq_zero_iff :
    c.uniformityViol r₁ r₂ = 0 ↔ Relator.LeftUnique (· ~[c.rel r₁ r₂] ·) := by
  simp only [uniformityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_const, not_lt, Finset.card_le_one, Finset.mem_filter, and_imp, Prod.forall,
    Prod.mk.injEq]
  exact ⟨fun h i i' j hi hi' ↦ (h i j hi rfl i' j hi' rfl).1,
    fun h j i b hi hb i' b' hi' hb' ↦ by subst hb hb'; exact ⟨h hi hi', rfl⟩⟩

theorem linearityViol_eq_zero_iff :
    c.linearityViol r₁ r₂ = 0 ↔
      ∀ ⦃i j⦄, i ~[c.rel r₁ r₂] j → ∀ ⦃i' j'⦄, i' ~[c.rel r₁ r₂] j' → i < i' → j ≤ j' := by
  simp only [linearityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_product,
    and_imp, not_and, not_lt, Prod.forall, mem_rel]
  exact ⟨fun h i j hij i' j' hij' ↦ h i j i' j' hij hij', fun h i j i' j' hij hij' ↦ h hij hij'⟩

theorem contigIViol_eq_zero_iff : c.contigIViol r₁ r₂ = 0 ↔ (c.rel r₁ r₂).dom.OrdConnected := by
  rw [Set.ordConnected_def, dom_rel, contigIViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not, Finset.mem_coe, Set.subset_def, Set.mem_Icc, and_imp]

theorem contigOViol_eq_zero_iff : c.contigOViol r₁ r₂ = 0 ↔ (c.rel r₁ r₂).cod.OrdConnected := by
  rw [Set.ordConnected_def, cod_rel, contigOViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not, Finset.mem_coe, Set.subset_def, Set.mem_Icc, and_imp]

theorem anchorLViol_eq_zero_iff :
    c.anchorLViol r₁ r₂ = 0 ↔ ∀ ⦃i j⦄, IsBot i → IsBot j → i ~[c.rel r₁ r₂] j := by
  rw [anchorLViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not]
  exact ⟨fun h i j ↦ h i j, fun h i j ↦ @h i j⟩

theorem anchorRViol_eq_zero_iff :
    c.anchorRViol r₁ r₂ = 0 ↔ ∀ ⦃i j⦄, IsTop i → IsTop j → i ~[c.rel r₁ r₂] j := by
  rw [anchorRViol, ite_eq_left_iff]
  simp only [one_ne_zero, imp_false, not_not]
  exact ⟨fun h i j ↦ h i j, fun h i j ↦ @h i j⟩

/-- A relation that deletes nothing skips nothing. -/
theorem contigIViol_eq_zero_of_maxViol_eq_zero (h : c.maxViol r₁ r₂ = 0) :
    c.contigIViol r₁ r₂ = 0 :=
  (contigIViol_eq_zero_iff c r₁ r₂).2 <| (maxViol_eq_zero_iff c r₁ r₂).1 h ▸ Set.ordConnected_univ

/-- A relation that inserts nothing intrudes nowhere. -/
theorem contigOViol_eq_zero_of_depViol_eq_zero (h : c.depViol r₁ r₂ = 0) :
    c.contigOViol r₁ r₂ = 0 :=
  (contigOViol_eq_zero_iff c r₁ r₂).2 <| (depViol_eq_zero_iff c r₁ r₂).1 h ▸ Set.ordConnected_univ

/-! ### Constructors -/

/-- The index pairs `(0, 0), …, (k - 1, k - 1)` of a parallel correspondence. -/
def diagonalPairs (k : ℕ) : List (ℕ × ℕ) := (List.range k).map fun i ↦ (i, i)

/-- The index pairs of the positions of two outputs that realise a common input position, from
the index pairs of the two input–output relations. -/
def composePairs (l₁ l₂ : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l₁.flatMap fun (r, p) ↦ l₂.filterMap fun (r', q) ↦ if r = r' then some (p, q) else none

/-- The positions of an output of length `n` that realise no input position under `l`. -/
def epentheticPositions (l : List (ℕ × ℕ)) (n : ℕ) : List ℕ :=
  (List.range n).filter fun p ↦ ∀ rp ∈ l, rp.2 ≠ p

/-- The site of an output position under `l`: the last input position realised at or before
it. -/
def site (l : List (ℕ × ℕ)) (p : ℕ) : Option ℕ :=
  ((l.filter fun rp ↦ rp.2 ≤ p).map Prod.fst).max?

/-- The output–output relation that two input–output relations `l₁`, `l₂` of outputs of lengths
`n₁`, `n₂` induce: the positions realising a common input position, and the epenthetic positions
at a common site. -/
def ooPairs (l₁ l₂ : List (ℕ × ℕ)) (n₁ n₂ : ℕ) : List (ℕ × ℕ) :=
  composePairs l₁ l₂ ++ (epentheticPositions l₁ n₁).flatMap fun p ↦
    (epentheticPositions l₂ n₂).filterMap fun q ↦
      if site l₁ p = site l₂ q then some (p, q) else none

/-- The relation on positions given by index pairs; pairs out of range are dropped. -/
def edgeOfPairs (m n : ℕ) (l : List (ℕ × ℕ)) : Finset (Fin m × Fin n) :=
  (l.filterMap fun p ↦
    if h : p.1 < m ∧ p.2 < n then some (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else none).toFinset

@[simp] theorem mem_edgeOfPairs {m n : ℕ} {l : List (ℕ × ℕ)} {p : Fin m × Fin n} :
    p ∈ edgeOfPairs m n l ↔ ((p.1 : ℕ), (p.2 : ℕ)) ∈ l := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  simp [edgeOfPairs, ha, hb]

/-- `ofPairs form pairs` is the correspondence whose relation `edge r₁ r₂` reads the index
pairs `pairs r₁ r₂` into the two position types. -/
def ofPairs (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ)) :
    Correspondence Role α where
  form := form
  edge r₁ r₂ := edgeOfPairs _ _ (pairs r₁ r₂)

@[simp] theorem ofPairs_form (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ))
    (r : Role) : (ofPairs form pairs).form r = form r := rfl

@[simp] theorem ofPairs_edge (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ)) :
    (ofPairs form pairs).edge r₁ r₂ = edgeOfPairs _ _ (pairs r₁ r₂) := rfl

/-- The diagonal `(0, 0), (1, 1), …` of `Fin m × Fin n`, one pair per index of the
shorter string. -/
def diagonal (m n : ℕ) : Finset (Fin m × Fin n) :=
  (Finset.univ : Finset (Fin (min m n))).image
    fun i ↦ (i.castLE (min_le_left _ _), i.castLE (min_le_right _ _))

@[simp] theorem mem_diagonal {m n : ℕ} (a : Fin m) (b : Fin n) :
    (a, b) ∈ diagonal m n ↔ (a : ℕ) = (b : ℕ) := by
  simp only [diagonal, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff,
    Fin.val_castLE]
  exact ⟨fun ⟨_, h₁, h₂⟩ ↦ h₁.symm.trans h₂,
    fun h ↦ ⟨⟨a, by have := a.2; have := b.2; omega⟩, rfl, h⟩⟩

theorem card_diagonal (m n : ℕ) : (diagonal m n).card = min m n := by
  rw [diagonal, Finset.card_image_of_injective _ fun _ _ h ↦ Fin.ext (congrArg (·.1.1) h),
    Finset.card_univ, Fintype.card_fin]

theorem image_swap_diagonal (m n : ℕ) : (diagonal m n).image Prod.swap = diagonal n m := by
  ext ⟨a, b⟩
  simp only [Finset.mem_image, mem_diagonal, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  exact ⟨fun ⟨_, _, h, rfl, rfl⟩ ↦ h.symm, fun h ↦ ⟨b, a, h.symm, rfl, rfl⟩⟩

/-- The diagonal correspondence on every pair of roles satisfying `hasEdge`, empty
elsewhere. -/
def diagram (form : Role → List α) (hasEdge : Role → Role → Prop) [DecidableRel hasEdge] :
    Correspondence Role α where
  form := form
  edge r₁ r₂ := if hasEdge r₁ r₂ then diagonal (form r₁).length (form r₂).length else ∅

section diagram

variable (form : Role → List α) (hasEdge : Role → Role → Prop) [DecidableRel hasEdge]

@[simp] theorem diagram_form (r : Role) : (diagram form hasEdge).form r = form r := rfl

theorem diagram_edge : (diagram form hasEdge).edge r₁ r₂ =
    if hasEdge r₁ r₂ then diagonal (form r₁).length (form r₂).length else ∅ := rfl

theorem diagram_edge_pos {r₁ r₂ : Role} (h : hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = diagonal (form r₁).length (form r₂).length :=
  ite_eq_left h

theorem diagram_edge_neg {r₁ r₂ : Role} (h : ¬ hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = ∅ :=
  ite_eq_right h

theorem diagram_isSymmetric (hsymm : ∀ {r₁ r₂}, hasEdge r₁ r₂ → hasEdge r₂ r₁) :
    IsSymmetric (diagram form hasEdge) := by
  intro r₁ r₂
  by_cases h : hasEdge r₁ r₂
  · rw [diagram_edge_pos _ _ (hsymm h), diagram_edge_pos _ _ h]
    exact (image_swap_diagonal _ _).symm
  · rw [diagram_edge_neg _ _ (mt hsymm h), diagram_edge_neg _ _ h, Finset.image_empty]

end diagram

/-- The diagonal correspondence between two strings, truncated to the shorter. -/
def parallel (s₁ s₂ : List α) : Correspondence BinaryRole α :=
  diagram (fun | .lhs => s₁ | .rhs => s₂) (· ≠ ·)

/-- `identity s` is the fully faithful candidate, the diagonal correspondence of a string with
itself. -/
def identity (s : List α) : Correspondence BinaryRole α := parallel s s

/-- The input–base–reduplicant diagram with diagonal correspondence between each pair of
distinct roles. -/
def reduplication (input base reduplicant : List α) : Correspondence ReduplicationRole α :=
  diagram (fun | .input => input | .base => base | .reduplicant => reduplicant) (· ≠ ·)

theorem parallel_isSymmetric (s₁ s₂ : List α) : IsSymmetric (parallel s₁ s₂) :=
  diagram_isSymmetric _ _ Ne.symm

theorem reduplication_isSymmetric (input base reduplicant : List α) :
    IsSymmetric (reduplication input base reduplicant) :=
  diagram_isSymmetric _ _ Ne.symm

@[simp] theorem parallel_form_lhs (s₁ s₂ : List α) : (parallel s₁ s₂).form .lhs = s₁ := rfl

@[simp] theorem parallel_form_rhs (s₁ s₂ : List α) : (parallel s₁ s₂).form .rhs = s₂ := rfl

@[simp] theorem parallel_edge_diag (s₁ s₂ : List α) (r : BinaryRole) :
    (parallel s₁ s₂).edge r r = ∅ :=
  diagram_edge_neg _ _ (by cases r <;> decide)

@[simp] theorem parallel_edge_lhs_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .lhs .rhs = diagonal s₁.length s₂.length :=
  diagram_edge_pos _ _ (by decide)

@[simp] theorem parallel_edge_rhs_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .rhs .lhs = diagonal s₂.length s₁.length := by
  rw [parallel_isSymmetric s₁ s₂ .lhs .rhs, parallel_edge_lhs_rhs]
  exact image_swap_diagonal _ _

@[simp] theorem reduplication_form_input (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .input = input := rfl

@[simp] theorem reduplication_form_base (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .base = base := rfl

@[simp] theorem reduplication_form_reduplicant (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .reduplicant = reduplicant := rfl

theorem reduplication_edge (input base reduplicant : List α) {r₁ r₂ : ReduplicationRole}
    (h : r₁ ≠ r₂) :
    (reduplication input base reduplicant).edge r₁ r₂ =
      diagonal ((reduplication input base reduplicant).form r₁).length
        ((reduplication input base reduplicant).form r₂).length :=
  diagram_edge_pos _ _ h

/-- `ofFun s t f` is the binary correspondence in which each position `i` of `s` has the single
correspondent `f i` in `t`. -/
def ofFun (s t : List α) (f : Fin s.length → Fin t.length) : Correspondence BinaryRole α where
  form
    | .lhs => s
    | .rhs => t
  edge
    | .lhs, .rhs => Finset.univ.filter fun p ↦ f p.1 = p.2
    | .rhs, .lhs => Finset.univ.filter fun p ↦ f p.2 = p.1
    | .lhs, .lhs | .rhs, .rhs => ∅

section ofFun

variable (s t : List α) (f : Fin s.length → Fin t.length)

@[simp] theorem ofFun_form_lhs : (ofFun s t f).form .lhs = s := rfl

@[simp] theorem ofFun_form_rhs : (ofFun s t f).form .rhs = t := rfl

variable {s t f} in
@[simp] theorem mem_ofFun_edge {i : Fin s.length} {j : Fin t.length} :
    (i, j) ∈ (ofFun s t f).edge .lhs .rhs ↔ f i = j := by
  simp [ofFun]

@[simp] theorem rel_ofFun : (ofFun s t f).rel .lhs .rhs = Function.graph f :=
  Set.ext fun _ ↦ mem_ofFun_edge

theorem ofFun_isSymmetric : (ofFun s t f).IsSymmetric := by
  rintro (_ | _) (_ | _) <;> ext ⟨a, b⟩ <;> simp [ofFun, eq_comm]

end ofFun

/-- `c.swap` is the binary correspondence `c` with its two strings exchanged. -/
def swap (c : Correspondence BinaryRole α) : Correspondence BinaryRole α where
  form r := c.form r.swap
  edge r₁ r₂ := c.edge r₁.swap r₂.swap

theorem IsSymmetric.swap {c : Correspondence BinaryRole α} (h : c.IsSymmetric) :
    c.swap.IsSymmetric :=
  fun r₁ r₂ ↦ h r₁.swap r₂.swap

theorem depViolAt_swap (c : Correspondence BinaryRole α) (P : ℕ → Prop) [DecidablePred P]
    (r₁ r₂ : BinaryRole) : c.swap.depViolAt P r₁ r₂ = c.depViolAt P r₁.swap r₂.swap := rfl

theorem maxViol_swap (c : Correspondence BinaryRole α) (r₁ r₂ : BinaryRole) :
    c.swap.maxViol r₁ r₂ = c.maxViol r₁.swap r₂.swap := rfl

theorem identViol_swap [DecidableEq α] (c : Correspondence BinaryRole α) (r₁ r₂ : BinaryRole) :
    c.swap.identViol r₁ r₂ = c.identViol r₁.swap r₂.swap := rfl

/-! ### Faithfulness on the diagonal

MAX, DEP, and IDENT vanish on a diagonal edge between equal strings, as on the fully faithful
candidate `identity s`. -/

theorem card_image_fst_diagonal (m n : ℕ) :
    ((diagonal m n).image Prod.fst).card = min m n := by
  rw [Finset.card_image_of_injOn, card_diagonal]
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' (rfl : a = a')
  exact Prod.ext rfl (Fin.ext (((mem_diagonal _ _).1 hab).symm.trans ((mem_diagonal _ _).1 hab')))

theorem card_image_snd_diagonal (m n : ℕ) :
    ((diagonal m n).image Prod.snd).card = min m n := by
  rw [Finset.card_image_of_injOn, card_diagonal]
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' (rfl : b = b')
  exact Prod.ext (Fin.ext (((mem_diagonal _ _).1 hab).trans ((mem_diagonal _ _).1 hab').symm)) rfl

theorem maxViol_of_diagonal
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViol r₁ r₂ = (c.form r₁).length - (c.form r₂).length := by
  rw [maxViol, hedge, Finset.card_univ_sdiff, card_image_fst_diagonal, Fintype.card_fin]
  omega

theorem depViol_of_diagonal
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViol r₁ r₂ = (c.form r₂).length - (c.form r₁).length := by
  rw [depViol, hedge, Finset.card_univ_sdiff, card_image_snd_diagonal, Fintype.card_fin]
  omega

theorem maxViol_eq_zero_of_diagonal (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViol r₁ r₂ = 0 := by
  rw [maxViol_of_diagonal c r₁ r₂ hedge, hform, Nat.sub_self]

theorem depViol_eq_zero_of_diagonal (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViol r₁ r₂ = 0 := by
  rw [depViol_of_diagonal c r₁ r₂ hedge, hform, Nat.sub_self]

theorem identViolFeature_eq_zero_of_diagonal {F : Type*} [DecidableEq F] (proj : α → F)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViolFeature proj r₁ r₂ = 0 := by
  simp only [identViolFeature, hedge, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
  rintro ⟨i, j⟩ hij
  have hij : (i : ℕ) = j := (mem_diagonal i j).1 hij
  have h : (c.form r₁)[(i : ℕ)]? = (c.form r₂)[(j : ℕ)]? := by rw [hij, hform]
  rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem j.2, Option.some_inj] at h
  exact congrArg proj h

theorem identViol_eq_zero_of_diagonal [DecidableEq α] (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViol r₁ r₂ = 0 :=
  identViolFeature_eq_zero_of_diagonal c r₁ r₂ id hform hedge

@[simp] theorem maxViol_identity (s : List α) : (identity s).maxViol .lhs .rhs = 0 :=
  maxViol_eq_zero_of_diagonal _ _ _ rfl (parallel_edge_lhs_rhs s s)

@[simp] theorem depViol_identity (s : List α) : (identity s).depViol .lhs .rhs = 0 :=
  depViol_eq_zero_of_diagonal _ _ _ rfl (parallel_edge_lhs_rhs s s)

@[simp] theorem identViol_identity [DecidableEq α] (s : List α) :
    (identity s).identViol .lhs .rhs = 0 :=
  identViol_eq_zero_of_diagonal _ _ _ rfl (parallel_edge_lhs_rhs s s)

@[simp] theorem identViolFeature_identity {F : Type*} [DecidableEq F] (proj : α → F)
    (s : List α) : (identity s).identViolFeature proj .lhs .rhs = 0 :=
  identViolFeature_eq_zero_of_diagonal _ _ _ proj rfl (parallel_edge_lhs_rhs s s)

/-! ### Diagonal edges as zips

On a diagonal edge the `i`-th positions of the two strings correspond, so a feature family counts
the offending pairs of their `List.zip`. -/

private theorem lt_of_lt_length_zip {β : Type*} {l₁ : List α} {l₂ : List β} {i : ℕ}
    (h : i < (l₁.zip l₂).length) : i < l₁.length ∧ i < l₂.length := by
  simpa [List.length_zip] using h

theorem card_filter_diagonal {β : Type*} (l₁ : List α) (l₂ : List β) (q : α × β → Prop)
    [DecidablePred q] :
    ((diagonal l₁.length l₂.length).filter fun p ↦ q (l₁[p.1], l₂[p.2])).card =
      (l₁.zip l₂).countP (q ·) := by
  rw [← Fin.card_filter_univ_getElem_eq_countP]
  symm
  refine Finset.card_bij (fun i _ ↦ (⟨i, (lt_of_lt_length_zip i.2).1⟩,
    ⟨i, (lt_of_lt_length_zip i.2).2⟩)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi
    simpa [mem_diagonal, List.getElem_zip] using hi
  · intro i _ j _ h
    exact Fin.ext (congrArg (fun p ↦ (p.1 : ℕ)) h)
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, mem_diagonal] at hab
    have hb : (a : ℕ) < l₂.length := hab.1 ▸ b.2
    refine ⟨⟨a, by simp [List.length_zip, hb]⟩, by simpa [List.getElem_zip, hab.1] using hab.2,
      ?_⟩
    ext <;> simp [hab.1]

theorem maxViolFeature_of_diagonal (P : α → Prop) [DecidablePred P]
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViolFeature P r₁ r₂ = ((c.form r₁).zip (c.form r₂)).countP fun p ↦ P p.1 ∧ ¬ P p.2 := by
  rw [maxViolFeature, hedge]
  exact card_filter_diagonal _ _ fun p ↦ P p.1 ∧ ¬ P p.2

theorem depViolFeature_of_diagonal (P : α → Prop) [DecidablePred P]
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViolFeature P r₁ r₂ = ((c.form r₁).zip (c.form r₂)).countP fun p ↦ ¬ P p.1 ∧ P p.2 := by
  rw [depViolFeature, hedge]
  exact card_filter_diagonal _ _ fun p ↦ ¬ P p.1 ∧ P p.2

theorem identViolFeature_of_diagonal {F : Type*} [DecidableEq F] (proj : α → F)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViolFeature proj r₁ r₂ =
      ((c.form r₁).zip (c.form r₂)).countP fun p ↦ proj p.1 ≠ proj p.2 := by
  rw [identViolFeature, hedge]
  exact card_filter_diagonal _ _ fun p ↦ proj p.1 ≠ proj p.2

/-- The index pairs `(0, 0), …, (k - 1, k - 1)` give the diagonal once `k` reaches the shorter
string. -/
theorem edgeOfPairs_diagonalPairs {m n k : ℕ} (h : min m n ≤ k) :
    edgeOfPairs m n (diagonalPairs k) = diagonal m n := by
  ext ⟨a, b⟩
  simp only [mem_edgeOfPairs, diagonalPairs, List.mem_map, List.mem_range, Prod.mk.injEq,
    mem_diagonal]
  refine ⟨fun ⟨i, _, hia, hib⟩ ↦ hia.symm.trans hib, fun hab ↦ ⟨a, ?_, rfl, hab⟩⟩
  have := a.2
  have := b.2
  omega

/-! ### Symmetric correspondences

Read along the reverse edge of a symmetric correspondence, MAX is DEP and IDENT is unchanged. -/

namespace IsSymmetric

variable {c} (h : c.IsSymmetric)
include h

theorem maxViolAt_eq (P : ℕ → Prop) [DecidablePred P] :
    c.maxViolAt P r₂ r₁ = c.depViolAt P r₁ r₂ := by
  rw [maxViolAt, depViolAt, h r₁ r₂, Finset.image_image]
  rfl

theorem maxViol_eq : c.maxViol r₂ r₁ = c.depViol r₁ r₂ := by
  rw [← maxViolAt_true, ← depViolAt_true, h.maxViolAt_eq]

theorem identViol_eq [DecidableEq α] : c.identViol r₂ r₁ = c.identViol r₁ r₂ := by
  simp only [identViol, h r₁ r₂, Finset.filter_image,
    Finset.card_image_of_injective _ Prod.swap_injective]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ ne_comm)

end IsSymmetric

/-! ### Edges that are graphs

When `rel r₁ r₂` is the graph of a map `f` from the positions of `form r₁` to those of `form r₂`,
the edge violates neither MAX nor INTEGRITY, DEP counts the positions off the range of `f`, and
UNIFORMITY and LINEARITY hold when `f` is injective and monotone. -/

section Graph

variable {c r₁ r₂} {f : Fin (c.form r₁).length → Fin (c.form r₂).length}
  (hf : c.rel r₁ r₂ = Function.graph f)
include hf

theorem mem_edge_iff_of_graph {i : Fin (c.form r₁).length} {j : Fin (c.form r₂).length} :
    (i, j) ∈ c.edge r₁ r₂ ↔ f i = j := by
  rw [← mem_rel, hf, Function.mem_graph]

theorem maxViol_eq_zero_of_graph : c.maxViol r₁ r₂ = 0 :=
  (maxViol_eq_zero_iff c r₁ r₂).2 <| hf ▸ Set.eq_univ_of_forall fun i ↦ ⟨f i, rfl⟩

theorem depViol_eq_zero_of_graph (hsurj : Function.Surjective f) : c.depViol r₁ r₂ = 0 :=
  (depViol_eq_zero_iff c r₁ r₂).2 <| hf ▸ Set.eq_univ_of_forall hsurj

theorem depViolAt_of_graph (P : ℕ → Prop) [DecidablePred P] :
    c.depViolAt P r₁ r₂ =
      ((Finset.univ.filter fun j : Fin (c.form r₂).length ↦ P j) \ Finset.univ.image f).card := by
  rw [depViolAt]
  congr 2
  ext j
  simp [mem_edge_iff_of_graph hf]

theorem integrityViol_eq_zero_of_graph : c.integrityViol r₁ r₂ = 0 :=
  (integrityViol_eq_zero_iff c r₁ r₂).2 <| hf ▸ fun _ _ _ h h' ↦ h.symm.trans h'

theorem uniformityViol_eq_zero_of_graph (hinj : Function.Injective f) :
    c.uniformityViol r₁ r₂ = 0 :=
  (uniformityViol_eq_zero_iff c r₁ r₂).2 <| hf ▸ fun _ _ _ h h' ↦ hinj (h.trans h'.symm)

theorem linearityViol_eq_zero_of_graph (hmono : Monotone f) : c.linearityViol r₁ r₂ = 0 :=
  (linearityViol_eq_zero_iff c r₁ r₂).2 <| hf ▸ fun _ _ h _ _ h' hlt ↦ h ▸ h' ▸ hmono hlt.le

theorem identViol_eq_zero_iff_of_graph [DecidableEq α] :
    c.identViol r₁ r₂ = 0 ↔ ∀ i, (c.form r₁)[i] = (c.form r₂)[f i] := by
  simp only [identViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
  refine ⟨fun H i ↦ H ((mem_edge_iff_of_graph hf).2 rfl), ?_⟩
  rintro H ⟨i, j⟩ hij
  rw [← (mem_edge_iff_of_graph hf).1 hij]
  exact H i

end Graph

/-! ### Faithfulness as order isomorphism -/

/-- An edge is *faithful* when it has no MAX, DEP, INTEGRITY, UNIFORMITY, or LINEARITY
violation. -/
structure IsFaithful : Prop where
  max : c.maxViol r₁ r₂ = 0
  dep : c.depViol r₁ r₂ = 0
  integrity : c.integrityViol r₁ r₂ = 0
  uniformity : c.uniformityViol r₁ r₂ = 0
  linearity : c.linearityViol r₁ r₂ = 0

/-- A relation with no MAX or INTEGRITY violation is the graph of a map of positions. -/
theorem exists_rel_eq_graph (hmax : c.maxViol r₁ r₂ = 0) (hint : c.integrityViol r₁ r₂ = 0) :
    ∃ f : Fin (c.form r₁).length → Fin (c.form r₂).length, c.rel r₁ r₂ = Function.graph f := by
  rw [maxViol_eq_zero_iff] at hmax
  rw [integrityViol_eq_zero_iff] at hint
  choose f hf using Set.eq_univ_iff_forall.1 hmax
  exact ⟨f, Set.ext fun ⟨i, j⟩ ↦ ⟨fun h ↦ hint (hf i) h, fun (h : f i = j) ↦ h ▸ hf i⟩⟩

/-- With no UNIFORMITY or LINEARITY violation either, the map is an order embedding: UNIFORMITY
rules out collisions and LINEARITY inversions. -/
theorem exists_orderEmbedding_rel_eq_graph (hmax : c.maxViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) (huni : c.uniformityViol r₁ r₂ = 0)
    (hlin : c.linearityViol r₁ r₂ = 0) :
    ∃ f : Fin (c.form r₁).length ↪o Fin (c.form r₂).length, c.rel r₁ r₂ = Function.graph f := by
  obtain ⟨f, hf⟩ := exists_rel_eq_graph c r₁ r₂ hmax hint
  rw [uniformityViol_eq_zero_iff, hf] at huni
  rw [linearityViol_eq_zero_iff, hf] at hlin
  exact ⟨.ofStrictMono f fun a b hab ↦
    (hlin rfl rfl hab).lt_of_ne fun h ↦ hab.ne (huni h rfl), hf⟩

/-- An edge is faithful exactly when it is the graph of an order isomorphism between the
positions of the two strings. -/
theorem isFaithful_iff_exists_orderIso :
    c.IsFaithful r₁ r₂ ↔
      ∃ e : Fin (c.form r₁).length ≃o Fin (c.form r₂).length, c.rel r₁ r₂ = Function.graph e := by
  constructor
  · rintro ⟨hmax, hdep, hint, huni, hlin⟩
    obtain ⟨f, hf⟩ := exists_orderEmbedding_rel_eq_graph c r₁ r₂ hmax hint huni hlin
    rw [depViol_eq_zero_iff, hf] at hdep
    exact ⟨StrictMono.orderIsoOfSurjective f f.strictMono (Set.eq_univ_iff_forall.1 hdep), hf⟩
  · rintro ⟨e, he⟩
    exact ⟨maxViol_eq_zero_of_graph he, depViol_eq_zero_of_graph he e.surjective,
      integrityViol_eq_zero_of_graph he, uniformityViol_eq_zero_of_graph he e.injective,
      linearityViol_eq_zero_of_graph he e.monotone⟩

/-- There is one faithful edge between two strings, the diagonal, and only when they are equally
long. -/
theorem isFaithful_iff_edge_eq_diagonal :
    c.IsFaithful r₁ r₂ ↔ (c.form r₁).length = (c.form r₂).length ∧
      c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length := by
  rw [isFaithful_iff_exists_orderIso]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨by simpa using Fintype.card_congr e.toEquiv, Finset.ext fun ⟨i, j⟩ ↦ ?_⟩
    rw [mem_edge_iff_of_graph he, mem_diagonal, Fin.ext_iff, Fin.coe_orderIso_apply]
  · rintro ⟨hlen, hedge⟩
    refine ⟨Fin.castOrderIso hlen, Set.ext fun ⟨i, j⟩ ↦ ?_⟩
    rw [mem_rel, hedge, mem_diagonal]
    exact (Fin.ext_iff (a := Fin.cast hlen i)).symm

variable {c r₁ r₂} in
theorem IsFaithful.length_eq (h : c.IsFaithful r₁ r₂) :
    (c.form r₁).length = (c.form r₂).length :=
  ((isFaithful_iff_edge_eq_diagonal c r₁ r₂).1 h).1

variable {c r₁ r₂} in
theorem IsFaithful.contigIViol_eq_zero (h : c.IsFaithful r₁ r₂) : c.contigIViol r₁ r₂ = 0 :=
  contigIViol_eq_zero_of_maxViol_eq_zero c r₁ r₂ h.max

variable {c r₁ r₂} in
theorem IsFaithful.contigOViol_eq_zero (h : c.IsFaithful r₁ r₂) : c.contigOViol r₁ r₂ = 0 :=
  contigOViol_eq_zero_of_depViol_eq_zero c r₁ r₂ h.dep

variable {c r₁ r₂} in
theorem IsFaithful.anchorLViol_eq_zero (h : c.IsFaithful r₁ r₂) : c.anchorLViol r₁ r₂ = 0 := by
  obtain ⟨e, he⟩ := (isFaithful_iff_exists_orderIso c r₁ r₂).1 h
  exact (anchorLViol_eq_zero_iff c r₁ r₂).2 fun i j hi hj ↦
    he ▸ le_antisymm (e.le_symm_apply.1 (hi _)) (hj _)

variable {c r₁ r₂} in
theorem IsFaithful.anchorRViol_eq_zero (h : c.IsFaithful r₁ r₂) : c.anchorRViol r₁ r₂ = 0 := by
  obtain ⟨e, he⟩ := (isFaithful_iff_exists_orderIso c r₁ r₂).1 h
  exact (anchorRViol_eq_zero_iff c r₁ r₂).2 fun i j hi hj ↦
    he ▸ le_antisymm (hj _) (e.symm_apply_le.1 (hi _))

/-- An edge that violates no constraint relates a string to itself along the diagonal, as in the
fully faithful candidate `identity s`. -/
theorem isFaithful_and_identViol_eq_zero_iff [DecidableEq α] :
    c.IsFaithful r₁ r₂ ∧ c.identViol r₁ r₂ = 0 ↔ c.form r₁ = c.form r₂ ∧
      c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length := by
  rw [isFaithful_iff_edge_eq_diagonal]
  constructor
  · rintro ⟨⟨hlen, hedge⟩, hid⟩
    refine ⟨List.ext_getElem hlen fun i h₁ h₂ ↦ ?_, hedge⟩
    simp only [identViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not] at hid
    exact hid (x := (⟨i, h₁⟩, ⟨i, h₂⟩)) (hedge ▸ (mem_diagonal _ _).2 rfl)
  · rintro ⟨hform, hedge⟩
    exact ⟨⟨congrArg List.length hform, hedge⟩, identViol_eq_zero_of_diagonal c r₁ r₂ hform hedge⟩

/-! ### Faithfulness and markedness constraints

A constraint over correspondences is faithfulness when the fully faithful candidate satisfies
it, and markedness when it reads only the output string. The constraint counting the segments
of the output is markedness and not faithfulness (`exists_isMarkedness_not_isFaithfulness`). -/

/-- A constraint over binary correspondences is *faithfulness* when the fully faithful candidate
`identity s` satisfies it. -/
def IsFaithfulness (k : Constraint (Correspondence BinaryRole α)) : Prop :=
  ∀ s : List α, k (identity s) = 0

/-- A constraint is *markedness* for the role `out` when it depends only on `form out`. -/
def IsMarkedness (out : Role) (k : Constraint (Correspondence Role α)) : Prop :=
  k.FactorsThrough (·.form out)

theorem isMarkedness_comap (out : Role) (m : Constraint (List α)) :
    IsMarkedness out (m.comap (·.form out)) :=
  Function.FactorsThrough.rfl.comp_left m

/-- A constraint is markedness for the role `out` exactly when it is a constraint on strings
pulled back along `form out`. -/
theorem isMarkedness_iff_exists_comap (out : Role) (k : Constraint (Correspondence Role α)) :
    IsMarkedness out k ↔ ∃ m : Constraint (List α), k = m.comap (·.form out) :=
  Function.factorsThrough_iff k

theorem isFaithfulness_maxViol : IsFaithfulness (α := α) (maxViol · .lhs .rhs) :=
  maxViol_identity

theorem isFaithfulness_depViol : IsFaithfulness (α := α) (depViol · .lhs .rhs) :=
  depViol_identity

theorem isFaithfulness_identViol [DecidableEq α] :
    IsFaithfulness (α := α) (identViol · .lhs .rhs) :=
  identViol_identity

/-- The anti-faithfulness constraint of a faithfulness constraint is not faithfulness, since the
fully faithful candidate violates it. -/
theorem IsFaithfulness.not_antifaithful {k : Constraint (Correspondence BinaryRole α)}
    (hk : IsFaithfulness k) : ¬ IsFaithfulness k.antifaithful := fun h ↦ by
  simpa [Constraint.antifaithful_eq_zero_iff, hk []] using h []

theorem exists_isMarkedness_not_isFaithfulness [Inhabited α] :
    ∃ k : Constraint (Correspondence BinaryRole α), IsMarkedness .rhs k ∧ ¬ IsFaithfulness k :=
  ⟨fun c ↦ (c.form .rhs).length, fun _ _ h ↦ by simp [h],
    fun h ↦ by simpa [identity] using h [default]⟩

end Correspondence

end OptimalityTheory
