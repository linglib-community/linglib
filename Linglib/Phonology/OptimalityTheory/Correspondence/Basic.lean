/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Fintype.Card
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.Fintype.Fin

/-!
# Correspondence Theory

A correspondence between two strings ([mccarthy-prince-1995] (10)) is a relation ℛ
between their positions, and a faithfulness constraint is a condition on ℛ: MAX reads
its domain, DEP its range, IDENT the segments at corresponding positions.
`Correspondence Role α` carries one string per role (`form`) and the relation
`edge r₁ r₂` for every ordered pair of roles, so the input–output, base–reduplicant
and output–output ([benua-1997]) relations of one candidate are cells of a single
diagram. The relation is directed, as ℛ is; "correspondents of one another" is the
derived property `IsSymmetric`.

The constraints of Appendix A are families `Correspondence Role α → Role → Role → ℕ`
counting offending elements; a named constraint is a partial application (MAX-IO is
`(·.maxViol .input .output)`), and each cardinal family vanishes iff the relation has
the matching order-theoretic property (`maxViol_eq_zero_iff`, …). Positions are
`Fin`-indexed, so every pair of `edge` is in range by type. The position-relation
encoding follows [payne-vu-heinz-2017] and [potts-pullum-2002] (base–reduplicant
relations: [dolatian-heinz-2020]).

## Main definitions

* `Correspondence` — role-indexed strings with a directed relation between the
  positions of each ordered pair of roles.
* `Correspondence.maxViol`, `depViol`, `identViol`, `identViolFeature`, `contigIViol`,
  `contigOViol`, `anchorLViol`, `anchorRViol`, `linearityViol`, `uniformityViol`,
  `integrityViol` — the constraint families of Appendix A; `maxViolOn`, `depViolOn` are
  their segment-class restrictions (MAX-V, DEP-C, …), and `maxViolAt`, `depViolAt` their
  restrictions to positions (positional faithfulness).
* `Correspondence.ofPairs`, `diagram`, `parallel`, `identity`, `reduplication` —
  constructors: from index pairs, the diagonal on a role predicate, and the binary
  and input–base–reduplicant diagonal diagrams.
* `Correspondence.IsSymmetric`, `IsFaithful` — symmetry of the relation; freedom from
  the five order-relevant violations on an edge.
* `Correspondence.IsFaithfulness`, `IsMarkedness` — the structural
  faithfulness/markedness split for constraints over correspondences.

## Main results

* `Correspondence.isFaithful_iff_exists_orderIso` — an edge is faithful iff it is the
  graph of an order isomorphism between the two position orders.
* `Correspondence.diagram_isSymmetric` — a diagonal diagram over a symmetric role
  predicate is symmetric.
* `Correspondence.isMarkedness_iff_exists_comap` — a markedness constraint is exactly a
  constraint on strings pulled back along the output form.
* `Correspondence.maxViolFeature_of_diagonal`, `depViolFeature_of_diagonal`,
  `identViolFeature_of_diagonal` — on a diagonal edge a feature family counts the offending pairs
  of the two strings' `List.zip`; `Correspondence.edgeOfPairs_diagonalPairs` — the index pairs
  `(i, i)` give the diagonal.
* `Correspondence.IsFaithfulness.not_antifaithful` — the anti-faithfulness constraint of a
  faithfulness constraint is not faithfulness.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [L. Benua, *Transderivational Identity: Phonological Relations between Words*
  (1997)][benua-1997]
* [A. Payne, M. H. Vu and J. Heinz, *A Formal Analysis of Correspondence Theory*
  (2017)][payne-vu-heinz-2017]
* [C. Potts and G. K. Pullum, *Model Theory and the Content of OT Constraints*
  (2002)][potts-pullum-2002]
* [H. Dolatian and J. Heinz, *Computing and Classifying Reduplication with 2-Way Finite-State
  Transducers* (2020)][dolatian-heinz-2020]
-/

@[expose] public section

namespace OptimalityTheory

/-- A correspondence diagram consists of a string for each role and, for each ordered pair of
roles, a directed relation between their positions. -/
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

variable {Role : Type*} {α : Type*}

/-- Correspondence is symmetric when each relation is the converse of the reverse
one. -/
def IsSymmetric (c : Correspondence Role α) : Prop :=
  ∀ r₁ r₂, c.edge r₂ r₁ = (c.edge r₁ r₂).image Prod.swap

/-! ### Constraint families -/

/-- MAX (A.1) counts the positions of `form r₁` without a correspondent in `form r₂`. -/
def maxViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.fst).card

/-- DEP (A.2) counts the positions of `form r₂` without a correspondent in `form r₁`. -/
def depViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.snd).card

/-- MAX (A.1) restricted to the positions of `form r₁` whose segment satisfies `P` — the
segment-class instances MAX-V, MAX-C. -/
def maxViolOn (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((Finset.univ.filter fun i : Fin (c.form r₁).length => P (c.form r₁)[i]) \
    (c.edge r₁ r₂).image Prod.fst).card

/-- DEP (A.2) restricted to the positions of `form r₂` whose segment satisfies `P` — the
segment-class instances DEP-V, DEP-C. -/
def depViolOn (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((Finset.univ.filter fun j : Fin (c.form r₂).length => P (c.form r₂)[j]) \
    (c.edge r₁ r₂).image Prod.snd).card

/-- MAX restricted to the positions of `form r₁` that satisfy `P`, the positional
faithfulness constraints that protect a segment by where it stands, not by what it is. -/
def maxViolAt (P : ℕ → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ.filter fun i : Fin (c.form r₁).length ↦ P i) \
    (c.edge r₁ r₂).image Prod.fst).card

/-- DEP restricted to the positions of `form r₂` that satisfy `P`. -/
def depViolAt (P : ℕ → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ.filter fun j : Fin (c.form r₂).length ↦ P j) \
    (c.edge r₁ r₂).image Prod.snd).card

/-- IDENT (A.3) on whole segments counts the corresponding pairs whose segments differ. -/
def identViol [DecidableEq α] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p => (c.form r₁)[p.1] ≠ (c.form r₂)[p.2]).card

/-- IDENT(F) (A.3) for the feature `proj` counts the corresponding pairs that differ under
`proj`. -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p => proj (c.form r₁)[p.1] ≠ proj (c.form r₂)[p.2]).card

/-- MAX of a privative property along a segmental correspondence counts the corresponding
pairs whose first member has `P` and whose second lacks it, the autosegment being lost. -/
def maxViolFeature (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((c.edge r₁ r₂).filter fun p => P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2]).card

/-- DEP of a privative property along a segmental correspondence counts the corresponding pairs
whose second member has `P` and whose first lacks it, the autosegment being inserted. -/
def depViolFeature (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((c.edge r₁ r₂).filter fun p => ¬ P (c.form r₁)[p.1] ∧ P (c.form r₂)[p.2]).card

theorem maxViolFeature_pos_iff (P : α → Prop) [DecidablePred P] (c : Correspondence Role α)
    (r₁ r₂ : Role) :
    0 < maxViolFeature P c r₁ r₂ ↔
      ∃ p ∈ c.edge r₁ r₂, P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2] := by
  simp [maxViolFeature, Finset.card_pos, Finset.filter_nonempty_iff]

/-- I-CONTIG, "No Skipping" (A.4a), checks whether the domain of the relation is a contiguous
substring of `form r₁`. -/
def contigIViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ((((c.edge r₁ r₂).image Prod.fst).image Fin.val).sort (· ≤ ·)).IsChain
      (fun a b => b = a + 1) then 0 else 1

/-- O-CONTIG, "No Intrusion" (A.4b), checks whether the range of the relation is a contiguous
substring of `form r₂`. -/
def contigOViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ((((c.edge r₁ r₂).image Prod.snd).image Fin.val).sort (· ≤ ·)).IsChain
      (fun a b => b = a + 1) then 0 else 1

/-- L-ANCHOR (A.5) checks whether the leftmost positions correspond, and is vacuous when either
string is empty. -/
def anchorLViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if h : 0 < (c.form r₁).length ∧ 0 < (c.form r₂).length then
    if (⟨0, h.1⟩, ⟨0, h.2⟩) ∈ c.edge r₁ r₂ then 0 else 1
  else 0

/-- R-ANCHOR (A.5) checks whether the rightmost positions correspond, and is vacuous when
either string is empty. -/
def anchorRViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if h : 0 < (c.form r₁).length ∧ 0 < (c.form r₂).length then
    if (⟨(c.form r₁).length - 1, Nat.pred_lt_self h.1⟩,
        ⟨(c.form r₂).length - 1, Nat.pred_lt_self h.2⟩) ∈ c.edge r₁ r₂ then 0 else 1
  else 0

/-- LINEARITY, "No Metathesis" (A.6), counts the pairs of correspondences `(i₁, j₁)`,
`(i₂, j₂)` with `i₁ < i₂` but `j₂ < j₁`. -/
def linearityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂ ×ˢ c.edge r₁ r₂).filter fun pq => pq.1.1 < pq.2.1 ∧ pq.2.2 < pq.1.2).card

/-- UNIFORMITY, "No Coalescence" (A.7), counts the positions of `form r₂` with more than one
correspondent in `form r₁`. -/
def uniformityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₂).length)).filter fun j =>
    1 < ((c.edge r₁ r₂).filter fun p => p.2 = j).card).card

/-- INTEGRITY, "No Breaking" (A.8), counts the positions of `form r₁` with more than one
correspondent in `form r₂`. -/
def integrityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₁).length)).filter fun i =>
    1 < ((c.edge r₁ r₂).filter fun p => p.1 = i).card).card

/-! ### Vanishing characterizations

Each cardinal constraint vanishes iff the relation has the corresponding order-theoretic
property: left-total, right-total, functional, injective, order-preserving. -/

variable (c : Correspondence Role α) (r₁ r₂ : Role)

theorem maxViol_eq_zero_iff :
    c.maxViol r₁ r₂ = 0 ↔ Finset.univ ⊆ (c.edge r₁ r₂).image Prod.fst := by
  simp only [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem depViol_eq_zero_iff :
    c.depViol r₁ r₂ = 0 ↔ Finset.univ ⊆ (c.edge r₁ r₂).image Prod.snd := by
  simp only [depViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem maxViolOn_true : maxViolOn (fun _ => True) c r₁ r₂ = c.maxViol r₁ r₂ := by
  simp [maxViolOn, maxViol]

theorem depViolOn_true : depViolOn (fun _ => True) c r₁ r₂ = c.depViol r₁ r₂ := by
  simp [depViolOn, depViol]

theorem maxViolAt_true : maxViolAt (fun _ ↦ True) c r₁ r₂ = c.maxViol r₁ r₂ := by
  simp [maxViolAt, maxViol]

theorem depViolAt_true : depViolAt (fun _ ↦ True) c r₁ r₂ = c.depViol r₁ r₂ := by
  simp [depViolAt, depViol]

theorem integrityViol_eq_zero_iff :
    c.integrityViol r₁ r₂ = 0 ↔ ∀ i, ((c.edge r₁ r₂).filter fun p => p.1 = i).card ≤ 1 := by
  simp [integrityViol, Finset.filter_eq_empty_iff]

theorem uniformityViol_eq_zero_iff :
    c.uniformityViol r₁ r₂ = 0 ↔ ∀ j, ((c.edge r₁ r₂).filter fun p => p.2 = j).card ≤ 1 := by
  simp [uniformityViol, Finset.filter_eq_empty_iff]

theorem linearityViol_eq_zero_iff :
    c.linearityViol r₁ r₂ = 0 ↔
      ∀ p ∈ c.edge r₁ r₂, ∀ q ∈ c.edge r₁ r₂, p.1 < q.1 → ¬ q.2 < p.2 := by
  rw [linearityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact ⟨fun h p hp q hq hpq hqp => h (Finset.mk_mem_product hp hq) ⟨hpq, hqp⟩,
    fun h pq hpq hinv => h _ (Finset.mem_product.1 hpq).1 _ (Finset.mem_product.1 hpq).2
      hinv.1 hinv.2⟩

/-! ### Constructors -/

/-- The index pairs `(0, 0), …, (k - 1, k - 1)` of a parallel correspondence. -/
def diagonalPairs (k : ℕ) : List (ℕ × ℕ) := (List.range k).map fun i => (i, i)

/-- The relation on positions given by index pairs; pairs out of range are dropped. -/
def edgeOfPairs (m n : ℕ) (l : List (ℕ × ℕ)) : Finset (Fin m × Fin n) :=
  (l.filterMap fun p =>
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
    fun i => (i.castLE (min_le_left _ _), i.castLE (min_le_right _ _))

@[simp] theorem mem_diagonal {m n : ℕ} (a : Fin m) (b : Fin n) :
    (a, b) ∈ diagonal m n ↔ (a : ℕ) = (b : ℕ) := by
  simp only [diagonal, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff,
    Fin.val_castLE]
  exact ⟨fun ⟨_, h₁, h₂⟩ => h₁.symm.trans h₂,
    fun h => ⟨⟨a, by have := a.2; have := b.2; omega⟩, rfl, h⟩⟩

theorem card_diagonal (m n : ℕ) : (diagonal m n).card = min m n := by
  rw [diagonal, Finset.card_image_of_injective _ fun _ _ h => Fin.ext (congrArg (·.1.1) h),
    Finset.card_univ, Fintype.card_fin]

theorem image_swap_diagonal (m n : ℕ) : (diagonal m n).image Prod.swap = diagonal n m := by
  ext ⟨a, b⟩
  simp only [Finset.mem_image, mem_diagonal, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  exact ⟨fun ⟨_, _, h, rfl, rfl⟩ => h.symm, fun h => ⟨b, a, h.symm, rfl, rfl⟩⟩

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

MAX, DEP and IDENT vanish on a diagonal edge between equal strings — the fully faithful
candidate, and total reduplication read on its base–reduplicant edge. -/

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

An edge is the graph of a map `f` from the positions of `form r₁` to those of `form r₂` when each
position `i` corresponds to `f i` alone. Such an edge violates neither MAX nor INTEGRITY, DEP
counts the positions off the range of `f`, and UNIFORMITY and LINEARITY hold when `f` is injective
and monotone. -/

section Graph

variable {c r₁ r₂} {f : Fin (c.form r₁).length → Fin (c.form r₂).length}
  (hf : ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ f i = j)
include hf

theorem maxViol_eq_zero_of_graph : c.maxViol r₁ r₂ = 0 :=
  (maxViol_eq_zero_iff c r₁ r₂).2 fun i _ ↦ Finset.mem_image.2 ⟨(i, f i), (hf _ _).2 rfl, rfl⟩

theorem depViolAt_of_graph (P : ℕ → Prop) [DecidablePred P] :
    c.depViolAt P r₁ r₂ =
      ((Finset.univ.filter fun j : Fin (c.form r₂).length ↦ P j) \ Finset.univ.image f).card := by
  rw [depViolAt]
  congr 2
  ext j
  simp [hf]

theorem integrityViol_eq_zero_of_graph : c.integrityViol r₁ r₂ = 0 :=
  (integrityViol_eq_zero_iff c r₁ r₂).2 fun _ ↦ Finset.card_le_one.2 fun p hp q hq ↦ by
    rw [Finset.mem_filter] at hp hq
    refine Prod.ext (hp.2.trans hq.2.symm) ?_
    rw [← (hf _ _).1 hp.1, ← (hf _ _).1 hq.1, hp.2, hq.2]

theorem uniformityViol_eq_zero_of_graph (hinj : Function.Injective f) :
    c.uniformityViol r₁ r₂ = 0 :=
  (uniformityViol_eq_zero_iff c r₁ r₂).2 fun _ ↦ Finset.card_le_one.2 fun p hp q hq ↦ by
    rw [Finset.mem_filter] at hp hq
    refine Prod.ext (hinj ?_) (hp.2.trans hq.2.symm)
    rw [(hf _ _).1 hp.1, (hf _ _).1 hq.1, hp.2, hq.2]

theorem linearityViol_eq_zero_of_graph (hmono : Monotone f) : c.linearityViol r₁ r₂ = 0 :=
  (linearityViol_eq_zero_iff c r₁ r₂).2 fun p hp q hq hpq ↦ by
    rw [← (hf _ _).1 hp, ← (hf _ _).1 hq]
    exact not_lt.2 (hmono hpq.le)

theorem identViol_eq_zero_iff_of_graph [DecidableEq α] :
    c.identViol r₁ r₂ = 0 ↔ ∀ i, (c.form r₁)[i] = (c.form r₂)[f i] := by
  simp only [identViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
  refine ⟨fun H i ↦ H ((hf _ _).2 rfl), ?_⟩
  rintro H ⟨i, j⟩ hij
  rw [← (hf _ _).1 hij]
  exact H i

end Graph

/-! ### Faithfulness as order isomorphism -/

/-- An edge is faithful when it has no MAX, DEP, INTEGRITY, UNIFORMITY or LINEARITY
violation — exactly the hypotheses under which it is the graph of an order
isomorphism. -/
structure IsFaithful : Prop where
  max : c.maxViol r₁ r₂ = 0
  dep : c.depViol r₁ r₂ = 0
  integrity : c.integrityViol r₁ r₂ = 0
  uniformity : c.uniformityViol r₁ r₂ = 0
  linearity : c.linearityViol r₁ r₂ = 0

theorem exists_fun_mem_edge_iff (hmax : c.maxViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) :
    ∃ f : Fin (c.form r₁).length → Fin (c.form r₂).length,
      ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ f i = j := by
  have hexU : ∀ i, ∃! j, (i, j) ∈ c.edge r₁ r₂ := fun i => by
    obtain ⟨⟨a, b⟩, hp, rfl⟩ :=
      Finset.mem_image.1 ((maxViol_eq_zero_iff c r₁ r₂).1 hmax (Finset.mem_univ i))
    have hone := Finset.card_le_one.1 ((integrityViol_eq_zero_iff c r₁ r₂).1 hint a)
    exact ⟨b, hp, fun j hj => congrArg Prod.snd
      (hone _ (Finset.mem_filter.2 ⟨hj, rfl⟩) _ (Finset.mem_filter.2 ⟨hp, rfl⟩))⟩
  choose f hf huniq using hexU
  exact ⟨f, fun i j => ⟨fun h => (huniq i j h).symm, fun h => h ▸ hf i⟩⟩

theorem exists_orderEmbedding_mem_edge_iff (hmax : c.maxViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) (huni : c.uniformityViol r₁ r₂ = 0)
    (hlin : c.linearityViol r₁ r₂ = 0) :
    ∃ f : Fin (c.form r₁).length ↪o Fin (c.form r₂).length,
      ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ f i = j := by
  obtain ⟨f, mem_iff⟩ := exists_fun_mem_edge_iff c r₁ r₂ hmax hint
  have memf : ∀ i, (i, f i) ∈ c.edge r₁ r₂ := fun i => (mem_iff i (f i)).2 rfl
  -- UNIFORMITY rules out collisions and LINEARITY inversions, so `f` is strictly monotone.
  have hmono : StrictMono f := by
    intro a b hab
    rcases lt_trichotomy (f a) (f b) with h | h | h
    · exact h
    · have hu := Finset.card_le_one.1 ((uniformityViol_eq_zero_iff c r₁ r₂).1 huni (f b))
      exact absurd (congrArg Prod.fst <| hu _ (Finset.mem_filter.2 ⟨memf a, h⟩)
        _ (Finset.mem_filter.2 ⟨memf b, rfl⟩)) (ne_of_lt hab)
    · exact absurd h ((linearityViol_eq_zero_iff c r₁ r₂).1 hlin _ (memf a) _ (memf b) hab)
  exact ⟨.ofStrictMono f hmono, mem_iff⟩

theorem isFaithful_iff_exists_orderIso :
    c.IsFaithful r₁ r₂ ↔
      ∃ e : Fin (c.form r₁).length ≃o Fin (c.form r₂).length,
        ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ e i = j := by
  constructor
  · rintro ⟨hmax, hdep, hint, huni, hlin⟩
    obtain ⟨f, mem_iff⟩ := exists_orderEmbedding_mem_edge_iff c r₁ r₂ hmax hint huni hlin
    have hsurj : Function.Surjective f := fun j => by
      obtain ⟨p, hp, hp2⟩ := Finset.mem_image.1
        ((depViol_eq_zero_iff c r₁ r₂).1 hdep (Finset.mem_univ j))
      exact ⟨p.1, (mem_iff p.1 j).1 (by simpa [← hp2] using hp)⟩
    exact ⟨StrictMono.orderIsoOfSurjective f f.strictMono hsurj,
      fun i j => by rw [mem_iff, StrictMono.coe_orderIsoOfSurjective]⟩
  · rintro ⟨e, he⟩
    refine ⟨maxViol_eq_zero_of_graph he, ?_, integrityViol_eq_zero_of_graph he,
      uniformityViol_eq_zero_of_graph he e.injective, linearityViol_eq_zero_of_graph he e.monotone⟩
    rw [← depViolAt_true, depViolAt_of_graph he, Finset.image_univ_of_surjective e.surjective]
    simp

theorem length_eq_of_isFaithful (h : c.IsFaithful r₁ r₂) :
    (c.form r₁).length = (c.form r₂).length := by
  obtain ⟨e, _⟩ := (isFaithful_iff_exists_orderIso c r₁ r₂).1 h
  simpa using Fintype.card_congr e.toEquiv

/-! ### Faithfulness and markedness constraints

A constraint over correspondences is faithfulness when the fully faithful candidate
satisfies it, and markedness when it reads only the output string. The split is
structural, and non-vacuous: \*STRUC is markedness and fires on `identity s`. -/

/-- A constraint over binary correspondences is **faithfulness** when the fully faithful
candidate `identity s` satisfies it. -/
def IsFaithfulness (k : Constraint (Correspondence BinaryRole α)) : Prop :=
  ∀ s : List α, k (identity s) = 0

/-- A constraint is **markedness** for the role `out` when it depends only on
`form out`. -/
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
  ⟨fun c => (c.form .rhs).length, fun _ _ h => by simp [h],
    fun h => by simpa [identity] using h [default]⟩

end Correspondence

end OptimalityTheory
