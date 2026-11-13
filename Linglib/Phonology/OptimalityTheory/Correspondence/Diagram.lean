/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.Fintype.Fin
public import Mathlib.Order.Fin.Basic

/-!
# Correspondence diagrams

A candidate of correspondence theory is a diagram: a string for each role and a correspondence
between the positions of each ordered pair of roles, so that the input, base, and reduplicant of
a reduplicative candidate form one object. Each constraint family is read at a pair of roles.
Between the positions of two lists there is
[one faithful correspondence](##OptimalityTheory.Correspondence.isFaithful_iff_eq_diagonal), the
diagonal between lists of equal length, and an edge that violates IDENT nowhere either relates
[a string to itself](##OptimalityTheory.Correspondence.Diagram.isFaithful_and_identViol_eq_zero_iff),
as in the fully faithful candidate.

## Implementation notes

* A named constraint is a partial application of a family to a pair of roles: MAX-IO is
  `(·.maxViol .input .output)`.
* `Correspondence.Diagram.ofPairs` reads a relation from index pairs and drops those out of
  range.
* A constraint over binary diagrams is faithfulness when the fully faithful candidate satisfies
  it, and markedness when it reads only the output string.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory

/-- A *correspondence diagram*: a string for each role and, for each ordered pair of roles, a
correspondence between their positions. -/
structure Correspondence.Diagram (Role : Type*) (α : Type*) where
  form : Role → List α
  edge : (r₁ r₂ : Role) → Correspondence (Fin (form r₁).length) (Fin (form r₂).length)

/-- The roles of a binary diagram are its two strings, as in `Correspondence.Diagram.parallel`
and `Correspondence.Diagram.identity`. -/
inductive BinaryRole where
  | lhs
  | rhs
  deriving DecidableEq, Repr

/-- `r.swap` is the other role of a binary diagram. -/
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

variable {α : Type*}

/-! ### The diagonal -/

/-- The diagonal `(0, 0), (1, 1), …` between `Fin m` and `Fin n`, one pair per index of the
shorter string. -/
def diagonal (m n : ℕ) : Correspondence (Fin m) (Fin n) :=
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

@[simp] theorem inv_diagonal (m n : ℕ) : (diagonal m n).inv = diagonal n m := by
  ext ⟨b, a⟩
  simp [eq_comm]

theorem card_image_fst_diagonal (m n : ℕ) :
    ((diagonal m n).image Prod.fst).card = min m n := by
  rw [Finset.card_image_of_injOn, card_diagonal]
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' (rfl : a = a')
  exact Prod.ext rfl (Fin.ext (((mem_diagonal _ _).1 hab).symm.trans ((mem_diagonal _ _).1 hab')))

theorem maxViol_diagonal (m n : ℕ) : (diagonal m n).maxViol = m - n := by
  rw [maxViol, Finset.card_univ_sdiff, card_image_fst_diagonal, Fintype.card_fin]
  omega

theorem depViol_diagonal (m n : ℕ) : (diagonal m n).depViol = n - m := by
  rw [depViol, inv_diagonal, maxViol_diagonal]

/-- There is one faithful correspondence between the positions of two lists, the diagonal, and
only when they are equally long. -/
theorem isFaithful_iff_eq_diagonal {m n : ℕ} {R : Correspondence (Fin m) (Fin n)} :
    R.IsFaithful ↔ m = n ∧ R = diagonal m n := by
  rw [isFaithful_iff_exists_orderIso]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨by simpa using Fintype.card_congr e.toEquiv, Finset.ext fun ⟨i, j⟩ ↦ ?_⟩
    rw [mem_iff_of_graph he, mem_diagonal, Fin.ext_iff, Fin.coe_orderIso_apply]
  · rintro ⟨rfl, rfl⟩
    exact ⟨OrderIso.refl _, Set.ext fun ⟨i, j⟩ ↦ by simp [Fin.ext_iff]⟩

/-! ### Diagonals as zips

On the diagonal the `i`-th positions of the two strings correspond, so a count of offending
pairs is a count over their `List.zip`. -/

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

/-! ### Index pairs -/

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

namespace Diagram

variable {Role : Type*}

/-- A diagram is *symmetric* when each correspondence is the converse of the reverse one. -/
def IsSymmetric (c : Diagram Role α) : Prop :=
  ∀ r₁ r₂, c.edge r₂ r₁ = (c.edge r₁ r₂).inv

/-! ### Constraint families -/

/-- MAX counts the positions of `form r₁` without a correspondent in `form r₂`. -/
def maxViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).maxViol

/-- DEP counts the positions of `form r₂` without a correspondent in `form r₁`. -/
def depViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).depViol

/-- MAX restricted to the positions of `form r₁` whose segment satisfies `P`, as in MAX-V and
MAX-C. -/
def maxViolOn (P : α → Prop) [DecidablePred P] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).maxViolOn fun i ↦ P (c.form r₁)[i]

/-- DEP restricted to the positions of `form r₂` whose segment satisfies `P`, as in DEP-V and
DEP-C. -/
def depViolOn (P : α → Prop) [DecidablePred P] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).depViolOn fun j ↦ P (c.form r₂)[j]

/-- MAX restricted to the positions of `form r₁` that satisfy `P`, which is the form of a
positional faithfulness constraint. -/
def maxViolAt (P : ℕ → Prop) [DecidablePred P] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).maxViolOn fun i : Fin (c.form r₁).length ↦ P i

/-- DEP restricted to the positions of `form r₂` that satisfy `P`. -/
def depViolAt (P : ℕ → Prop) [DecidablePred P] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).depViolOn fun j : Fin (c.form r₂).length ↦ P j

/-- IDENT(F) for the feature `proj` counts the corresponding pairs that differ under `proj`. -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F) (c : Diagram Role α)
    (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).identViol (fun i ↦ proj (c.form r₁)[i]) fun j ↦ proj (c.form r₂)[j]

/-- IDENT on whole segments counts the corresponding pairs whose segments differ. -/
def identViol [DecidableEq α] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  c.identViolFeature id r₁ r₂

/-- MAX of a privative property along a segmental correspondence counts the corresponding
pairs whose first member has `P` and whose second lacks it, the autosegment being lost. -/
def maxViolFeature (P : α → Prop) [DecidablePred P] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).maxViolFeature (fun i ↦ P (c.form r₁)[i]) fun j ↦ P (c.form r₂)[j]

/-- DEP of a privative property along a segmental correspondence counts the corresponding pairs
whose second member has `P` and whose first lacks it, the autosegment being inserted. -/
def depViolFeature (P : α → Prop) [DecidablePred P] (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).depViolFeature (fun i ↦ P (c.form r₁)[i]) fun j ↦ P (c.form r₂)[j]

/-- INTEGRITY counts the positions of `form r₁` with more than one correspondent. -/
def integrityViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).integrityViol

/-- UNIFORMITY counts the positions of `form r₂` with more than one correspondent. -/
def uniformityViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).uniformityViol

/-- LINEARITY counts the inversions of the correspondence. -/
def linearityViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).linearityViol

/-- I-CONTIG is violated once unless the domain of the correspondence is a contiguous substring
of `form r₁`. -/
def contigIViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).contigIViol

/-- O-CONTIG is violated once unless the range of the correspondence is a contiguous substring
of `form r₂`. -/
def contigOViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).contigOViol

/-- L-ANCHOR is violated once unless the leftmost positions of the two strings correspond. -/
def anchorLViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).anchorLViol

/-- R-ANCHOR is violated once unless the rightmost positions of the two strings correspond. -/
def anchorRViol (c : Diagram Role α) (r₁ r₂ : Role) : ℕ :=
  (c.edge r₁ r₂).anchorRViol

variable (c : Diagram Role α) (r₁ r₂ : Role)

theorem maxViolOn_true : maxViolOn (fun _ ↦ True) c r₁ r₂ = c.maxViol r₁ r₂ :=
  Correspondence.maxViolOn_true _

theorem depViolOn_true : depViolOn (fun _ ↦ True) c r₁ r₂ = c.depViol r₁ r₂ :=
  Correspondence.depViolOn_true _

theorem maxViolAt_true : maxViolAt (fun _ ↦ True) c r₁ r₂ = c.maxViol r₁ r₂ :=
  Correspondence.maxViolOn_true _

theorem depViolAt_true : depViolAt (fun _ ↦ True) c r₁ r₂ = c.depViol r₁ r₂ :=
  Correspondence.depViolOn_true _

/-! ### Constructors -/

/-- `ofPairs form pairs` is the diagram whose correspondence `edge r₁ r₂` reads the index pairs
`pairs r₁ r₂` into the two position types. -/
def ofPairs (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ)) : Diagram Role α where
  form := form
  edge r₁ r₂ := edgeOfPairs _ _ (pairs r₁ r₂)

@[simp] theorem ofPairs_form (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ))
    (r : Role) : (ofPairs form pairs).form r = form r := rfl

@[simp] theorem ofPairs_edge (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ)) :
    (ofPairs form pairs).edge r₁ r₂ = edgeOfPairs _ _ (pairs r₁ r₂) := rfl

/-- The diagonal correspondence on every pair of roles satisfying `hasEdge`, empty
elsewhere. -/
def diagram (form : Role → List α) (hasEdge : Role → Role → Prop) [DecidableRel hasEdge] :
    Diagram Role α where
  form := form
  edge r₁ r₂ := if hasEdge r₁ r₂ then diagonal (form r₁).length (form r₂).length else ∅

section diagram

variable (form : Role → List α) (hasEdge : Role → Role → Prop) [DecidableRel hasEdge]

@[simp] theorem diagram_form (r : Role) : (diagram form hasEdge).form r = form r := rfl

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
  · rw [diagram_edge_pos _ _ (hsymm h), diagram_edge_pos _ _ h, inv_diagonal]
  · rw [diagram_edge_neg _ _ (mt hsymm h), diagram_edge_neg _ _ h, inv_empty]

end diagram

/-- The diagonal correspondence between two strings, truncated to the shorter. -/
def parallel (s₁ s₂ : List α) : Diagram BinaryRole α :=
  diagram (fun | .lhs => s₁ | .rhs => s₂) (· ≠ ·)

/-- `identity s` is the fully faithful candidate, the diagonal correspondence of a string with
itself. -/
def identity (s : List α) : Diagram BinaryRole α := parallel s s

/-- The input–base–reduplicant diagram with diagonal correspondence between each pair of
distinct roles. -/
def reduplication (input base reduplicant : List α) : Diagram ReduplicationRole α :=
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
    (parallel s₁ s₂).edge .rhs .lhs = diagonal s₂.length s₁.length :=
  diagram_edge_pos _ _ (by decide)

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

/-- `ofFun s t f` is the binary diagram in which each position `i` of `s` has the single
correspondent `f i` in `t`. -/
def ofFun (s t : List α) (f : Fin s.length → Fin t.length) : Diagram BinaryRole α where
  form
    | .lhs => s
    | .rhs => t
  edge
    | .lhs, .rhs => graph f
    | .rhs, .lhs => (graph f).inv
    | .lhs, .lhs | .rhs, .rhs => ∅

section ofFun

variable (s t : List α) (f : Fin s.length → Fin t.length)

@[simp] theorem ofFun_form_lhs : (ofFun s t f).form .lhs = s := rfl

@[simp] theorem ofFun_form_rhs : (ofFun s t f).form .rhs = t := rfl

@[simp] theorem ofFun_edge_lhs_rhs : (ofFun s t f).edge .lhs .rhs = graph f := rfl

@[simp] theorem ofFun_edge_rhs_lhs : (ofFun s t f).edge .rhs .lhs = (graph f).inv := rfl

theorem ofFun_isSymmetric : (ofFun s t f).IsSymmetric := by
  rintro (_ | _) (_ | _) <;> first | rfl | exact (inv_inv _).symm

end ofFun

/-- `c.swap` is the binary diagram `c` with its two strings exchanged. -/
def swap (c : Diagram BinaryRole α) : Diagram BinaryRole α where
  form r := c.form r.swap
  edge r₁ r₂ := c.edge r₁.swap r₂.swap

theorem IsSymmetric.swap {c : Diagram BinaryRole α} (h : c.IsSymmetric) : c.swap.IsSymmetric :=
  fun r₁ r₂ ↦ h r₁.swap r₂.swap

theorem depViolAt_swap (c : Diagram BinaryRole α) (P : ℕ → Prop) [DecidablePred P]
    (r₁ r₂ : BinaryRole) : c.swap.depViolAt P r₁ r₂ = c.depViolAt P r₁.swap r₂.swap := rfl

theorem maxViol_swap (c : Diagram BinaryRole α) (r₁ r₂ : BinaryRole) :
    c.swap.maxViol r₁ r₂ = c.maxViol r₁.swap r₂.swap := rfl

theorem identViol_swap [DecidableEq α] (c : Diagram BinaryRole α) (r₁ r₂ : BinaryRole) :
    c.swap.identViol r₁ r₂ = c.identViol r₁.swap r₂.swap := rfl

/-! ### Faithfulness on the diagonal

MAX, DEP, and IDENT vanish on a diagonal edge between equal strings, as on the fully faithful
candidate `identity s`, and a feature family counts the offending pairs of the two strings'
`List.zip`. -/

theorem maxViol_of_diagonal
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViol r₁ r₂ = (c.form r₁).length - (c.form r₂).length := by
  rw [maxViol, hedge, maxViol_diagonal]

theorem depViol_of_diagonal
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViol r₁ r₂ = (c.form r₂).length - (c.form r₁).length := by
  rw [depViol, hedge, depViol_diagonal]

theorem maxViol_eq_zero_of_diagonal (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViol r₁ r₂ = 0 := by
  rw [maxViol_of_diagonal c r₁ r₂ hedge, hform, Nat.sub_self]

theorem depViol_eq_zero_of_diagonal (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViol r₁ r₂ = 0 := by
  rw [depViol_of_diagonal c r₁ r₂ hedge, hform, Nat.sub_self]

theorem maxViolFeature_of_diagonal (P : α → Prop) [DecidablePred P]
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViolFeature P r₁ r₂ = ((c.form r₁).zip (c.form r₂)).countP fun p ↦ P p.1 ∧ ¬ P p.2 := by
  rw [maxViolFeature, Correspondence.maxViolFeature, hedge]
  exact card_filter_diagonal _ _ fun p ↦ P p.1 ∧ ¬ P p.2

theorem depViolFeature_of_diagonal (P : α → Prop) [DecidablePred P]
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViolFeature P r₁ r₂ = ((c.form r₁).zip (c.form r₂)).countP fun p ↦ ¬ P p.1 ∧ P p.2 := by
  rw [depViolFeature, Correspondence.depViolFeature, hedge]
  exact card_filter_diagonal _ _ fun p ↦ ¬ P p.1 ∧ P p.2

theorem identViolFeature_of_diagonal {F : Type*} [DecidableEq F] (proj : α → F)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViolFeature proj r₁ r₂ =
      ((c.form r₁).zip (c.form r₂)).countP fun p ↦ proj p.1 ≠ proj p.2 := by
  rw [identViolFeature, Correspondence.identViol, hedge]
  exact card_filter_diagonal _ _ fun p ↦ proj p.1 ≠ proj p.2

theorem identViolFeature_eq_zero_of_diagonal {F : Type*} [DecidableEq F] (proj : α → F)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViolFeature proj r₁ r₂ = 0 := by
  simp only [identViolFeature, Correspondence.identViol, hedge, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, not_not]
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

/-- An edge that violates no constraint relates a string to itself along the diagonal, as in the
fully faithful candidate `identity s`. -/
theorem isFaithful_and_identViol_eq_zero_iff [DecidableEq α] :
    (c.edge r₁ r₂).IsFaithful ∧ c.identViol r₁ r₂ = 0 ↔ c.form r₁ = c.form r₂ ∧
      c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length := by
  rw [isFaithful_iff_eq_diagonal]
  constructor
  · rintro ⟨⟨hlen, hedge⟩, hid⟩
    refine ⟨List.ext_getElem hlen fun i h₁ h₂ ↦ ?_, hedge⟩
    simp only [identViol, identViolFeature, Correspondence.identViol, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, not_not, id] at hid
    exact hid (x := (⟨i, h₁⟩, ⟨i, h₂⟩)) (hedge ▸ (mem_diagonal _ _).2 rfl)
  · rintro ⟨hform, hedge⟩
    exact ⟨⟨congrArg List.length hform, hedge⟩, identViol_eq_zero_of_diagonal c r₁ r₂ hform hedge⟩

/-! ### Symmetric diagrams

Read along the reverse edge of a symmetric diagram, MAX is DEP and IDENT is unchanged. -/

namespace IsSymmetric

variable {c} (h : c.IsSymmetric)
include h

theorem maxViolAt_eq (P : ℕ → Prop) [DecidablePred P] :
    c.maxViolAt P r₂ r₁ = c.depViolAt P r₁ r₂ := by
  rw [maxViolAt, h r₁ r₂]
  rfl

theorem maxViol_eq : c.maxViol r₂ r₁ = c.depViol r₁ r₂ := by
  rw [maxViol, h r₁ r₂]
  rfl

theorem identViol_eq [DecidableEq α] : c.identViol r₂ r₁ = c.identViol r₁ r₂ := by
  rw [identViol, identViolFeature, h r₁ r₂, identViol_inv]
  rfl

end IsSymmetric

/-! ### Faithfulness and markedness constraints

A constraint over correspondences is faithfulness when the fully faithful candidate satisfies
it, and markedness when it reads only the output string. The constraint counting the segments
of the output is markedness and not faithfulness (`exists_isMarkedness_not_isFaithfulness`). -/

/-- A constraint over binary correspondences is *faithfulness* when the fully faithful candidate
`identity s` satisfies it. -/
def IsFaithfulness (k : Constraint (Diagram BinaryRole α)) : Prop :=
  ∀ s : List α, k (identity s) = 0

/-- A constraint is *markedness* for the role `out` when it depends only on `form out`. -/
def IsMarkedness (out : Role) (k : Constraint (Diagram Role α)) : Prop :=
  k.FactorsThrough (·.form out)

theorem isMarkedness_comap (out : Role) (m : Constraint (List α)) :
    IsMarkedness out (m.comap (·.form out)) :=
  Function.FactorsThrough.rfl.comp_left m

/-- A constraint is markedness for the role `out` exactly when it is a constraint on strings
pulled back along `form out`. -/
theorem isMarkedness_iff_exists_comap (out : Role) (k : Constraint (Diagram Role α)) :
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
theorem IsFaithfulness.not_antifaithful {k : Constraint (Diagram BinaryRole α)}
    (hk : IsFaithfulness k) : ¬ IsFaithfulness k.antifaithful := fun h ↦ by
  simpa [Constraint.antifaithful_eq_zero_iff, hk []] using h []

theorem exists_isMarkedness_not_isFaithfulness [Inhabited α] :
    ∃ k : Constraint (Diagram BinaryRole α), IsMarkedness .rhs k ∧ ¬ IsFaithfulness k :=
  ⟨fun c ↦ (c.form .rhs).length, fun _ _ h ↦ by simp [h],
    fun h ↦ by simpa [identity] using h [default]⟩

end Diagram

end Correspondence

end OptimalityTheory
