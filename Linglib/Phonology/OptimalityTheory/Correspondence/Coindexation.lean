/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Indices
public import Linglib.Phonology.OptimalityTheory.Correspondence.Diagram

/-!
# Coindexed candidates

A candidate of correspondence theory is a string for each role, the input and the output, or the
input, the base and the reduplicant, with a correspondence relation between each two of them. A
constraint is named for the two strings it reads, MAX-IO for the input and the output, IDENT-OI
for the output and the input, IDENT-CC for the consonants of the output among themselves. Here
each segment bears indices on its correspondence with the string of each role, and the string
of one role [as it corresponds with another](##OptimalityTheory.Correspondence.Coindexation.toward)
is a coindexed string, on which the constraint families are those of two coindexed strings.

## Implementation notes

* The segments of a role correspond with those of another through the indices each bears toward
  the other, so the relation between two roles is symmetric, and the relations of a role with
  two others are independent.
* A constraint over binary candidates is faithfulness when the fully faithful candidate
  satisfies it, and markedness when it reads only the output string.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [rose-walker-2004]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

/-- A *coindexation* of the strings of a candidate: a string for each role, each segment with
the indices it bears on its correspondence with the string of each role. -/
structure Coindexation (Role α : Type*) where
  form : Role → List (α × (Role → List ℕ))

namespace Coindexation

variable {Role α F : Type*} (c : Coindexation Role α) (r₁ r₂ : Role)

/-- The string of the role `r`. -/
def string (r : Role) : List α := (c.form r).map Prod.fst

/-- The string of `r₁` with the indices its segments bear toward `r₂`. -/
def toward : List (Segment α) := (c.form r₁).map fun x ↦ ⟨x.1, x.2 r₂⟩

/-! ### Constraint families -/

/-- MAX counts the segments of `r₁` without a correspondent in `r₂`. -/
def maxViol : ℕ := Segment.maxViol (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- DEP counts the segments of `r₂` without a correspondent in `r₁`. -/
def depViol : ℕ := Segment.depViol (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- MAX restricted to the segments of `r₁` satisfying `P`, as in MAX-V and MAX-C. -/
def maxViolOn (P : α → Prop) [DecidablePred P] (c : Coindexation Role α) (r₁ r₂ : Role) : ℕ :=
  Segment.maxViolOn P (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- DEP restricted to the segments of `r₂` satisfying `P`, as in DEP-V and DEP-C. -/
def depViolOn (P : α → Prop) [DecidablePred P] (c : Coindexation Role α) (r₁ r₂ : Role) : ℕ :=
  Segment.depViolOn P (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- MAX restricted to the positions of `r₁` that satisfy `P`, which is the form of a positional
faithfulness constraint. -/
def maxViolAt (P : ℕ → Prop) [DecidablePred P] (c : Coindexation Role α) (r₁ r₂ : Role) : ℕ :=
  Segment.maxViolAt P (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- DEP restricted to the positions of `r₂` that satisfy `P`. -/
def depViolAt (P : ℕ → Prop) [DecidablePred P] (c : Coindexation Role α) (r₁ r₂ : Role) : ℕ :=
  Segment.depViolAt P (c.toward r₁ r₂) (c.toward r₂ r₁)

theorem maxViolAt_true : maxViolAt (fun _ ↦ True) c r₁ r₂ = c.maxViol r₁ r₂ :=
  Segment.maxViolAt_true _ _

theorem depViolAt_true : depViolAt (fun _ ↦ True) c r₁ r₂ = c.depViol r₁ r₂ :=
  Segment.maxViolAt_true _ _

/-- IDENT(F) for the feature `f` counts the corresponding pairs that differ under `f`. -/
def identViolFeature [DecidableEq F] (f : α → F) (c : Coindexation Role α) (r₁ r₂ : Role) : ℕ :=
  Segment.identViol f (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- MAX of a privative property counts the corresponding pairs whose first member has `P` and
whose second lacks it, the autosegment being lost. -/
def maxViolFeature (P : α → Prop) [DecidablePred P] (c : Coindexation Role α) (r₁ r₂ : Role) :
    ℕ :=
  Segment.maxViolFeature P (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- DEP of a privative property counts the corresponding pairs whose second member has `P` and
whose first lacks it, the autosegment being inserted. -/
def depViolFeature (P : α → Prop) [DecidablePred P] (c : Coindexation Role α) (r₁ r₂ : Role) :
    ℕ :=
  Segment.depViolFeature P (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- The correspondence between the positions of `r₁` and those of `r₂`. -/
def rel : Correspondence (Fin (c.toward r₁ r₂).length) (Fin (c.toward r₂ r₁).length) :=
  ofIndices (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- INTEGRITY counts the segments of `r₁` with more than one correspondent. -/
def integrityViol : ℕ := Segment.integrityViol (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- UNIFORMITY counts the segments of `r₂` with more than one correspondent. -/
def uniformityViol : ℕ := Segment.uniformityViol (c.toward r₁ r₂) (c.toward r₂ r₁)

/-- LINEARITY counts the inversions of the correspondence. -/
def linearityViol : ℕ := (c.rel r₁ r₂).linearityViol

/-- I-CONTIG is violated once unless the segments of `r₁` with a correspondent are a contiguous
substring. -/
def contigIViol : ℕ := (c.rel r₁ r₂).contigIViol

/-- O-CONTIG is violated once unless the segments of `r₂` with a correspondent are a contiguous
substring. -/
def contigOViol : ℕ := (c.rel r₁ r₂).contigOViol

/-- L-ANCHOR is violated once unless the leftmost segments of the two strings correspond. -/
def anchorLViol : ℕ := (c.rel r₁ r₂).anchorLViol

/-- R-ANCHOR is violated once unless the rightmost segments of the two strings correspond. -/
def anchorRViol : ℕ := (c.rel r₁ r₂).anchorRViol

/-! ### Faithfulness and markedness -/

/-- The two strings coindexed position by position, the segments of each string bearing no
index toward their own. -/
def parallel (s₁ s₂ : List α) : Coindexation BinaryRole α where
  form
    | .lhs => s₁.zipIdx.map fun x ↦ (x.1, fun | .rhs => [x.2] | .lhs => [])
    | .rhs => s₂.zipIdx.map fun x ↦ (x.1, fun | .lhs => [x.2] | .rhs => [])

/-- `identity s` is the fully faithful candidate, a string and itself coindexed position by
position. -/
def identity (s : List α) : Coindexation BinaryRole α := parallel s s

theorem toward_parallel_lhs_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).toward .lhs .rhs = indexed s₁ := by
  simp [toward, parallel, indexed, Segment.ofIndex]

theorem toward_parallel_rhs_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).toward .rhs .lhs = indexed s₂ := by
  simp [toward, parallel, indexed, Segment.ofIndex]

@[simp] theorem string_parallel_lhs (s₁ s₂ : List α) : (parallel s₁ s₂).string .lhs = s₁ := by
  rw [string, parallel, List.map_map]
  exact (List.map_congr_left fun _ _ ↦ rfl).trans (List.zipIdx_map_fst 0 _)

@[simp] theorem string_parallel_rhs (s₁ s₂ : List α) : (parallel s₁ s₂).string .rhs = s₂ := by
  rw [string, parallel, List.map_map]
  exact (List.map_congr_left fun _ _ ↦ rfl).trans (List.zipIdx_map_fst 0 _)

@[simp] theorem string_identity (s : List α) (r : BinaryRole) : (identity s).string r = s := by
  cases r <;> simp [identity]

theorem toward_identity {s : List α} {r₁ r₂ : BinaryRole} (h : r₁ ≠ r₂) :
    (identity s).toward r₁ r₂ = indexed s := by
  cases r₁ <;> cases r₂ <;>
    first
    | exact absurd rfl h
    | exact toward_parallel_lhs_rhs s s
    | exact toward_parallel_rhs_lhs s s

theorem toward_identity_self (s : List α) (r : BinaryRole) :
    (identity s).toward r r = s.map fun a ↦ ⟨a, []⟩ := by
  cases r <;>
  · rw [toward, identity, parallel, List.map_map]
    conv_rhs => rw [← List.zipIdx_map_fst 0 s, List.map_map]
    exact List.map_congr_left fun x _ ↦ by simp

/-- The candidate with the strings `form` and, for each `(r₁, r₂, l)` of `pairs`, the positions
of `r₁` and `r₂` paired in `l` corresponding. -/
def ofPairs [DecidableEq Role] (form : Role → List α)
    (pairs : List (Role × Role × List (ℕ × ℕ))) : Coindexation Role α where
  form r := (form r).zipIdx.map fun x ↦ (x.1, fun r' ↦
    (((pairs.flatMap fun e ↦ e.2.2.map fun p ↦ (e.1, e.2.1, p)).zipIdx.filter fun q ↦
      (q.1.1 = r ∧ q.1.2.1 = r' ∧ q.1.2.2.1 = x.2) ∨
        (q.1.1 = r' ∧ q.1.2.1 = r ∧ q.1.2.2.2 = x.2)).map (·.2)))

/-- A constraint over binary candidates is *faithfulness* when the fully faithful candidate
`identity s` satisfies it. -/
def IsFaithfulness (k : Constraint (Coindexation BinaryRole α)) : Prop :=
  ∀ s : List α, k (identity s) = 0

/-- A constraint is *markedness* for the role `out` when it depends only on the string of
`out`. -/
def IsMarkedness (out : Role) (k : Constraint (Coindexation Role α)) : Prop :=
  k.FactorsThrough (·.string out)

theorem isFaithfulness_maxViol : IsFaithfulness (α := α) (maxViol · .lhs .rhs) := fun s ↦ by
  show Segment.maxViol ((identity s).toward .lhs .rhs) ((identity s).toward .rhs .lhs) = 0
  rw [toward_identity (by decide), toward_identity (by decide)]
  exact maxViol_indexed_self s

theorem isFaithfulness_depViol : IsFaithfulness (α := α) (depViol · .lhs .rhs) := fun s ↦ by
  show Segment.maxViol ((identity s).toward .rhs .lhs) ((identity s).toward .lhs .rhs) = 0
  rw [toward_identity (by decide), toward_identity (by decide)]
  exact maxViol_indexed_self s

theorem isFaithfulness_identViolFeature [DecidableEq F] (f : α → F) :
    IsFaithfulness (α := α) (identViolFeature f · .lhs .rhs) := fun s ↦ by
  show Segment.identViol f ((identity s).toward .lhs .rhs) ((identity s).toward .rhs .lhs) = 0
  rw [toward_identity (by decide), toward_identity (by decide)]
  exact identViol_indexed_self f s

@[simp] theorem maxViol_identity (s : List α) : (identity s).maxViol .lhs .rhs = 0 :=
  isFaithfulness_maxViol s

@[simp] theorem depViol_identity (s : List α) : (identity s).depViol .lhs .rhs = 0 :=
  isFaithfulness_depViol s

/-- The anti-faithfulness constraint of a faithfulness constraint is not faithfulness, since the
fully faithful candidate violates it. -/
theorem IsFaithfulness.not_antifaithful {k : Constraint (Coindexation BinaryRole α)}
    (hk : IsFaithfulness k) : ¬ IsFaithfulness k.antifaithful := fun h ↦ by
  simpa [Constraint.antifaithful_eq_zero_iff, hk []] using h []

/-! ### One indexing of every string -/

/-- The candidate whose strings bear the same indices toward every role. -/
def ofStrings (f : Role → List (Segment α)) : Coindexation Role α where
  form r := (f r).map fun x ↦ (x.seg, fun _ ↦ x.indices)

@[simp] theorem toward_ofStrings (f : Role → List (Segment α)) (r₁ r₂ : Role) :
    (ofStrings f).toward r₁ r₂ = f r₁ := by
  simp [toward, ofStrings, Function.comp_def]

@[simp] theorem string_ofStrings (f : Role → List (Segment α)) (r : Role) :
    (ofStrings f).string r = (f r).map (·.seg) := by
  simp [string, ofStrings]

/-- The input, the base and the reduplicant, coindexed position by position. -/
def reduplication (input base reduplicant : List α) : Coindexation ReduplicationRole α :=
  ofStrings fun
    | .input => indexed input
    | .base => indexed base
    | .reduplicant => indexed reduplicant

end Coindexation

end OptimalityTheory.Correspondence
