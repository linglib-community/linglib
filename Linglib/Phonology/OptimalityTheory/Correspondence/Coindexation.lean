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

/-! ### Faithfulness and markedness -/

/-- `identity s` is the fully faithful candidate: a string and itself, coindexed position by
position, the segments of each string bearing no index toward their own. -/
def identity (s : List α) : Coindexation BinaryRole α where
  form r := s.zipIdx.map fun x ↦ (x.1, fun r' ↦ if r' = r then [] else [x.2])

theorem toward_identity {s : List α} {r₁ r₂ : BinaryRole} (h : r₁ ≠ r₂) :
    (identity s).toward r₁ r₂ = indexed s := by
  simp [toward, identity, indexed, Segment.ofIndex, h.symm]

theorem toward_identity_self (s : List α) (r : BinaryRole) :
    (identity s).toward r r = s.map fun a ↦ ⟨a, []⟩ := by
  rw [toward, identity, List.map_map]
  conv_rhs => rw [← List.zipIdx_map_fst 0 s, List.map_map]
  exact List.map_congr_left fun x _ ↦ by simp

/-- A constraint over binary candidates is *faithfulness* when the fully faithful candidate
`identity s` satisfies it. -/
def IsFaithfulness (k : Constraint (Coindexation BinaryRole α)) : Prop :=
  ∀ s : List α, k (identity s) = 0

/-- A constraint is *markedness* for the role `out` when it depends only on the string of
`out`. -/
def IsMarkedness (out : Role) (k : Constraint (Coindexation Role α)) : Prop :=
  k.FactorsThrough (·.string out)

end Coindexation

end OptimalityTheory.Correspondence
