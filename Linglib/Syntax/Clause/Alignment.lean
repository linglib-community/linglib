/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Obligatoriness

/-!
# Alignment

A marking of the argument roles, by case, agreement or constituent order, is a function out of
`ArgumentRole`, and its alignment is which of the three core roles S, A and P it identifies, the
kernel of the marking on the core roles, as Comrie and Dixon define it. A three-element set has five
partitions, so [a marking has one of five alignments](##Alignment.marking_cases): neutral,
accusative, with S marked like A, ergative, with S marked like P, horizontal, with A marked like P,
and tripartite. Ditransitive alignment reads P, T and R the same way. A marking may also depend on a
condition besides the role, and [hierarchy effects are its fit to an order on the
conditions](##Alignment.Fits); where coding may also be optional, [a graded marking fits when it
fits at every degree](##Alignment.fitsGraded_iff_forall_fits).

## Implementation notes

The predicates classify a marking; `Alignment.AlignmentType` is Comrie's observational
classification of languages in WALS chapters 98 to 100, which `AlignmentType.Classifies` links to
them. The two differ on purpose: no WALS chapter has a horizontal type, and `AlignmentType.active`,
the split-S systems, identifies no fixed pair of roles and so is not the alignment of a single
marking.

## References

* [aissen-2003]
* [bickel-et-al-2015]
* [comrie-1978]
* [comrie-2013]
* [dixon-1994]
* [haspelmath-2011]
-/

@[expose] public section

namespace Alignment

variable {κ : Type*} (m : ArgumentRole → κ)

/-- The marking treats S, A and P alike. -/
def IsNeutral : Prop := m .S = m .A ∧ m .S = m .P

/-- The marking treats S like A and unlike P. -/
def IsAccusative : Prop := m .S = m .A ∧ m .S ≠ m .P

/-- The marking treats S like P and unlike A. -/
def IsErgative : Prop := m .S = m .P ∧ m .S ≠ m .A

/-- The marking treats A like P and unlike S. -/
def IsHorizontal : Prop := m .A = m .P ∧ m .S ≠ m .A

/-- The marking treats S, A and P all differently. -/
def IsTripartite : Prop := m .S ≠ m .A ∧ m .S ≠ m .P ∧ m .A ≠ m .P

section
variable [DecidableEq κ]

instance : Decidable (IsNeutral m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsAccusative m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsErgative m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsHorizontal m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsTripartite m) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end

/-- Every marking has one of the five alignments, the five partitions of a three-element
set. -/
theorem marking_cases :
    IsNeutral m ∨ IsAccusative m ∨ IsErgative m ∨ IsHorizontal m ∨ IsTripartite m := by
  unfold IsNeutral IsAccusative IsErgative IsHorizontal IsTripartite
  by_cases h₁ : m .S = m .A <;> by_cases h₂ : m .S = m .P <;> by_cases h₃ : m .A = m .P <;>
    simp_all

variable {m}

theorem IsAccusative.not_isErgative (h : IsAccusative m) : ¬ IsErgative m := fun h' ↦ h.2 h'.1

theorem IsErgative.not_isAccusative (h : IsErgative m) : ¬ IsAccusative m := fun h' ↦ h.2 h'.1

/-! ### Ditransitive alignment

Ditransitive alignment compares how a marking codes P, T and R, and Haspelmath draws its triangle
like the monotransitive one, with P in the place of S, T in that of A and R in that of P. The
ditransitive alignment of a marking is the alignment of the marking read through that
correspondence, so indirective alignment, T with P and R apart, is the counterpart of accusative
alignment, and secundative alignment, R with P and T apart, the counterpart of ergative
alignment. -/

/-- The ditransitive role in the place of each monotransitive role in [haspelmath-2011]'s (6): P
for S, T for A and R for P. R and T, outside the monotransitive triangle, stay fixed. -/
def ditransitive : ArgumentRole → ArgumentRole
  | .S => .P
  | .A => .T
  | .P => .R
  | .R => .R
  | .T => .T

variable (m) in
/-- The marking treats T like P and unlike R. -/
def IsIndirective : Prop := IsAccusative (m ∘ ditransitive)

variable (m) in
/-- The marking treats R like P and unlike T. -/
def IsSecundative : Prop := IsErgative (m ∘ ditransitive)

theorem isIndirective_iff : IsIndirective m ↔ m .P = m .T ∧ m .P ≠ m .R := Iff.rfl

theorem isSecundative_iff : IsSecundative m ↔ m .P = m .R ∧ m .P ≠ m .T := Iff.rfl

instance [DecidableEq κ] : Decidable (IsIndirective m) := decidable_of_iff' _ isIndirective_iff

instance [DecidableEq κ] : Decidable (IsSecundative m) := decidable_of_iff' _ isSecundative_iff

/-! ### The observational classification -/

/-- Morphosyntactic alignment type, the classification of WALS chapters 98 to 100
([comrie-2013]): how a language groups S, A and P. -/
inductive AlignmentType where
  /-- S, A and P alike. -/
  | neutral
  /-- S with A, P apart. -/
  | accusative
  /-- S with P, A apart. -/
  | ergative
  /-- S, A and P all distinct. -/
  | tripartite
  /-- Split-S, with S marked like A for some predicates and like P for others. -/
  | active
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The alignment a type names, as a property of a marking. The split-S type names none, since
it identifies no fixed pair of roles. -/
def AlignmentType.Classifies {κ : Type*} (a : AlignmentType) (m : ArgumentRole → κ) : Prop :=
  match a with
  | .neutral => IsNeutral m
  | .accusative => IsAccusative m
  | .ergative => IsErgative m
  | .tripartite => IsTripartite m
  | .active => False

instance {κ : Type*} [DecidableEq κ] (m : ArgumentRole → κ) :
    (a : AlignmentType) → Decidable (a.Classifies m)
  | .neutral => inferInstanceAs (Decidable (IsNeutral m))
  | .accusative => inferInstanceAs (Decidable (IsAccusative m))
  | .ergative => inferInstanceAs (Decidable (IsErgative m))
  | .tripartite => inferInstanceAs (Decidable (IsTripartite m))
  | .active => inferInstanceAs (Decidable False)

/-! ### Conditioned marking

A marking may depend on a condition besides the role, such as the referential properties of the
argument or of its co-argument, or the tense of the clause. A conditioned marking
`m : ArgumentRole → C → Option κ` codes role `r` under condition `c` by the marker `m r c`, or by
none, and its alignment under `c` is that of `(m · c)`. Bickel, Witzlack-Makarevich and Zakharko
represent a case as a relation between roles and conditions, and test hierarchy effects as the
fit of a marking to an order on the conditions: A overtly coded on a lower set of them, P on an
upper set. The papers that posit a scale assert fit; the papers that test it count it. -/

section Conditioned

variable {C : Type*} (m : ArgumentRole → C → Option κ)

/-- The conditions under which role `r` is overtly coded. -/
def overt (r : ArgumentRole) : Set C := {c | m r c ≠ none}

@[simp] theorem mem_overt {r : ArgumentRole} {c : C} : c ∈ overt m r ↔ m r c ≠ none := Iff.rfl

/-- A conditioned marking fits an order on its conditions when A is overtly coded on a lower set
of them and P on an upper set. -/
def Fits [Preorder C] : Prop := IsLowerSet (overt m .A) ∧ IsUpperSet (overt m .P)

end Conditioned

/-! ### Graded overtness

Coding may be obligatory under some conditions and optional under others, as in Aissen's three
zones of overt case marking, so a graded marking gives the obligatoriness of a role's overt coding
under each condition. It fits an order on the conditions when A's overtness falls along it and P's
rises, and this is the fit of `Fits` at every degree. -/

section Graded

variable {C : Type*} [Preorder C] (μ : ArgumentRole → C → Obligatoriness)

/-- A graded marking fits an order on its conditions when A's overtness falls along it and P's
rises. -/
def FitsGraded : Prop := Antitone (μ .A) ∧ Monotone (μ .P)

/-- A graded marking fits exactly when, at every degree, the marking overt where the overtness
reaches that degree fits. -/
theorem fitsGraded_iff_forall_fits :
    FitsGraded μ ↔ ∀ k : Obligatoriness, Fits fun r c ↦ if k ≤ μ r c then some () else none := by
  have h (k : Obligatoriness) (r : ArgumentRole) :
      overt (fun r c ↦ if k ≤ μ r c then some () else none) r = {c | k ≤ μ r c} := by
    ext; simp
  simp only [FitsGraded, Fits, h, isLowerSet_setOfPred, isUpperSet_setOfPred, forall_and]
  refine and_congr ⟨fun hA k _ _ hab hb ↦ hb.trans (hA hab), fun hA _ _ hab ↦ hA _ hab le_rfl⟩
    ⟨fun hP k _ _ hab ha ↦ ha.trans (hP hab), fun hP _ _ hab ↦ hP _ hab le_rfl⟩

end Graded

end Alignment
