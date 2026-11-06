/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott, Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Deployment

/-!
# Universal inferences of trivalent quantifiers

A trivalent quantifier has a universal entailment over a domain when it is true of a predicate only
if the predicate is defined throughout the domain, a universal anti-entailment when it is false only
then, and a universal presupposition when it has both. Under Peters-Kleene deployment these turn on
[single steps](##Trivalent.universalEntailment_deployQuantifier_iff): a quantifier has a universal
entailment when it never holds of both a set and the set with one more element, and a universal
presupposition when it [flips at every
step](##Trivalent.universalPresupposition_deployQuantifier_iff).

## Implementation notes

The definitions take any `(α → SignType) → SignType`, so they apply to the other trivalent
quantifiers of `Linglib.Logic.Trivalent.Pointwise` as well as to deployed ones. The domain lets one
notion cover quantifiers, over the whole universe, and determiners, over the restrictor.

## References

* [george-2014]
-/

@[expose] public section

namespace Trivalent

open SignType

variable {α : Type*}

/-- `T` has a universal entailment over `R` when it is true of a predicate only if the predicate is
defined throughout `R`. -/
def UniversalEntailment (R : Set α) (T : (α → SignType) → SignType) : Prop :=
  ∀ A, T A = 1 → ∀ a ∈ R, A a ≠ 0

/-- `T` has a universal anti-entailment over `R` when it is false of a predicate only if the
predicate is defined throughout `R`. -/
def UniversalAntiEntailment (R : Set α) (T : (α → SignType) → SignType) : Prop :=
  ∀ A, T A = -1 → ∀ a ∈ R, A a ≠ 0

/-- `T` has a universal presupposition over `R` when it has a universal entailment and a universal
anti-entailment there. -/
def UniversalPresupposition (R : Set α) (T : (α → SignType) → SignType) : Prop :=
  UniversalEntailment R T ∧ UniversalAntiEntailment R T

variable {Q : Set α → Prop} {R : Set α}

/-- Over a domain `R`, a property of sets that holds of the repairs of a trivalent predicate only
when the predicate is defined throughout `R` is one that never holds of both a set and the set with
one more element of `R`. -/
theorem forall_repairs_imp_iff (P : Set α → Prop) (R : Set α) :
    (∀ A : α → SignType, (∀ X ∈ repairs A, P X) → ∀ a ∈ R, A a ≠ 0) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (P B ∧ P (insert a B)) := by
  constructor
  · rintro h B a haR haB ⟨hB, hC⟩
    refine h (ofIcc B (insert a B)) (fun X hX ↦ ?_) a haR (by simp [ofIcc, haB])
    rw [repairs_ofIcc (Set.subset_insert a B)] at hX
    rcases (Set.covBy_insert haB).eq_or_eq hX.1 hX.2 with rfl | rfl <;> assumption
  · intro h A hA a haR ha0
    rw [repairs_eq_Icc] at hA
    exact h (posSupport A) a haR (by simp [ha0]) ⟨hA _ ⟨le_rfl, posSupport_subset A⟩,
      hA _ ⟨Set.subset_insert _ _, Set.insert_subset (by simp [ha0]) (posSupport_subset A)⟩⟩

/-! ### Deployed quantifiers: single steps -/

/-- A deployed quantifier has a universal entailment over `R` when it never holds of both a set and
the set with one more element of `R`. -/
theorem universalEntailment_deployQuantifier_iff :
    UniversalEntailment R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (Q B ∧ Q (insert a B)) := by
  rw [← forall_repairs_imp_iff]
  simp [UniversalEntailment, deployQuantifier_eq_supervaluationOn, supervaluationOn_eq_one_iff]

/-- A deployed quantifier has a universal anti-entailment over `R` when it never fails of both a set
and the set with one more element of `R`. -/
theorem universalAntiEntailment_deployQuantifier_iff :
    UniversalAntiEntailment R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (¬ Q B ∧ ¬ Q (insert a B)) := by
  rw [← forall_repairs_imp_iff (fun B ↦ ¬ Q B)]
  simp [UniversalAntiEntailment, deployQuantifier_eq_supervaluationOn,
    supervaluationOn_eq_neg_one_iff, repairs_nonempty]

/-- A deployed quantifier has a universal anti-entailment exactly when its complement has a
universal entailment. -/
theorem universalAntiEntailment_deployQuantifier_iff_compl :
    UniversalAntiEntailment R (deployQuantifier Q) ↔
      UniversalEntailment R (deployQuantifier Qᶜ) := by
  rw [universalAntiEntailment_deployQuantifier_iff, universalEntailment_deployQuantifier_iff]; rfl

/-- A deployed quantifier has a universal presupposition over `R` when it flips at every step in
`R`. -/
theorem universalPresupposition_deployQuantifier_iff :
    UniversalPresupposition R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → (Q (insert a B) ↔ ¬ Q B) := by
  rw [UniversalPresupposition, universalEntailment_deployQuantifier_iff,
    universalAntiEntailment_deployQuantifier_iff]
  refine ⟨fun h B a haR ha ↦ ?_, fun h ↦ ⟨fun B a haR ha ↦ ?_, fun B a haR ha ↦ ?_⟩⟩
  · have := h.1 B a haR ha; have := h.2 B a haR ha; tauto
  · have := h B a haR ha; tauto
  · have := h B a haR ha; tauto

end Trivalent
