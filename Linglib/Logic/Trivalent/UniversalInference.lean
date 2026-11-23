/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott, Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Deployment
public import Mathlib.Order.Cover

/-!
# Universal inferences of trivalent quantifiers

A trivalent quantifier has a universal entailment over a domain when it is true of a predicate only
if the predicate is defined throughout the domain, a universal anti-entailment when it is false only
then, and a universal presupposition when it has both. Under Peters-Kleene deployment these turn on
[single steps](##Trivalent.universalEntailment_deployQuantifier_iff): a quantifier has a universal
entailment when it never holds of both a set and the set with one more element, and a universal
presupposition when it [flips at every
step](##Trivalent.universalPresupposition_deployQuantifier_iff).
[Universal projection](##Quantifier.universalProjection) over a domain has a universal
presupposition there, and for a quantifier that lives on the domain it is [deployment cut down to
the predicates defined throughout
it](##Quantifier.universalProjection_eq_transplication_deployQuantifier).

## Implementation notes

The definitions take any `(α → Trivalent) → Trivalent`, so they apply to the other trivalent
quantifiers of `Linglib.Logic.Trivalent.Quantifier` as well as to deployed ones. The domain lets one
notion cover quantifiers, over the whole universe, and determiners, over the restrictor.

## References

* [george-2014]
-/

@[expose] public section

namespace Trivalent

variable {α : Type*}

/-- `T` has a universal entailment over `R` when it is true of a predicate only if the predicate is
defined throughout `R`. -/
def UniversalEntailment (R : Set α) (T : (α → Trivalent) → Trivalent) : Prop :=
  ∀ A, T A = .true → ∀ a ∈ R, A a ≠ .undefined

/-- `T` has a universal anti-entailment over `R` when it is false of a predicate only if the
predicate is defined throughout `R`. -/
def UniversalAntiEntailment (R : Set α) (T : (α → Trivalent) → Trivalent) : Prop :=
  ∀ A, T A = .false → ∀ a ∈ R, A a ≠ .undefined

/-- `T` has a universal presupposition over `R` when it has a universal entailment and a universal
anti-entailment there. -/
def UniversalPresupposition (R : Set α) (T : (α → Trivalent) → Trivalent) : Prop :=
  UniversalEntailment R T ∧ UniversalAntiEntailment R T

variable {Q : Set α → Prop} {R : Set α}

/-- Over a domain `R`, a property of sets that holds throughout the interval of a trivalent
predicate only when the predicate is defined throughout `R` is one that never holds of both a set
and the set with one more element of `R`. -/
theorem forall_mem_interval_imp_iff (P : Set α → Prop) (R : Set α) :
    (∀ A : α → Trivalent, (∀ X ∈ Trivalent.interval A, P X) → ∀ a ∈ R, A a ≠ .undefined) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (P B ∧ P (insert a B)) := by
  constructor
  · rintro h B a haR haB ⟨hB, hC⟩
    refine h (ofIcc B (insert a B)) (fun X hX ↦ ?_) a haR (by simp [ofIcc, haB])
    rw [interval_ofIcc (Set.subset_insert a B)] at hX
    rcases (Set.covBy_insert haB).eq_or_eq hX.1 hX.2 with rfl | rfl <;> assumption
  · intro h A hA a haR ha0
    simp only [mem_interval] at hA
    exact h (posExt A) a haR (by simp [ha0]) ⟨hA _ ⟨le_rfl, posExt_subset A⟩,
      hA _ ⟨Set.subset_insert _ _, Set.insert_subset (by simp [ha0]) (posExt_subset A)⟩⟩

/-! ### Deployed quantifiers: single steps -/

/-- A deployed quantifier has a universal entailment over `R` when it never holds of both a set and
the set with one more element of `R`. -/
theorem universalEntailment_deployQuantifier_iff :
    UniversalEntailment R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (Q B ∧ Q (insert a B)) := by
  rw [← forall_mem_interval_imp_iff]
  simp [UniversalEntailment, deployQuantifier_eq_supervaluationOn, supervaluationOn_eq_true_iff]

/-- A deployed quantifier has a universal anti-entailment over `R` when it never fails of both a set
and the set with one more element of `R`. -/
theorem universalAntiEntailment_deployQuantifier_iff :
    UniversalAntiEntailment R (deployQuantifier Q) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (¬ Q B ∧ ¬ Q (insert a B)) := by
  rw [← forall_mem_interval_imp_iff (fun B ↦ ¬ Q B)]
  simp [UniversalAntiEntailment, deployQuantifier_eq_supervaluationOn,
    supervaluationOn_eq_false_iff, posExt_subset]

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

/-! ### Universal projection -/

namespace Quantifier

open Trivalent Bilattice

variable {α : Type*} {R : Set α} {Q : Quantifier α} {A : α → Trivalent}

open Classical in
/-- Universal projection of a quantifier over `R`: its classical value at the positive extension
of its argument, defined only where the argument is defined throughout `R`. -/
noncomputable def universalProjection (Q : Quantifier α) (R : Set α) (A : α → Trivalent) :
    Trivalent :=
  transplication (ofProp (∀ u ∈ R, A u ≠ .undefined)) (ofProp (Q (posExt A)))

/-- Universal projection of a determiner: the restrictor is read at its positive extension, and
the scope must be defined throughout it. -/
noncomputable def Det.universalProjection (D : Det α) (B A : α → Trivalent) : Trivalent :=
  (D (posExt B)).universalProjection (posExt B) A

@[simp]
theorem universalProjection_eq_undefined_iff :
    Q.universalProjection R A = .undefined ↔ ¬ ∀ u ∈ R, A u ≠ .undefined := by
  simp [universalProjection]

@[simp]
theorem universalProjection_eq_true_iff :
    Q.universalProjection R A = .true ↔ (∀ u ∈ R, A u ≠ .undefined) ∧ Q (posExt A) := by
  simp [universalProjection]

@[simp]
theorem universalProjection_eq_false_iff :
    Q.universalProjection R A = .false ↔ (∀ u ∈ R, A u ≠ .undefined) ∧ ¬ Q (posExt A) := by
  simp [universalProjection]

@[simp]
theorem Det.universalProjection_eq_undefined_iff {D : Det α} {B : α → Trivalent} :
    D.universalProjection B A = .undefined ↔ ¬ ∀ u, B u = .true → A u ≠ .undefined :=
  Quantifier.universalProjection_eq_undefined_iff

@[simp]
theorem Det.universalProjection_eq_true_iff {D : Det α} {B : α → Trivalent} :
    D.universalProjection B A = .true ↔
      (∀ u, B u = .true → A u ≠ .undefined) ∧ D (posExt B) (posExt A) :=
  Quantifier.universalProjection_eq_true_iff

theorem universalPresupposition_universalProjection (Q : Quantifier α) (R : Set α) :
    UniversalPresupposition R (Q.universalProjection R) :=
  ⟨fun _ h ↦ (universalProjection_eq_true_iff.1 h).1,
    fun _ h ↦ (universalProjection_eq_false_iff.1 h).1⟩

theorem isExtensionOf_universalProjection (Q : Quantifier α) (R : Set α) :
    IsExtensionOf Q (Q.universalProjection R) := fun S ↦ by
  classical
  have h : ∀ u ∈ R, ofProp (u ∈ S) ≠ .undefined := fun _ _ ↦ ofProp_ne_undefined
  have e : posExt (fun u ↦ ofProp (u ∈ S)) = S := by ext u; simp
  rw [universalProjection, ofProp_eq_true_iff.2 h, transplication_true_left, e]

open Classical in
/-- For a quantifier that lives on `R`, universal projection is deployment cut down to the
predicates defined throughout `R`. -/
theorem universalProjection_eq_transplication_deployQuantifier (hQ : Q.LivesOn R) :
    Q.universalProjection R A =
      transplication (ofProp (∀ u ∈ R, A u ≠ .undefined)) (deployQuantifier Q A) := by
  by_cases h : ∀ u ∈ R, A u ≠ .undefined
  · rw [universalProjection, deployQuantifier_of_livesOn hQ h]
  · rw [universalProjection, ofProp_eq_false_iff.2 h]
    rfl

/-- For a quantifier that lives on `R`, universal projection has the deployed value wherever it
is defined. -/
theorem universalProjection_kLE_deployQuantifier (hQ : Q.LivesOn R) :
    Q.universalProjection R A ≤ₖ deployQuantifier Q A := by
  classical
  rw [universalProjection_eq_transplication_deployQuantifier hQ, kLE_iff]
  by_cases h : ∀ u ∈ R, A u ≠ .undefined
  · exact .inr (by rw [ofProp_eq_true_iff.2 h, transplication_true_left])
  · exact .inl (by rw [ofProp_eq_false_iff.2 h]; rfl)

/-- Universal projection of a quantifier that lives on `R` is regular. -/
theorem isRegular_universalProjection (hQ : Q.LivesOn R) :
    IsRegular (Q.universalProjection R) := fun A A' hAA' ↦ by
  classical
  rw [kLE_iff]
  by_cases h : ∀ u ∈ R, A u ≠ .undefined
  · have hE : Set.EqOn A A' R := fun u hu ↦ (kLE_iff.1 (hAA' u)).resolve_left (h u hu)
    have h' : ∀ u ∈ R, A' u ≠ .undefined := fun u hu ↦ hE hu ▸ h u hu
    refine .inr ?_
    rw [universalProjection_eq_transplication_deployQuantifier hQ,
      universalProjection_eq_transplication_deployQuantifier hQ, ofProp_eq_true_iff.2 h,
      ofProp_eq_true_iff.2 h', deployQuantifier_congr_of_livesOn hQ hE]
  · exact .inl (universalProjection_eq_undefined_iff.2 h)

end Quantifier
