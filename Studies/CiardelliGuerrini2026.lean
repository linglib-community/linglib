module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Logic.Modal.Basic
public import Linglib.Data.Examples.CiardelliGuerrini2026

/-!
# Ciardelli and Guerrini (2026): Against wide scope free choice

This file formalizes the reductionist thesis of Ciardelli and Guerrini (2026): the free-choice
reading of *you may A or you may B* arises from the narrow-scope LF ◇(A ∨ B), the reading of
the wide-scope ◇A ∨ ◇B being the ignorance one (Fusco 2019). Possibility distributes over
disjunction, so the two LFs coincide in truth conditions there, and the ambiguity shows where
they differ: *you must A or you must B* has a reading as one disjunctive obligation □(A ∨ B),
strictly weaker than □A ∨ □B, and *you may A and you may B* one as a conjunctive permission
◇(A ∧ B), strictly stronger than ◇A ∧ ◇B. The narrow LF arises by modal concord
(Zeijlstra 2007): a modal auxiliary carries an uninterpretable modal feature, and one silent
interpretable operator above the coordination checks both auxiliaries' features when they fall
in one concord class. Non-auxiliary modals carry interpretable features and cannot be checked,
which is why *it's ok for John to sing or it's ok for John to dance* has no free choice
(Meyer and Sauerland 2017), while *may* and *can* share their feature and mix
(Alonso-Ovalle 2006). Across negation concord needs dual forces (Grosz 2010, Anand and
Brasoveanu 2010), negation flipping the force of the feature it scopes over, so *I need not cook
and I need not clean* conveys a permission to do neither and not an obligation. The
modal features come from the English auxiliary Fragment, and the paper's coordination and
concord examples are rows.

## Implementation notes

The argument against across-the-board movement from *everyone sang or everyone danced*
(Simons 2005) has no movement substrate here, and the cases the paper leaves open, *it is
possible that A or it is possible that B* and conjoined *be allowed*, are not rows.

## References

* [ciardelli-guerrini-2026]
* [zeijlstra-2007]
* [meyer-sauerland-2017]
* [fusco-2019]
* [simons-2005]
* [grosz-2010]
* [anand-brasoveanu-2010]
* [alonso-ovalle-2006]
-/

@[expose] public section

namespace CiardelliGuerrini2026

open Modality ModalLogic English.Auxiliaries
open SetRel

/-! ### Scope and truth conditions (§2) -/

section Scope

variable {World : Type*} (R : SetRel World World) (A B : Set World)

/-- Universal accessibility on two worlds, the countermodels' frame. -/
abbrev universalAccess : SetRel Bool Bool := .univ

/-- May-or-may, (2): possibility distributes over disjunction, so this is the one cell of the
paradigm where the scope ambiguity is invisible to truth conditions. -/
theorem poss_union_eq : R.preimage (A ∪ B) = R.preimage A ∪ R.preimage B := preimage_union ..

theorem exists_not_poss_union_subset_inter :
    ∃ A B : Set Bool,
      ¬ universalAccess.preimage A ∪ universalAccess.preimage B ⊆
        universalAccess.preimage A ∩ universalAccess.preimage B :=
  ⟨Set.univ, ∅, fun h ↦ by simpa using (@h true (by simp)).2⟩

/-- Must-or-must, (5): the narrow-scope disjunctive obligation follows from the wide-scope
disjunction of obligations. -/
theorem nec_union_subset_nec_union : R.core A ∪ R.core B ⊆ R.core (A ∪ B) := core_union_subset

theorem exists_not_nec_union_subset :
    ∃ A B : Set Bool,
      ¬ universalAccess.core (A ∪ B) ⊆ universalAccess.core A ∪ universalAccess.core B :=
  ⟨{true}, {false}, fun h ↦ by
    simpa [Bool.forall_bool] using @h true (by simp)⟩

/-- May-and-may, (7): the narrow-scope conjunctive permission entails the wide-scope
conjunction of permissions. -/
theorem poss_inter_subset_poss_inter : R.preimage (A ∩ B) ⊆ R.preimage A ∩ R.preimage B :=
  preimage_inter_subset R

/-- Joint permissibility does not follow from two permissions, which makes the conjunctive reading
of (9b) absurd. -/
theorem exists_not_poss_inter_subset :
    ∃ A B : Set Bool,
      ¬ universalAccess.preimage A ∩ universalAccess.preimage B ⊆
        universalAccess.preimage (A ∩ B) :=
  ⟨{true}, {false}, fun h ↦ by simpa using @h true (by simp)⟩

end Scope

/-! ### Modal features ([zeijlstra-2007]) -/

/-- A modal feature is interpretable, contributing a modal operator, or uninterpretable,
checked by an interpretable feature that c-commands it. -/
inductive ModalInterpretability
  | interpretable
  | uninterpretable
  deriving DecidableEq

/-- A modal feature pairs a force with its interpretability: the four features `[i∀-MOD]`,
`[u∀-MOD]`, `[i∃-MOD]` and `[u∃-MOD]`. -/
structure ModalFeature where
  force : ModalForce
  interp : ModalInterpretability
  deriving DecidableEq

/-- An interpretable feature checks an uninterpretable one of the same concord class; one
interpretable feature may check several. -/
def ModalFeature.Checks (checker checked : ModalFeature) : Prop :=
  checker.interp = .interpretable ∧ checked.interp = .uninterpretable ∧
    (checker.force.IsUniversal ↔ checked.force.IsUniversal)

instance : DecidableRel ModalFeature.Checks :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ↔ _)))

/-- The feature of a negated constituent: negation flips the force of the feature it scopes
over, so concord across negation checks the negated feature (§4.2, footnote 7, after
[grosz-2010] and [anand-brasoveanu-2010]). -/
def ModalFeature.negated (f : ModalFeature) : ModalFeature := ⟨f.force.dual, f.interp⟩

theorem ModalFeature.checks_negated_iff {checker checked : ModalFeature}
    (hi : checker.interp = .interpretable) (hu : checked.interp = .uninterpretable) :
    checker.Checks checked.negated ↔ ¬ (checker.force.IsUniversal ↔ checked.force.IsUniversal) := by
  simp only [ModalFeature.Checks, ModalFeature.negated, hi, hu, true_and]
  cases checker.force <;> cases checked.force <;> decide

/-- The features of a modal auxiliary of the Fragment: the forces of its meanings, uninterpretable,
Zeijlstra's generalization that auxiliaries contribute no operator. -/
def auxiliaryFeatures (a : ModalAuxiliary) : Finset ModalFeature :=
  a.forces.image (⟨·, .uninterpretable⟩)

/-! ### Modal concord (§3) -/

/-- Two modal features stand in concord when both are uninterpretable and fall in one concord
class: one silent interpretable operator above the coordination then checks both, (15), so the
modal outscopes the coordinator. -/
def Concord (f₁ f₂ : ModalFeature) : Prop :=
  f₁.interp = .uninterpretable ∧ f₂.interp = .uninterpretable ∧
    (f₁.force.IsUniversal ↔ f₂.force.IsUniversal)

instance : DecidableRel Concord := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ↔ _)))

theorem exists_checks_of_concord {f₁ f₂ : ModalFeature} (h : Concord f₁ f₂) :
    ∃ op : ModalFeature, op.interp = .interpretable ∧ op.Checks f₁ ∧ op.Checks f₂ :=
  ⟨⟨f₁.force, .interpretable⟩, rfl, ⟨rfl, h.1, Iff.rfl⟩, ⟨rfl, h.2.1, h.2.2⟩⟩

theorem concord_of_checks {op f₁ f₂ : ModalFeature} (h₁ : op.Checks f₁) (h₂ : op.Checks f₂) :
    Concord f₁ f₂ :=
  ⟨h₁.2.1, h₂.2.1, h₁.2.2.symm.trans h₂.2.2⟩

/-- An interpreted feature is never checked, so non-auxiliary modals such as *be allowed* admit
no narrow-scope LF, (19) and (20). -/
theorem not_checks_of_interpretable (op : ModalFeature) {f : ModalFeature}
    (h : f.interp = .interpretable) : ¬ op.Checks f := by
  intro hc
  have := hc.2.1
  simp [h] at this

/-- In the fragment *may* concords with *may* and *can* (footnote 4, [alonso-ovalle-2006]), *must*
with *must*, and *may* not with *must*. -/
theorem fragment_concord :
    (∀ f ∈ auxiliaryFeatures may, ∀ g ∈ auxiliaryFeatures may, Concord f g) ∧
      (∀ f ∈ auxiliaryFeatures must, ∀ g ∈ auxiliaryFeatures must, Concord f g) ∧
      (∀ f ∈ auxiliaryFeatures may, ∀ g ∈ auxiliaryFeatures can, Concord f g) ∧
      (∀ f ∈ auxiliaryFeatures may, ∀ g ∈ auxiliaryFeatures must, ¬ Concord f g) := by
  decide

/-! ### Concord across negation (§4.2) -/

/-- The negated feature of *need* in (28) is checked by a silent possibility operator (29a), not a
necessity one (29c). -/
theorem need_not :
    ∀ f ∈ auxiliaryFeatures need,
      ModalFeature.Checks ⟨.possibility, .interpretable⟩ f.negated ∧
        ¬ ModalFeature.Checks ⟨.necessity, .interpretable⟩ f.negated := by
  decide

/-! ### The rows -/

/-- The modal features of a modal named in the rows: the auxiliaries' from the Fragment, and the
interpretable feature of the non-auxiliary modals, (20). -/
def featuresOf : String → Finset ModalFeature
  | "may" => auxiliaryFeatures may
  | "can" => auxiliaryFeatures can
  | "must" => auxiliaryFeatures must
  | "need" => auxiliaryFeatures need
  | "allow" | "it's ok" | "be allowed" | "be permitted" => {⟨.possibility, .interpretable⟩}
  | "demand" | "be required" => {⟨.necessity, .interpretable⟩}
  | _ => ∅

theorem coordination_rows :
    ∀ e ∈ Examples.all, ∀ m₁ ∈ e.feature? "modal1", ∀ m₂ ∈ e.feature? "modal2",
      ∀ f₁ ∈ featuresOf m₁, ∀ f₂ ∈ featuresOf m₂,
        (e.feature? "narrowReading" ≠ none ↔ Concord f₁ f₂) := by
  decide

theorem narrow_reading_available :
    ∀ e ∈ Examples.all, ∀ n ∈ e.feature? "narrowReading",
      ∃ r ∈ e.readings, r.1 = n ∧ r.2 = .acceptable := by
  decide

theorem concord_rows :
    ∀ e ∈ Examples.all, ∀ c ∈ e.feature? "checker", ∀ k ∈ e.feature? "checked",
      ∀ op ∈ featuresOf c, ∀ f ∈ featuresOf k,
        ((∃ r ∈ e.readings, r.1 = "modal concord" ∧ r.2 = .acceptable) ↔
          op.Checks (if e.feature? "negated" = some "true" then f.negated else f)) := by
  decide

end CiardelliGuerrini2026
