module

public import Mathlib.Logic.Function.Basic
public import Linglib.Logic.Modal.Defs

/-!
# Extensional operators

An operator `O` on intensions `W → α` is *extensional at* `w` when its value at `w` depends on
its argument only through the argument's extension at `w`, i.e. `O · w` factors through
evaluation at `w`. Equivalently, `O` cannot tell an argument whose index it binds from the same
argument with the index fixed at `w`, which is why a situation pronoun bound under an extensional
operator reads as if it were free. The pointwise connectives are extensional, and extensionality
is closed under them and under composition; the Kripke box `ModalLogic.Box R` is extensional at
`w` only when `w` reaches no index but itself.

## Main definitions

* `IsExtensionalAt O w`, `IsExtensional O`: local truth-functionality of an operator.

## Main results

* `isExtensionalAt_iff_forall_diag`: extensionality as the failure to distinguish a bound index
  from a fixed one.
* `isExtensionalAt_box_iff`: when the box is extensional.
* `IsExtensionalAt.and`, `IsExtensionalAt.or`, `IsExtensionalAt.not`,
  `IsExtensionalAt.comp`: closure of extensional operators.
-/

@[expose] public section

namespace ModalLogic

variable {W α β : Type*}

/-- `O` is extensional at `w` when its value at `w` depends on the argument intension only
through the argument's extension at `w`, that is, when `O · w` factors through evaluation at
`w`. -/
def IsExtensionalAt (O : (W → α) → W → β) (w : W) : Prop :=
  ∀ p q : W → α, p w = q w → O p w = O q w

/-- `O` is extensional at every index. -/
def IsExtensional (O : (W → α) → W → β) : Prop :=
  ∀ w, IsExtensionalAt O w

theorem isExtensionalAt_iff_factorsThrough (O : (W → α) → W → β) (w : W) :
    IsExtensionalAt O w ↔ Function.FactorsThrough (O · w) (· w) :=
  ⟨fun h _ _ hpq => h _ _ hpq, fun h _ _ hpq => h hpq⟩

theorem not_isExtensionalAt_iff_exists_witness {O : (W → α) → W → β} {w : W} :
    ¬ IsExtensionalAt O w ↔ ∃ p q, p w = q w ∧ O p w ≠ O q w := by
  simp only [IsExtensionalAt, not_forall, exists_prop]

/-- An operator is extensional at `w` exactly when it cannot tell an argument whose index it
binds, `fun v ↦ g v v`, from the same argument with the index fixed at `w`, `g w`. -/
theorem isExtensionalAt_iff_forall_diag {O : (W → α) → W → β} {w : W} :
    IsExtensionalAt O w ↔ ∀ g : W → W → α, O (fun v ↦ g v v) w = O (g w) w := by
  classical
  refine ⟨fun h g ↦ h _ _ rfl, fun h p q hpq ↦ ?_⟩
  have h' := h fun u v ↦ if u = w then q v else p v
  have e₁ : (fun v ↦ if v = w then q v else p v) = p := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [hpq]
    · simp [hv]
  have e₂ : (fun v ↦ if w = w then q v else p v) = q := by simp
  rwa [e₁, e₂] at h'

open SetRel in
/-- The box along `R` is extensional at `w` exactly when `w` reaches no index but itself. -/
theorem isExtensionalAt_box_iff {R : SetRel W W} {w : W} :
    IsExtensionalAt (Box R) w ↔ ∀ v, w ~[R] v → v = w := by
  refine ⟨fun h v hv ↦ ?_, fun h p q hpq ↦ propext ⟨fun hp v hv ↦ ?_, fun hq v hv ↦ ?_⟩⟩
  · have := h (fun _ ↦ True) (· = w) (eq_true rfl).symm
    exact (this ▸ fun _ _ ↦ trivial : Box R (· = w) w) v hv
  · obtain rfl := h v hv
    exact hpq ▸ hp v hv
  · obtain rfl := h v hv
    exact hpq ▸ hq v hv

namespace IsExtensionalAt

variable {w : W}

theorem eval : IsExtensionalAt (fun (p : W → α) w' => p w') w :=
  fun _ _ hpq => hpq

theorem const (P : W → Prop) : IsExtensionalAt (fun (_ : W → α) w' => P w') w :=
  fun _ _ _ => rfl

/-- Pointwise negation is extensional, since negation is not an intensional operator. -/
theorem neg : IsExtensionalAt (fun p (w' : W) => ¬ p w') w :=
  fun _ _ hpq => congrArg Not hpq

theorem and {O₁ O₂ : (W → α) → W → Prop} (h₁ : IsExtensionalAt O₁ w)
    (h₂ : IsExtensionalAt O₂ w) : IsExtensionalAt (fun p w' => O₁ p w' ∧ O₂ p w') w :=
  fun p q hpq => congrArg₂ And (h₁ p q hpq) (h₂ p q hpq)

theorem or {O₁ O₂ : (W → α) → W → Prop} (h₁ : IsExtensionalAt O₁ w)
    (h₂ : IsExtensionalAt O₂ w) : IsExtensionalAt (fun p w' => O₁ p w' ∨ O₂ p w') w :=
  fun p q hpq => congrArg₂ Or (h₁ p q hpq) (h₂ p q hpq)

theorem not {O : (W → α) → W → Prop} (h : IsExtensionalAt O w) :
    IsExtensionalAt (fun p w' => ¬ O p w') w :=
  fun p q hpq => congrArg Not (h p q hpq)

/-- Extensional operators compose, so scope-inertness lifts through a stack of them. -/
theorem comp {O₁ : (W → α) → W → β} {O₂ : (W → β) → W → Prop}
    (h₂ : IsExtensionalAt O₂ w) (h₁ : IsExtensionalAt O₁ w) :
    IsExtensionalAt (fun p w' => O₂ (fun s => O₁ p s) w') w :=
  fun p q hpq => h₂ _ _ (h₁ p q hpq)

end IsExtensionalAt

end ModalLogic
