/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character

/-!
# Kripke (1980): Naming and Necessity

This file formalizes the modal argument of [kripke-1980]. A designator is rigid exactly when
the de re and the de dicto reading of every predication of it coincide
(`isRigid_iff_deRe_iff_deDicto`): a name eliminates the scope ambiguity that a description
creates, and a designator that varies between two worlds is separated from its actual-world
referent by the identity predicate (`exists_deRe_not_deDicto`). A description that varies is
therefore not synonymous with a rigid name (`modal_argument`), and fixing a name's reference
by a description, Kaplan's `dthat`, does not make the two synonymous
(`Character.dthat_ne`). Necessity attaches to things: a rigid designator of `e` carries `e`'s
essential properties to every world (`IsEssential.of_isRigid`), and a strongly rigid
designator designates something that exists at every world (`IsStronglyRigid`).

## References

* [kripke-1980]
* [kaplan-1989]
-/

@[expose] public section

namespace Kripke1980

open Kaplan

variable {W E : Type*} {t name desc : W → E} {P : E → W → Prop} {w w₀ w₁ w₂ : W} {e : E}

/-- The de dicto reading: the designator is evaluated at the world of the predication. -/
def deDicto (P : E → W → Prop) (t : W → E) (w : W) : Prop := P (t w) w

/-- The de re reading: the designator is evaluated at the actual world `w₀`. -/
def deRe (P : E → W → Prop) (t : W → E) (w₀ w : W) : Prop := P (t w₀) w

theorem isRigid_iff_deRe_iff_deDicto (t : W → E) (w₀ : W) :
    IsRigid t ↔ ∀ (P : E → W → Prop) (w : W), deRe P t w₀ w ↔ deDicto P t w := by
  refine ⟨λ h P w => by rw [deRe, deDicto, h w₀ w], λ h w₁ w₂ => ?_⟩
  exact ((h (λ e _ => e = t w₀) w₁).1 rfl).trans ((h (λ e _ => e = t w₀) w₂).1 rfl).symm

theorem exists_deRe_not_deDicto (h : t w₁ ≠ t w₀) :
    ∃ P : E → W → Prop, deRe P t w₀ w₁ ∧ ¬ deDicto P t w₁ :=
  ⟨λ e _ => e = t w₀, rfl, h⟩

theorem modal_argument (h : IsRigid name) (hv : desc w₁ ≠ desc w₂) : name ≠ desc :=
  λ e => hv ((e ▸ h) w₁ w₂)

/-- An essential property of `e` holds of it at every world. -/
def IsEssential (e : E) (P : E → W → Prop) : Prop := ∀ w, P e w

theorem IsEssential.of_isRigid (hP : IsEssential e P) (ht : IsRigid t) (h : t w₀ = e) (w : W) :
    P (t w) w := by
  rw [(ht w w₀).trans h]
  exact hP w

/-- A strongly rigid designator is rigid and designates something that exists at every
world, as a numeral does and a name of a person does not. -/
def IsStronglyRigid (exists_ : E → W → Prop) (t : W → E) : Prop :=
  IsRigid t ∧ ∀ w, exists_ (t w) w

theorem isStronglyRigid_const {exists_ : E → W → Prop} (h : ∀ w, exists_ e w) :
    IsStronglyRigid exists_ (λ _ => e) :=
  ⟨isRigid_const e, h⟩

end Kripke1980
