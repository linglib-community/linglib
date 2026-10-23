module

public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Semantics.Quantification.Basic

/-!
# Possessive quantifiers

A possessive determiner such as *most students'* denotes a generalized quantifier built from a
possessor quantifier `Q₁` with restriction `C`, a quantifier `Q₂` over the possessed objects and a
possession relation `R`. This file defines it, together with its variant for a possessor noun
phrase, and proves its conservativity and scope monotonicity.

## Main definitions

* `Possession.Poss`: `Poss Q₁ C Q₂ R A B ↔ Q₁ (C ∩ dom A R) {x | Q₂ (π A R x) B}`.
* `Possession.PossNP`: `PossNP Q Q₂ R A B ↔ Q (dom A R ∩ {x | Q₂ (π A R x) B})`.

## Main statements

* `Quantifier.GQ.Conservative.poss`: `Poss Q₁ C Q₂ R` is conservative if `Q₂` is (7.29).
* `Quantifier.GQ.ScopeMonotone.poss` and its variants: `Poss` is scope monotone in the product of
  the directions of `Q₁` and `Q₂`.
* `Possession.poss_eq_possNP_restrict`: for symmetric `Q₁`, `Poss Q₁ C = PossNP (Q₁ C)`
  (Fact 1).
* `Possession.possNP_individual_the`: `PossNP` at an individual with the definite as `Q₂` is the
  definite over the relationalized noun.
* `Possession.poss_not_quantityInvariant`: `Poss` is not invariant under permutations
  (p. 256).

## Implementation notes

The restriction of the possessors to `dom A R` is the narrowing of Peters and Westerståhl. The
quantifier `Q₂` of a bare possessive such as *John's bikes* is a parameter.

## References

* [peters-westerstahl-2006]
* [peters-westerstahl-2013]
* [barker-1995]
* [coppock-beaver-2015]
-/

@[expose] public section

namespace Possession

open Quantifier Quantifier.GQ Quantifier.NP

variable {α : Type*}

/-! ### Possessive operators -/

/-- The possessive quantifier of a possessor quantifier `Q₁` with restriction `C`: *[Q₁ C]'s A
are B* holds iff `Q₁` relates the `C`s that possess some `A` to the `x` with `Q₂ (π A R x) B`
([peters-westerstahl-2006], (7.30)). -/
def Poss (Q₁ : GQ α) (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B ↦ Q₁ (fun x ↦ C x ∧ dom A R x) (fun x ↦ Q₂ (π A R x) B)

/-- The possessive quantifier of a possessor noun phrase `Q`: *[Q]'s A are B* holds iff `Q`
holds of the `x` that possess some `A` and satisfy `Q₂ (π A R x) B` ([peters-westerstahl-2006],
(7.45)). -/
def PossNP (Q : NP α) (Q₂ : GQ α) (R : α → α → Prop) : GQ α :=
  fun A B ↦ Q (fun a ↦ dom A R a ∧ Q₂ (π A R a) B)

/-! ### Conservativity -/

theorem _root_.Quantifier.GQ.Conservative.poss {Q₂ : GQ α} (h₂ : Conservative Q₂) (Q₁ : GQ α)
    (C : α → Prop) (R : α → α → Prop) : Conservative (Poss Q₁ C Q₂ R) := fun _ _ ↦
  iff_of_eq (congrArg (Q₁ _) (funext fun _ ↦ propext
    (Conservative.congr_scope h₂ fun _ hy ↦ (and_iff_right hy.1).symm)))

theorem _root_.Quantifier.GQ.Conservative.possNP {Q₂ : GQ α} (h₂ : Conservative Q₂) (Q : NP α)
    (R : α → α → Prop) : Conservative (PossNP Q Q₂ R) := fun _ _ ↦
  iff_of_eq (congrArg Q (funext fun _ ↦ propext (and_congr_right fun _ ↦
    Conservative.congr_scope h₂ fun _ hy ↦ (and_iff_right hy.1).symm)))

/-! ### Scope monotonicity

`Poss Q₁ C Q₂ R` is upward monotone in its scope when `Q₁` and `Q₂` are monotone in the same
direction, and downward monotone otherwise (Proposition 5, §7.13). -/

section Monotone

variable {Q₁ Q₂ : GQ α} (C : α → Prop) (R : α → α → Prop)

theorem _root_.Quantifier.GQ.ScopeMonotone.poss (h₁ : ScopeMonotone Q₁)
    (h₂ : ScopeMonotone Q₂) : ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

theorem _root_.Quantifier.GQ.ScopeMonotone.poss_scopeAntitone (h₁ : ScopeMonotone Q₁)
    (h₂ : ScopeAntitone Q₂) : ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

theorem _root_.Quantifier.GQ.ScopeAntitone.poss (h₁ : ScopeAntitone Q₁)
    (h₂ : ScopeAntitone Q₂) : ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

theorem _root_.Quantifier.GQ.ScopeAntitone.poss_scopeMonotone (h₁ : ScopeAntitone Q₁)
    (h₂ : ScopeMonotone Q₂) : ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

end Monotone

/-! ### Narrowing -/

theorem poss_eq_possNP_restrict {Q₁ : GQ α} (hSym : Std.Symm Q₁) (hCons : Conservative Q₁)
    (C : α → Prop) (Q₂ : GQ α) (R : α → α → Prop) :
    Poss Q₁ C Q₂ R = PossNP (Q₁ C) Q₂ R :=
  funext fun _ ↦ funext fun _ ↦
    propext ((conserv_symm_iff_int Q₁ hCons).mp hSym _ _ _ _ fun _ ↦ and_assoc)

/-! ### Individual possessors -/

theorem possNP_individual_iff {Q₂ : GQ α} {R : α → α → Prop} {a : α} {A B : α → Prop} :
    PossNP (individual a) Q₂ R A B ↔ dom A R a ∧ Q₂ (π A R a) B :=
  Iff.rfl

theorem possNP_individual_existential_import {Q₂ : GQ α} {R : α → α → Prop}
    {a : α} {A B : α → Prop} (h : PossNP (individual a) Q₂ R A B) : dom A R a :=
  h.1

theorem possNP_individual_the {R : α → α → Prop} {a : α} {A B : α → Prop} :
    PossNP (individual a) the R A B ↔ the (π A R a) B :=
  ⟨And.right, fun h ↦ ⟨h.elim fun x hx ↦ ⟨x, (hx.1 x).2 rfl⟩, h⟩⟩

/-! ### Quantity invariance -/

theorem poss_not_quantityInvariant :
    ¬ QuantityInvariant
        (Poss (GQ.some (α := Bool)) (fun _ ↦ True) GQ.some
          (fun x y ↦ x = true ∧ y = true)) := by
  intro h
  have hiff := h (fun x ↦ x = true) (fun _ ↦ True) (fun x ↦ x = false)
    (fun _ ↦ True) Bool.not
    ((Function.Involutive.bijective fun b ↦ Bool.not_not b))
    (fun x ↦ by cases x <;> simp) (fun _ ↦ Iff.rfl)
  have hpos : Poss (GQ.some (α := Bool)) (fun _ ↦ True) GQ.some
      (fun x y ↦ x = true ∧ y = true) (fun x ↦ x = true) (fun _ ↦ True) :=
    ⟨true, ⟨trivial, true, rfl, rfl, rfl⟩, true, ⟨rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨x, ⟨-, b, hb, -, hb'⟩, -⟩ := hiff.mp hpos
  exact absurd (hb' ▸ hb) (by simp)

end Possession
