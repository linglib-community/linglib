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

* `Quantifier.Det.Conservative.poss`: `Poss Q₁ C Q₂ R` is conservative if `Q₂` is (7.29).
* `Quantifier.Det.ScopeMonotone.poss` and its variants: `Poss` is scope monotone in the product of
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

open Quantifier Quantifier.Det

variable {α : Type*}

/-! ### Possessive operators -/

/-- The possessive quantifier of a possessor quantifier `Q₁` with restriction `C`, under which *[Q₁
C]'s A are B* holds iff `Q₁` relates the `C`s that possess some `A` to the `x` with `Q₂ (π A R x) B`
([peters-westerstahl-2006], (7.30)). -/
def Poss (Q₁ : Det α) (C : Set α) (Q₂ : Det α) (R : α → α → Prop) : Det α :=
  fun A B ↦ Q₁ (C ∩ {x | dom A R x}) {x | Q₂ (π A R x) B}

/-- The possessive quantifier of a possessor noun phrase `Q`, under which *[Q]'s A are B* holds iff
`Q` holds of the `x` that possess some `A` and satisfy `Q₂ (π A R x) B` ([peters-westerstahl-2006],
(7.45)). -/
def PossNP (Q : Quantifier α) (Q₂ : Det α) (R : α → α → Prop) : Det α :=
  fun A B ↦ Q {a | dom A R a ∧ Q₂ (π A R a) B}

/-! ### Conservativity -/

theorem _root_.Quantifier.Det.Conservative.poss {Q₂ : Det α} (h₂ : Q₂.Conservative) (Q₁ : Det α)
    (C : Set α) (R : α → α → Prop) : (Poss Q₁ C Q₂ R).Conservative := fun _ _ ↦
  iff_of_eq (congrArg (Q₁ _) (Set.ext fun _ ↦
    h₂.congr_scope fun _ hy ↦ (and_iff_right hy.1).symm))

theorem _root_.Quantifier.Det.Conservative.possNP {Q₂ : Det α} (h₂ : Q₂.Conservative)
    (Q : Quantifier α) (R : α → α → Prop) : (PossNP Q Q₂ R).Conservative := fun _ _ ↦
  iff_of_eq (congrArg Q (Set.ext fun _ ↦ and_congr_right fun _ ↦
    h₂.congr_scope fun _ hy ↦ (and_iff_right hy.1).symm))

/-! ### Scope monotonicity

`Poss Q₁ C Q₂ R` is upward monotone in its scope when `Q₁` and `Q₂` are monotone in the same
direction, and downward monotone otherwise (Proposition 5, §7.13). -/

section Monotone

variable {Q₁ Q₂ : Det α} (C : Set α) (R : α → α → Prop)

theorem _root_.Quantifier.Det.ScopeMonotone.poss (h₁ : ScopeMonotone Q₁)
    (h₂ : ScopeMonotone Q₂) : ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

theorem _root_.Quantifier.Det.ScopeMonotone.poss_scopeAntitone (h₁ : ScopeMonotone Q₁)
    (h₂ : ScopeAntitone Q₂) : ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

theorem _root_.Quantifier.Det.ScopeAntitone.poss (h₁ : ScopeAntitone Q₁)
    (h₂ : ScopeAntitone Q₂) : ScopeMonotone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

theorem _root_.Quantifier.Det.ScopeAntitone.poss_scopeMonotone (h₁ : ScopeAntitone Q₁)
    (h₂ : ScopeMonotone Q₂) : ScopeAntitone (Poss Q₁ C Q₂ R) :=
  fun _ _ _ hB ↦ h₁ _ fun _ ↦ h₂ _ hB

end Monotone

/-! ### Narrowing -/

theorem poss_eq_possNP_restrict {Q₁ : Det α} (hSym : Std.Symm Q₁) (hCons : Q₁.Conservative)
    (C : Set α) (Q₂ : Det α) (R : α → α → Prop) :
    Poss Q₁ C Q₂ R = PossNP (Q₁ C) Q₂ R :=
  funext fun _ ↦ funext fun _ ↦
    propext (hCons.symm_iff_intersective.1 hSym _ _ _ _ (Set.inter_assoc _ _ _))

/-! ### Individual possessors -/

theorem possNP_individual_iff {Q₂ : Det α} {R : α → α → Prop} {a : α} {A B : Set α} :
    PossNP (individual a) Q₂ R A B ↔ dom A R a ∧ Q₂ (π A R a) B :=
  Iff.rfl

theorem possNP_individual_existential_import {Q₂ : Det α} {R : α → α → Prop}
    {a : α} {A B : Set α} (h : PossNP (individual a) Q₂ R A B) : dom A R a :=
  h.1

theorem possNP_individual_the {R : α → α → Prop} {a : α} {A B : Set α} :
    PossNP (individual a) the R A B ↔ the (π A R a) B :=
  ⟨And.right, fun h ↦ ⟨h.elim fun x hx ↦ ⟨x, (hx.1 x).2 rfl⟩, h⟩⟩

/-! ### Quantity invariance -/

theorem poss_not_quantityInvariant :
    ¬ (Poss (Det.some (α := Bool)) Set.univ Det.some
      fun x y ↦ x = true ∧ y = true).QuantityInvariant := by
  intro h
  have hiff := h (Equiv.swap true false) {true} Set.univ
  have hpos : Poss (Det.some (α := Bool)) Set.univ Det.some
      (fun x y ↦ x = true ∧ y = true) {true} Set.univ :=
    ⟨true, ⟨trivial, true, rfl, rfl, rfl⟩, true, ⟨rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨-, ⟨-, b, hb, -, rfl⟩, -⟩ := hiff.2 hpos
  exact absurd (show Equiv.swap true false true = true from hb) (by simp)

end Possession
