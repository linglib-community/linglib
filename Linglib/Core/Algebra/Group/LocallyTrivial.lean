/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.LocallyTrivial`.
-/
module

public import Linglib.Core.Algebra.Group.Idempotent
public import Linglib.Core.Algebra.Group.IdempotentPower
public import Mathlib.Algebra.Group.Prod

/-!
# Definite and locally trivial semigroups

A semigroup is *definite* when each of its idempotents is a right zero, *reverse definite* when
each is a left zero, and *locally trivial* when every idempotent `e` satisfies `e * s * e = e` for
every `s`. In a finite semigroup each condition is equivalent to an equation on all sufficiently
long products, which is the form in which these semigroups recognize the definite, reverse definite
and generalized definite languages.

## Main definitions

* `Semigroup.IsDefinite`, `Semigroup.IsReverseDefinite`, `Semigroup.IsLocallyTrivial`: the three
  conditions.

## Main results

* `Semigroup.IsDefinite.of_injective`, `.of_surjective`, `.prod` and their mirrors: closure under
  subsemigroups, quotients and products.
* `Semigroup.IsDefinite.isRightZero_map`, `Semigroup.IsReverseDefinite.isLeftZero_map`,
  `Semigroup.IsLocallyTrivial.map_mul_map_eq`: in a finite semigroup satisfying the condition,
  every product of at least `|S|` elements is a right zero, a left zero, respectively absorbs
  anything placed between two copies of it.
* `Semigroup.IsDefinite.of_isRightZero_map` and its two mirrors: the converse, for any bound.

## Implementation notes

Pin calls definite semigroups *righty trivial* and reverse definite ones *lefty trivial*. The
long-product characterizations are Propositions XI.4.15–XI.4.17 of Pin's lecture notes.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

namespace Semigroup

variable {S T : Type*} [Semigroup S] [Semigroup T]

/-- A semigroup is *definite* when every idempotent is a right zero. -/
def IsDefinite (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → IsRightZero e

/-- A semigroup is *reverse definite* when every idempotent is a left zero. -/
def IsReverseDefinite (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → IsLeftZero e

/-- A semigroup is *locally trivial* when every idempotent `e` absorbs anything placed between two
copies of it, `e * s * e = e`. -/
def IsLocallyTrivial (S : Type*) [Semigroup S] : Prop :=
  ∀ e : S, IsIdempotentElem e → ∀ s : S, e * s * e = e

/-! ### Closure properties -/

theorem IsDefinite.of_injective {f : S →ₙ* T} (hf : Function.Injective f) (h : IsDefinite T) :
    IsDefinite S := fun e he ↦ (h (f e) (he.map f)).of_map hf

theorem IsReverseDefinite.of_injective {f : S →ₙ* T} (hf : Function.Injective f)
    (h : IsReverseDefinite T) : IsReverseDefinite S := fun e he ↦ (h (f e) (he.map f)).of_map hf

theorem IsLocallyTrivial.of_injective {f : S →ₙ* T} (hf : Function.Injective f)
    (h : IsLocallyTrivial T) : IsLocallyTrivial S := fun e he s ↦ hf <| by
  rw [map_mul, map_mul, h (f e) (he.map f) (f s)]

theorem IsDefinite.prod (hS : IsDefinite S) (hT : IsDefinite T) : IsDefinite (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

theorem IsReverseDefinite.prod (hS : IsReverseDefinite S) (hT : IsReverseDefinite T) :
    IsReverseDefinite (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

theorem IsLocallyTrivial.prod (hS : IsLocallyTrivial S) (hT : IsLocallyTrivial T) :
    IsLocallyTrivial (S × T) := by
  rintro ⟨e₁, e₂⟩ he ⟨s₁, s₂⟩
  exact Prod.ext (hS e₁ (congrArg Prod.fst he) s₁) (hT e₂ (congrArg Prod.snd he) s₂)

section Surjective

variable [Finite S]

theorem IsDefinite.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f) (h : IsDefinite S) :
    IsDefinite T := fun _ he' ↦
  have ⟨e, he, hfe⟩ := exists_isIdempotentElem_map_eq hf he'
  hfe ▸ (h e he).map_of_surjective hf

theorem IsReverseDefinite.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f)
    (h : IsReverseDefinite S) : IsReverseDefinite T := fun _ he' ↦
  have ⟨e, he, hfe⟩ := exists_isIdempotentElem_map_eq hf he'
  hfe ▸ (h e he).map_of_surjective hf

theorem IsLocallyTrivial.of_surjective {f : S →ₙ* T} (hf : Function.Surjective f)
    (h : IsLocallyTrivial S) : IsLocallyTrivial T := by
  intro e' he' t
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_map_eq hf he'
  obtain ⟨s, rfl⟩ := hf t
  rw [← map_mul, ← map_mul, h e he s]

end Surjective

/-! ### Long products

Each condition is equivalent to an equation on all sufficiently long products: `S` is definite
exactly when long products are right zeros, reverse definite when they are left zeros, and locally
trivial when they absorb any element placed between two copies. A product is the image of a word
under a homomorphism `f` out of a free semigroup. One direction holds with the bound `|S|`, by
`FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul`; the other holds for any bound once `f` is
surjective, because an idempotent is the image of arbitrarily long words. -/

section LongProducts

variable {α : Type*} {f : FreeSemigroup α →ₙ* S} {w : FreeSemigroup α} {k : ℕ}

/-- A semigroup is definite when, for some bound, every product of at least that many elements is a
right zero. -/
theorem IsDefinite.of_isRightZero_map (hf : Function.Surjective f)
    (h : ∀ w, k ≤ w.length → IsRightZero (f w)) : IsDefinite S := by
  intro e he
  obtain ⟨u, rfl⟩ := hf e
  obtain ⟨v, hv, hfv⟩ := FreeSemigroup.exists_le_length_map_eq f he k
  exact hfv ▸ h v hv

theorem IsReverseDefinite.of_isLeftZero_map (hf : Function.Surjective f)
    (h : ∀ w, k ≤ w.length → IsLeftZero (f w)) : IsReverseDefinite S := by
  intro e he
  obtain ⟨u, rfl⟩ := hf e
  obtain ⟨v, hv, hfv⟩ := FreeSemigroup.exists_le_length_map_eq f he k
  exact hfv ▸ h v hv

theorem IsLocallyTrivial.of_map_mul_map_eq (hf : Function.Surjective f)
    (h : ∀ w, k ≤ w.length → ∀ s, f w * s * f w = f w) : IsLocallyTrivial S := by
  intro e he s
  obtain ⟨u, rfl⟩ := hf e
  obtain ⟨v, hv, hfv⟩ := FreeSemigroup.exists_le_length_map_eq f he k
  rw [← hfv, h v hv]

variable [Finite S] (f)

/-- In a finite definite semigroup, a product of at least `|S|` elements is a right zero. -/
theorem IsDefinite.isRightZero_map (h : IsDefinite S) (hw : Nat.card S ≤ w.length) :
    IsRightZero (f w) := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  rw [hw, h e he x]
  exact (h e he).mul_right y

/-- In a finite reverse definite semigroup, a product of at least `|S|` elements is a left
zero. -/
theorem IsReverseDefinite.isLeftZero_map (h : IsReverseDefinite S) (hw : Nat.card S ≤ w.length) :
    IsLeftZero (f w) := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  rw [hw, mul_assoc, h e he y]
  exact (h e he).mul_left x

/-- In a finite locally trivial semigroup, a product of at least `|S|` elements absorbs anything
placed between two copies of it. -/
theorem IsLocallyTrivial.map_mul_map_eq (h : IsLocallyTrivial S) (hw : Nat.card S ≤ w.length)
    (s : S) : f w * s * f w = f w := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  rw [hw, show x * e * y * s * (x * e * y) = x * (e * (y * s * x) * e) * y by
    simp only [mul_assoc], h e he]

theorem IsLocallyTrivial.isIdempotentElem_map (h : IsLocallyTrivial S)
    (hw : Nat.card S ≤ w.length) : IsIdempotentElem (f w) := by
  obtain ⟨x, e, y, he, hw⟩ := FreeSemigroup.exists_isIdempotentElem_map_eq_mul_mul f hw
  rw [IsIdempotentElem, hw, show x * e * y * (x * e * y) = x * (e * (y * x) * e) * y by
    simp only [mul_assoc], h e he]

end LongProducts

end Semigroup
