/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Abel

/-!
# Rota–Baxter operators

A map `P : A → A` is a Rota–Baxter operator of weight `θ` if
`P a * P b = P (P a * b + a * P b + θ • (a * b))` for all `a b`. The projection of Laurent series
onto their polar part has weight `-1`. Over a semiring, whose addition is not invertible, the
operators of interest have weight `+1`; over a ring the two are exchanged by `P ↦ -P`.

The identity makes the ranges of `P` and of `θ • id + P` closed under multiplication. For an
idempotent operator of weight `-1` these are the two subalgebras of the splitting of `A` on which
the algebraic Birkhoff factorization of renormalization rests.

## Main definitions

* `IsRotaBaxter θ P`: `P` satisfies the Rota–Baxter identity of weight `θ`.

## Main results

* `IsRotaBaxter.mul_mem_range`, `IsRotaBaxter.mul_mem_range_smul_add`: the ranges of `P` and of
  `θ • id + P` are closed under multiplication.
* `IsRotaBaxter.neg`: if the additive map `P` has weight `θ`, then `-P` has weight `-θ`.

## Implementation notes

`IsRotaBaxter` is a predicate on functions, so it applies to additive and linear maps alike, and
a construction that never uses the identity, such as the Bogolyubov recursion
`ConnesKreimer.birkhoffMinus`, takes the bare operator. The weight `±1` forms
`isRotaBaxter_one_iff` and `isRotaBaxter_neg_one_iff` do not mention the scalars, which lets a
weight move between scalar rings.

## References

* [ebrahimi-fard-guo-kreimer-2004]
* [marcolli-tedeschi-2015]
-/

@[expose] public section

variable {k A : Type*}

section Mul

variable [Add A] [Mul A] [SMul k A]

/-- `P` is a Rota–Baxter operator of weight `θ` if
`P a * P b = P (P a * b + a * P b + θ • (a * b))` for all `a b`. -/
def IsRotaBaxter (θ : k) (P : A → A) : Prop :=
  ∀ a b, P a * P b = P (P a * b + a * P b + θ • (a * b))

variable {θ : k} {P : A → A} {a b : A}

/-- The range of a Rota–Baxter operator is closed under multiplication. -/
theorem IsRotaBaxter.mul_mem_range (h : IsRotaBaxter θ P) (ha : a ∈ Set.range P)
    (hb : b ∈ Set.range P) : a * b ∈ Set.range P := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨_, (h x y).symm⟩

end Mul

theorem isRotaBaxter_one_iff [Add A] [Mul A] [Monoid k] [MulAction k A] {P : A → A} :
    IsRotaBaxter (1 : k) P ↔ ∀ a b, P a * P b = P (P a * b + a * P b + a * b) := by
  simp only [IsRotaBaxter, one_smul]

section Semiring

variable [Monoid k] [NonUnitalNonAssocSemiring A] [DistribMulAction k A] [IsScalarTower k A A]
  [SMulCommClass k A A] {θ : k} {P : A → A} {a b : A}

/-- The range of `θ • id + P` is closed under multiplication when `P` has weight `θ`: the product
of the values at `x` and `y` is the value at `P x * y + x * P y + θ • (x * y)`. -/
theorem IsRotaBaxter.mul_mem_range_smul_add (h : IsRotaBaxter θ P)
    (ha : a ∈ Set.range fun x ↦ θ • x + P x) (hb : b ∈ Set.range fun x ↦ θ • x + P x) :
    a * b ∈ Set.range fun x ↦ θ • x + P x := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  refine ⟨P x * y + x * P y + θ • (x * y), ?_⟩
  simp only [← h x y, smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  abel

end Semiring

section Ring

variable [Ring k] [NonUnitalNonAssocRing A] [Module k A]

theorem isRotaBaxter_neg_one_iff {P : A → A} :
    IsRotaBaxter (-1 : k) P ↔ ∀ a b, P a * P b = P (P a * b + a * P b - a * b) := by
  simp only [IsRotaBaxter, neg_one_smul, sub_eq_add_neg]

/-- If `P` is an additive Rota–Baxter operator of weight `θ`, then `-P` has weight `-θ`. -/
theorem IsRotaBaxter.neg {θ : k} {P : A →+ A} (h : IsRotaBaxter θ P) :
    IsRotaBaxter (-θ) ⇑(-P) := fun a b ↦ by
  simp only [AddMonoidHom.neg_apply, neg_mul, mul_neg, neg_smul, ← neg_add, map_neg,
    neg_neg]
  exact h a b

end Ring
