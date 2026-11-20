/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.FreeMonoid.FreeSemigroup

/-!
# Bracketings in a free magma

An element of the free magma `FreeMagma α` is a bracketing of a nonempty word over `α`. The
homomorphism `FreeMagma.toFreeSemigroup` forgets the bracketing and keeps the word, and
`FreeMagma.toFreeMonoid` reads that word in the free monoid. Every homomorphism from the free
magma to a semigroup factors through `toFreeSemigroup`, so it takes two bracketings of one word
to the same value: see `FreeMagma.lift_comp_toFreeSemigroup` and
`FreeMagma.apply_eq_apply_of_toFreeMonoid_eq`.

A *left comb* is a bracketing `((a * b) * c) * d` in which every product has a generator as its
right factor. Each word `a b c d` has exactly one, `FreeSemigroup.leftComb`, given by the formula
`l.foldl (· * of ·) (of a)` that defines `FreeSemigroup.lift` in a semigroup. The map `leftComb`
is a section of `toFreeSemigroup`, and `FreeMagma.leftCombEquiv` is the resulting bijection
between words and left combs.
-/

@[expose] public section

variable {α β : Type*}

namespace FreeMagma

/-! ### The word of a bracketing -/

/-- The canonical multiplicative morphism from `FreeMagma α` to `FreeMonoid α`. -/
def toFreeMonoid : FreeMagma α →ₙ* FreeMonoid α := lift FreeMonoid.of

@[simp] theorem toFreeMonoid_of (a : α) : toFreeMonoid (of a) = FreeMonoid.of a := rfl

theorem toFreeMonoid_comp_toFreeSemigroup :
    FreeSemigroup.toFreeMonoid.comp toFreeSemigroup = @toFreeMonoid α := by ext1; rfl

@[simp] theorem toFreeMonoid_toFreeSemigroup (x : FreeMagma α) :
    (toFreeSemigroup x).toFreeMonoid = toFreeMonoid x :=
  DFunLike.congr_fun toFreeMonoid_comp_toFreeSemigroup x

theorem toFreeMonoid_eq_toFreeMonoid_iff {x y : FreeMagma α} :
    toFreeMonoid x = toFreeMonoid y ↔ toFreeSemigroup x = toFreeSemigroup y := by
  simp only [← toFreeMonoid_toFreeSemigroup, FreeSemigroup.toFreeMonoid_injective.eq_iff]

theorem toFreeSemigroup_foldl_mul_of (x : FreeMagma α) (l : List α) :
    toFreeSemigroup (l.foldl (· * of ·) x) =
      ⟨(toFreeSemigroup x).head, (toFreeSemigroup x).tail ++ l⟩ := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih]

section Semigroup

variable [Semigroup β]

/-- A homomorphism from a free magma to a semigroup factors through the free semigroup. -/
theorem lift_comp_toFreeSemigroup (f : α → β) :
    (FreeSemigroup.lift f).comp toFreeSemigroup = lift f := by ext1; rfl

@[simp] theorem lift_toFreeSemigroup (f : α → β) (x : FreeMagma α) :
    FreeSemigroup.lift f (toFreeSemigroup x) = lift f x :=
  DFunLike.congr_fun (lift_comp_toFreeSemigroup f) x

theorem apply_eq_apply_of_toFreeSemigroup_eq (f : FreeMagma α →ₙ* β) {x y : FreeMagma α}
    (h : toFreeSemigroup x = toFreeSemigroup y) : f x = f y := by
  rw [← lift_comp_of' f, ← lift_toFreeSemigroup, ← lift_toFreeSemigroup, h]

/-- A homomorphism from a free magma to a semigroup takes two bracketings of the same word to the
same value. -/
theorem apply_eq_apply_of_toFreeMonoid_eq (f : FreeMagma α →ₙ* β) {x y : FreeMagma α}
    (h : toFreeMonoid x = toFreeMonoid y) : f x = f y :=
  apply_eq_apply_of_toFreeSemigroup_eq f (toFreeMonoid_eq_toFreeMonoid_iff.1 h)

end Semigroup

/-! ### Left combs -/

/-- An element of a free magma is a left comb when every product in it has a generator as its
right factor. -/
def IsLeftComb : FreeMagma α → Prop
  | of _ => True
  | mul x (of _) => IsLeftComb x
  | mul _ (mul _ _) => False

instance decidableIsLeftComb : (x : FreeMagma α) → Decidable (IsLeftComb x)
  | of _ => isTrue trivial
  | mul x (of _) => decidableIsLeftComb x
  | mul _ (mul _ _) => isFalse id

@[simp] theorem isLeftComb_of (a : α) : IsLeftComb (of a) := trivial

@[simp] theorem isLeftComb_mul_of (x : FreeMagma α) (a : α) :
    IsLeftComb (x * of a) ↔ IsLeftComb x := Iff.rfl

@[simp] theorem not_isLeftComb_mul_mul (x y z : FreeMagma α) : ¬ IsLeftComb (x * (y * z)) := id

theorem isLeftComb_mul {x y : FreeMagma α} :
    IsLeftComb (x * y) ↔ IsLeftComb x ∧ ∃ a, y = of a := by
  cases y with
  | of a => exact (isLeftComb_mul_of x a).trans (and_iff_left ⟨a, rfl⟩).symm
  | mul y z => exact iff_of_false (not_isLeftComb_mul_mul x y z) (by rintro ⟨-, a, ⟨⟩⟩)

@[simp] theorem isLeftComb_foldl_mul_of (x : FreeMagma α) (l : List α) :
    IsLeftComb (l.foldl (· * of ·) x) ↔ IsLeftComb x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp [ih]

end FreeMagma

namespace FreeSemigroup

open FreeMagma

/-- The left comb of a word, the bracketing `((a * b) * c) * d` of `a b c d`. -/
def leftComb (u : FreeSemigroup α) : FreeMagma α := u.tail.foldl (· * .of ·) (.of u.head)

theorem leftComb_mk (a : α) (l : List α) : leftComb ⟨a, l⟩ = l.foldl (· * .of ·) (.of a) := rfl

@[simp] theorem leftComb_of (a : α) : leftComb (of a) = .of a := rfl

@[simp] theorem leftComb_mul_of (u : FreeSemigroup α) (a : α) :
    leftComb (u * of a) = leftComb u * .of a := by
  simp [leftComb]

@[simp] theorem isLeftComb_leftComb (u : FreeSemigroup α) : (leftComb u).IsLeftComb :=
  (isLeftComb_foldl_mul_of _ _).2 (isLeftComb_of _)

/-- The left comb of a word is a bracketing of that word. -/
@[simp] theorem toFreeSemigroup_leftComb (u : FreeSemigroup α) :
    toFreeSemigroup (leftComb u) = u := by
  simp [leftComb, toFreeSemigroup_foldl_mul_of]

theorem leftInverse_toFreeSemigroup_leftComb :
    Function.LeftInverse toFreeSemigroup (@leftComb α) := toFreeSemigroup_leftComb

theorem leftComb_injective : Function.Injective (@leftComb α) :=
  leftInverse_toFreeSemigroup_leftComb.injective

@[simp] theorem toFreeMonoid_leftComb (u : FreeSemigroup α) :
    FreeMagma.toFreeMonoid (leftComb u) = u.toFreeMonoid := by
  rw [← toFreeMonoid_toFreeSemigroup, toFreeSemigroup_leftComb]

/-- In a semigroup, a homomorphism of the free magma evaluates the left comb of a word as the
product of the word. -/
theorem lift_leftComb [Semigroup β] (f : α → β) (u : FreeSemigroup α) :
    FreeMagma.lift f (leftComb u) = lift f u := by
  rw [← lift_toFreeSemigroup, toFreeSemigroup_leftComb]

end FreeSemigroup

namespace FreeMagma

open FreeSemigroup

theorem toFreeSemigroup_surjective : Function.Surjective (@toFreeSemigroup α) :=
  leftInverse_toFreeSemigroup_leftComb.surjective

/-- A left comb is the left comb of its word. -/
theorem IsLeftComb.leftComb_toFreeSemigroup :
    ∀ {x : FreeMagma α}, x.IsLeftComb → leftComb (toFreeSemigroup x) = x
  | of _, _ => rfl
  | mul x (of a), h => by
    rw [mul_eq, map_mul, toFreeSemigroup_of, leftComb_mul_of,
      IsLeftComb.leftComb_toFreeSemigroup (x := x) h]

theorem isLeftComb_iff_leftComb_toFreeSemigroup {x : FreeMagma α} :
    x.IsLeftComb ↔ leftComb (toFreeSemigroup x) = x :=
  ⟨IsLeftComb.leftComb_toFreeSemigroup, fun h ↦ h ▸ isLeftComb_leftComb _⟩

theorem range_leftComb : Set.range (@leftComb α) = {x | x.IsLeftComb} :=
  Set.ext fun _ ↦
    ⟨fun ⟨u, hu⟩ ↦ hu ▸ isLeftComb_leftComb u, fun h ↦ ⟨_, h.leftComb_toFreeSemigroup⟩⟩

/-- Left combs are a normal form for bracketings: each word has exactly one. -/
@[simps] def leftCombEquiv : FreeSemigroup α ≃ {x : FreeMagma α // x.IsLeftComb} where
  toFun u := ⟨leftComb u, isLeftComb_leftComb u⟩
  invFun x := toFreeSemigroup x.1
  left_inv := toFreeSemigroup_leftComb
  right_inv x := Subtype.ext x.2.leftComb_toFreeSemigroup

end FreeMagma
