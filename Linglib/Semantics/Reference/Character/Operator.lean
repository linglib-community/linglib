/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Extensional
public import Linglib.Semantics.Reference.Character
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.GroupTheory.Submonoid.Centralizer
public import Mathlib.Logic.Function.Conjugate

/-!
# Operators on characters

This file defines three classes of operators on characters and the shifts of the context. An
operator on characters is a function from characters to characters. With a fixed type of values,
the operators form a monoid under composition.

An operator `O` is intensional if, for every context `c`, the content of `O χ` at `c` depends only
on the content of `χ` at `c`. It is one-dimensional if moreover the dependence is the same at
every context, so that one function from contents to contents gives `O` at all of them. A monster
is an operator that is not intensional. The term *intensional* is Kaplan's, who also calls these
the operators on content, and whose thesis is that every operator of English is intensional. The
term *one-dimensional* is Stalnaker's, for the operators that take each row of a matrix of
contexts and indices to a row.

Let `τ` be a family of transformations of the context, one for each index. The shift of a
character `χ` by `τ` has, at a context `c` and an index `v`, the value of `χ` at `τ v c` and `v`.
Such families form a monoid under composition at each index.

For example, let `τ v` replace the agent of each context by Ann. The sentence *I am hungry*,
shifted by `τ`, says at every context that Ann is hungry. This shift is a monster if some context
has an agent other than Ann, there is an index, and the values include two distinct ones. An
operator that applies the same function to the content at every context is one-dimensional, and
it commutes with this shift.

## Main definitions

* `Character.IsIntensional O`: for every context `c`, the content `O χ c` depends only on `χ c`.
* `Character.IsMonster O`: `O` is not intensional.
* `Character.IsOneDimensional O`: the content `O χ c` depends only on `χ c`, in the same way at
  every context `c`.
* `Character.shiftBy τ χ`: the character `fun c v ↦ χ (τ v c) v`.
* `Character.shiftByHom`: `shiftBy` as a monoid homomorphism from the opposite of the monoid of
  families.
* `Character.shift σ`: the shift by the family that is `σ` at every index.
* `Character.intensional C V α`, `Character.oneDimensional C V α`: the submonoids of intensional
  and of one-dimensional operators on characters with values in `α`.

## Main results

* `Character.isIntensional_iff_exists`: `O` is intensional if and only if `O χ c = o c (χ c)` for
  some function `o` and all `χ` and `c`.
* `Character.isOneDimensional_iff_exists`: if there is a context, `O` is one-dimensional if and
  only if `O χ c = o (χ c)` for some function `o` and all `χ` and `c`.
* `Character.IsOneDimensional.isIntensional`: a one-dimensional operator is intensional.
* `Character.shiftBy_mul`: the shift by `τ₁ * τ₂` is the shift by `τ₁` followed by the shift by
  `τ₂`.
* `Character.isIntensional_shiftBy_iff`: if the values include two distinct ones, the shift by `τ`
  is intensional if and only if `τ = 1`.
* `Character.isOneDimensional_iff_forall_semiconj_shift`: an operator is one-dimensional if and
  only if it commutes with the shift by every transformation of the context.
* `Character.centralizer_range_shift`: the centralizer of the constant shifts is the submonoid of
  one-dimensional operators.

## Implementation notes

An intensional operator on characters is an extensional operator on functions of the context, in
the sense of `Logic/Modal/Extensional.lean`, and the definition is stated with that predicate.

A one-dimensional operator is defined by a condition on pairs of contexts and not by the
existence of a function from contents to contents. The two agree when there is a context. With
the condition on pairs, the characterization by shifts needs no context to exist.

The shift by a product of two families is the shift by the first followed by the shift by the
second, so shifting reverses products, and the homomorphism is from the opposite monoid.

A monster is defined as the negation of an intensional operator, so that the lemmas are stated
for the positive property.

## References

* [kaplan-1989]
* [stalnaker-1978]
* [anand-nevins-2004]
-/

@[expose] public section

namespace Character

variable {C V α β γ : Type*}

/-! ### Intensional operators -/

section Intensional

variable {O : Character C V α → Character C V β}

/-- An operator `O` on characters is **intensional** if, for every context `c`, the content of
`O χ` at `c` depends only on the content of `χ` at `c`. Equivalently, `O` is extensional as an
operator on functions of the context. -/
def IsIntensional (O : Character C V α → Character C V β) : Prop :=
  IsExtensional (W := C) (α := V → α) (β := V → β) O

/-- An operator is intensional if and only if characters with the same content at a context are
sent to characters with the same content there. -/
theorem isIntensional_iff :
    IsIntensional O ↔ ∀ (c : C) ⦃χ₁ χ₂ : Character C V α⦄, χ₁ c = χ₂ c → O χ₁ c = O χ₂ c :=
  .rfl

/-- An operator that is given at each context by a function from contents to contents is
intensional. -/
theorem IsIntensional.of_apply {o : C → (V → α) → (V → β)} (h : ∀ χ c, O χ c = o c (χ c)) :
    IsIntensional O :=
  isIntensional_iff.2 fun c χ₁ χ₂ hχ ↦ by rw [h, h, hχ]

/-- An operator is intensional if and only if it is given at each context by a function from
contents to contents. -/
theorem isIntensional_iff_exists :
    IsIntensional O ↔ ∃ o : C → (V → α) → (V → β), ∀ χ c, O χ c = o c (χ c) :=
  ⟨fun h ↦ ⟨fun c f ↦ O (fun _ ↦ f) c, fun _ c ↦ h c rfl⟩, fun ⟨_, h⟩ ↦ .of_apply h⟩

/-- The identity operator is intensional. -/
theorem isIntensional_id : IsIntensional (id : Character C V α → Character C V α) :=
  fun _ ↦ isExtensionalAt_id

/-- A composition of intensional operators is intensional. -/
theorem IsIntensional.comp {O' : Character C V β → Character C V γ} (h' : IsIntensional O')
    (h : IsIntensional O) : IsIntensional (O' ∘ O) :=
  fun c ↦ (h' c).comp (h c)

/-- An operator on characters is a **monster** if it is not intensional ([kaplan-1989]). -/
def IsMonster (O : Character C V α → Character C V β) : Prop := ¬ IsIntensional O

@[simp] theorem not_isMonster : ¬ IsMonster O ↔ IsIntensional O := not_not

theorem IsIntensional.not_isMonster (h : IsIntensional O) : ¬ IsMonster O :=
  Character.not_isMonster.2 h

end Intensional

/-! ### One-dimensional operators -/

section OneDimensional

variable {O : Character C V α → Character C V β}

/-- An operator `O` on characters is **one-dimensional** if the content of `O χ` at a context
depends only on the content of `χ` there, in the same way at every context: whenever `χ` at `c`
and `χ'` at `c'` have the same content, so do `O χ` at `c` and `O χ'` at `c'` ([stalnaker-1978]). -/
def IsOneDimensional (O : Character C V α → Character C V β) : Prop :=
  ∀ ⦃c c' : C⦄ ⦃χ χ' : Character C V α⦄, χ c = χ' c' → O χ c = O χ' c'

/-- An operator that is given at every context by one function from contents to contents is
one-dimensional. -/
theorem IsOneDimensional.of_apply {o : (V → α) → (V → β)} (h : ∀ χ c, O χ c = o (χ c)) :
    IsOneDimensional O :=
  fun c c' χ χ' hχ ↦ (h χ c).trans ((congrArg o hχ).trans (h χ' c').symm)

/-- If there is a context, an operator is one-dimensional if and only if it is given at every
context by one function from contents to contents. -/
theorem isOneDimensional_iff_exists [Nonempty C] :
    IsOneDimensional O ↔ ∃ o : (V → α) → (V → β), ∀ χ c, O χ c = o (χ c) :=
  ⟨fun h ↦ ‹Nonempty C›.elim fun c₀ ↦
    ⟨fun p ↦ O (fun _ ↦ p) c₀, fun χ c ↦ h (c' := c₀) (χ' := fun _ ↦ χ c) rfl⟩,
    fun ⟨_, h⟩ ↦ .of_apply h⟩

/-- A one-dimensional operator is intensional. -/
theorem IsOneDimensional.isIntensional (h : IsOneDimensional O) : IsIntensional O :=
  isIntensional_iff.2 fun _ _ _ hχ ↦ h hχ

theorem IsOneDimensional.not_isMonster (h : IsOneDimensional O) : ¬ IsMonster O :=
  h.isIntensional.not_isMonster

/-- The identity operator is one-dimensional. -/
theorem isOneDimensional_id : IsOneDimensional (id : Character C V α → Character C V α) :=
  fun _ _ _ _ hχ ↦ hχ

/-- A composition of one-dimensional operators is one-dimensional. -/
theorem IsOneDimensional.comp {O' : Character C V β → Character C V γ}
    (h' : IsOneDimensional O') (h : IsOneDimensional O) : IsOneDimensional (O' ∘ O) :=
  fun _ _ _ _ hχ ↦ h' (h hχ)

end OneDimensional

/-! ### Shifts -/

section Shift

/-- The **shift** of a character `χ` by a family `τ` of transformations of the context is the
character whose value at a context `c` and an index `v` is the value of `χ` at `τ v c` and `v`. -/
def shiftBy (τ : V → Function.End C) (χ : Character C V α) : Character C V α :=
  fun c v ↦ χ (τ v c) v

@[simp] theorem shiftBy_apply (τ : V → Function.End C) (χ : Character C V α) (c : C) (v : V) :
    shiftBy τ χ c v = χ (τ v c) v := rfl

@[simp] theorem shiftBy_one (χ : Character C V α) : shiftBy (1 : V → Function.End C) χ = χ := rfl

/-- The shift by a product of two families is the shift by the first followed by the shift by the
second. -/
theorem shiftBy_mul (τ₁ τ₂ : V → Function.End C) (χ : Character C V α) :
    shiftBy (τ₁ * τ₂) χ = shiftBy τ₂ (shiftBy τ₁ χ) := rfl

/-- The **shift homomorphism** is the map `shiftBy` as a monoid homomorphism from the opposite of
the monoid of families of transformations of the context to the monoid of operators on
characters. -/
def shiftByHom : (V → Function.End C)ᵐᵒᵖ →* Function.End (Character C V α) where
  toFun τ := shiftBy τ.unop
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem shiftByHom_apply (τ : (V → Function.End C)ᵐᵒᵖ) (χ : Character C V α) :
    shiftByHom τ χ = shiftBy τ.unop χ := rfl

/-- The **constant shift** by a transformation `σ` of the context is the shift by the family that
is `σ` at every index. -/
def shift (σ : Function.End C) : Character C V α → Character C V α := shiftBy fun _ ↦ σ

@[simp] theorem shift_apply (σ : Function.End C) (χ : Character C V α) (c : C) :
    shift σ χ c = χ (σ c) := rfl

@[simp] theorem shift_one (χ : Character C V α) : shift (1 : Function.End C) χ = χ := rfl

/-- The constant shift by a product of two transformations is the shift by the first followed by
the shift by the second. -/
theorem shift_mul (σ₁ σ₂ : Function.End C) (χ : Character C V α) :
    shift (σ₁ * σ₂) χ = shift σ₂ (shift σ₁ χ) := rfl

end Shift

/-! ### Shifts that are monsters -/

section Monster

/-- If the values include two distinct ones, the shift by a family that moves some context at some
index is a monster. -/
theorem isMonster_shiftBy_of_ne [Nontrivial α] {τ : V → Function.End C} {v : V} {c : C}
    (h : τ v c ≠ c) : IsMonster (shiftBy τ : Character C V α → Character C V α) := fun hO ↦ by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have : a = Function.update (fun _ _ ↦ a) (τ v c) (fun _ ↦ b) (τ v c) v :=
    congrFun (hO c (p := fun _ _ ↦ a) (q := Function.update (fun _ _ ↦ a) (τ v c) fun _ ↦ b)
      (by rw [Function.update_of_ne h.symm])) v
  exact hab (by simpa using this)

/-- If the values include two distinct ones, the shift by a family `τ` is intensional if and only
if `τ` is the identity at every index. -/
theorem isIntensional_shiftBy_iff [Nontrivial α] {τ : V → Function.End C} :
    IsIntensional (shiftBy τ : Character C V α → Character C V α) ↔ τ = 1 := by
  refine ⟨fun h ↦ by_contra fun hτ ↦ ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Function.ne_iff.1 hτ
    obtain ⟨c, hc⟩ := Function.ne_iff.1 (show (τ v : C → C) ≠ id from hv)
    exact isMonster_shiftBy_of_ne hc h
  · rintro rfl
    exact isIntensional_id

/-- If the values include two distinct ones, the shift by a family `τ` is a monster if and only if
`τ` is not the identity at some index. -/
theorem isMonster_shiftBy_iff [Nontrivial α] {τ : V → Function.End C} :
    IsMonster (shiftBy τ : Character C V α → Character C V α) ↔ τ ≠ 1 :=
  isIntensional_shiftBy_iff.not

/-- If the contents include two distinct ones, the constant shift by `σ` is intensional if and
only if `σ` is the identity. -/
theorem isIntensional_shift_iff [Nontrivial (V → α)] {σ : Function.End C} :
    IsIntensional (shift σ : Character C V α → Character C V α) ↔ σ = 1 := by
  have := Function.nontrivial_of_nontrivial V α
  obtain ⟨f, g, h⟩ := exists_pair_ne (V → α)
  obtain ⟨v⟩ : Nonempty V := (Function.ne_iff.1 h).nonempty
  exact isIntensional_shiftBy_iff.trans ⟨fun hσ ↦ congrFun hσ v, fun hσ ↦ hσ ▸ rfl⟩

/-- If the contents include two distinct ones, the constant shift by `σ` is a monster if and only
if `σ` is not the identity. -/
theorem isMonster_shift_iff [Nontrivial (V → α)] {σ : Function.End C} :
    IsMonster (shift σ : Character C V α → Character C V α) ↔ σ ≠ 1 :=
  isIntensional_shift_iff.not

end Monster

/-! ### One-dimensional operators and shifts -/

/-- An operator is one-dimensional if and only if it commutes with the constant shift by every
transformation of the context. -/
theorem isOneDimensional_iff_forall_semiconj_shift {O : Character C V α → Character C V β} :
    IsOneDimensional O ↔ ∀ σ : Function.End C, Function.Semiconj O (shift σ) (shift σ) := by
  refine ⟨fun h σ χ ↦ funext fun c ↦ h (c' := σ c) (χ' := χ) rfl, fun h c c' χ χ' hχ ↦ ?_⟩
  have h₁ : O (fun _ ↦ χ c) c = O χ c := congrFun (h (fun _ ↦ c) χ) c
  have h₂ : O (fun _ ↦ χ' c') c = O χ' c' := congrFun (h (fun _ ↦ c') χ') c
  rw [← h₁, ← h₂, hχ]

/-! ### The monoids of operators -/

section Submonoid

variable (C V α)

/-- The **intensional operators** on characters with values in `α` form a submonoid of the monoid
of all operators on those characters. -/
def intensional : Submonoid (Function.End (Character C V α)) where
  carrier := {O | IsIntensional O}
  one_mem' := isIntensional_id
  mul_mem' h h' := h.comp h'

/-- The **one-dimensional operators** on characters with values in `α` form a submonoid of the
monoid of all operators on those characters. -/
def oneDimensional : Submonoid (Function.End (Character C V α)) where
  carrier := {O | IsOneDimensional O}
  one_mem' := isOneDimensional_id
  mul_mem' h h' := h.comp h'

variable {C V α} {O : Function.End (Character C V α)}

@[simp] theorem mem_intensional : O ∈ intensional C V α ↔ IsIntensional O := .rfl

@[simp] theorem mem_oneDimensional : O ∈ oneDimensional C V α ↔ IsOneDimensional O := .rfl

theorem oneDimensional_le_intensional : oneDimensional C V α ≤ intensional C V α :=
  fun _ h ↦ h.isIntensional

/-- The centralizer of the constant shifts is the submonoid of one-dimensional operators. -/
theorem centralizer_range_shift :
    Submonoid.centralizer (M := Function.End (Character C V α))
      (Set.range (shift (C := C) (V := V) (α := α))) = oneDimensional C V α := by
  ext O
  refine Iff.trans ⟨fun h σ χ ↦ ?_, ?_⟩ isOneDimensional_iff_forall_semiconj_shift.symm
  · exact (congrFun (h _ ⟨σ, rfl⟩) χ).symm
  · rintro h _ ⟨σ, rfl⟩
    exact funext fun χ ↦ (h σ χ).symm

end Submonoid

end Character
