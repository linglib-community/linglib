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
is an operator that is not intensional.

Let `τ` be a family of transformations of the context, one for each index. The shift of a
character `χ` by `τ` has, at a context `c` and an index `v`, the value of `χ` at `τ v c` and `v`.
Such families form a monoid under composition at each index.

For example, let `τ v` replace the agent of each context by Ann. The sentence *I am hungry*,
shifted by `τ`, says at every context that Ann is hungry. This shift is a monster if some context
has an agent other than Ann and the values include two distinct ones. An operator that applies
the same function to the content at every context is one-dimensional, and it commutes with this
shift.

## Main definitions

* `Character.IsIntensional O`: for every context `c`, the content `O χ c` depends only on `χ c`.
* `Character.IsMonster O`: `O` is not intensional.
* `Character.IsOneDimensional O`: `O χ c = o (χ c)` for some function `o` and all `χ` and `c`.
* `Character.shiftBy τ χ`: the character `fun c v ↦ χ (τ v c) v`.
* `Character.shiftByHom`: `shiftBy` as a monoid homomorphism from the opposite of the monoid of
  families.
* `Character.shift σ`: the shift by the family that is `σ` at every index.
* `Character.intensional C V α`, `Character.oneDimensional C V α`: the submonoids of intensional
  and of one-dimensional operators on characters with values in `α`.

## Main results

* `Character.isIntensional_iff_exists`: `O` is intensional if and only if `O χ c = o c (χ c)` for
  some function `o` and all `χ` and `c`.
* `Character.IsOneDimensional.isIntensional`: a one-dimensional operator is intensional.
* `Character.shiftBy_mul`: the shift by `τ₁ * τ₂` is the shift by `τ₁` followed by the shift by
  `τ₂`.
* `Character.isMonster_shiftBy_iff`: if the values include two distinct ones, the shift by `τ` is
  a monster if and only if `τ ≠ 1`.
* `Character.isOneDimensional_iff_semiconj_shift`: an operator is one-dimensional if and only if
  it commutes with the shift by every transformation of the context.
* `Character.oneDimensional_eq_centralizer`: the one-dimensional operators are the centralizer of
  the constant shifts.

## Implementation notes

The term *intensional* is Kaplan's, who also calls these the operators on content. An intensional
operator may act differently at different contexts, as *now* and *actually* do. Kaplan's thesis
is that every operator of English is intensional. The term *one-dimensional* is Stalnaker's, for
the operators that take each row of a matrix of contexts and indices to a row.

An intensional operator on characters is an extensional operator on functions of the context, in
the sense of `Logic/Modal/Extensional.lean`, and the definition is stated with that predicate.
Stalnaker draws the same parallel one level up: the one-dimensional operators stand to the
operators on characters as the extensional operators stand to the operators on contents.

A shift whose family overwrites coordinates of the context by those of the index is a shifty
operator in the sense of Anand and Nevins. These are defined in `Context/Overwrite.lean`.

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
  fun c χ₁ χ₂ hχ ↦ by rw [h, h, hχ]

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

theorem not_isMonster : ¬ IsMonster O ↔ IsIntensional O := not_not

end Intensional

/-! ### One-dimensional operators -/

section OneDimensional

variable {O : Character C V α → Character C V β}

/-- An operator `O` on characters is **one-dimensional** if there is a function `o` from contents
to contents such that the content of `O χ` at every context `c` is `o (χ c)`
([stalnaker-1978]). -/
def IsOneDimensional (O : Character C V α → Character C V β) : Prop :=
  ∃ o : (V → α) → (V → β), ∀ χ c, O χ c = o (χ c)

/-- A one-dimensional operator is intensional. -/
theorem IsOneDimensional.isIntensional (h : IsOneDimensional O) : IsIntensional O :=
  h.elim fun o ho ↦ .of_apply (o := fun _ ↦ o) ho

theorem IsOneDimensional.not_isMonster (h : IsOneDimensional O) : ¬ IsMonster O :=
  Character.not_isMonster.2 h.isIntensional

/-- The identity operator is one-dimensional. -/
theorem isOneDimensional_id : IsOneDimensional (id : Character C V α → Character C V α) :=
  ⟨id, fun _ _ ↦ rfl⟩

/-- A composition of one-dimensional operators is one-dimensional. -/
theorem IsOneDimensional.comp {O' : Character C V β → Character C V γ}
    (h' : IsOneDimensional O') (h : IsOneDimensional O) : IsOneDimensional (O' ∘ O) :=
  let ⟨o', ho'⟩ := h'
  let ⟨o, ho⟩ := h
  ⟨o' ∘ o, fun χ c ↦ by rw [Function.comp_apply, ho', ho, Function.comp_apply]⟩

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

/-- The map `shiftBy` is a monoid homomorphism from the opposite of the monoid of families of
transformations of the context to the monoid of operators on characters. -/
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
    shift σ χ c = χ (σ • c) := rfl

@[simp] theorem shift_one (χ : Character C V α) : shift (1 : Function.End C) χ = χ := rfl

/-- The constant shift by a product of two transformations is the shift by the first followed by
the shift by the second. -/
theorem shift_mul (σ₁ σ₂ : Function.End C) (χ : Character C V α) :
    shift (σ₁ * σ₂) χ = shift σ₂ (shift σ₁ χ) := rfl

/-- A transformation of the context is not the identity if and only if it moves some context. -/
theorem _root_.Function.End.ne_one_iff_exists_smul_ne (σ : Function.End C) :
    σ ≠ 1 ↔ ∃ c : C, σ • c ≠ c :=
  show (σ : C → C) ≠ id ↔ _ from Function.ne_iff

end Shift

/-! ### Shifts that are monsters -/

section Monster

/-- If the values include two distinct ones, the shift by a family that moves some context at some
index is a monster. -/
theorem isMonster_shiftBy_of_ne [Nontrivial α] {τ : V → Function.End C} {v : V} {c : C}
    (h : τ v c ≠ c) : IsMonster (shiftBy τ : Character C V α → Character C V α) := fun hO ↦ by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have := hO c (p := fun _ _ ↦ a) (q := Function.update (fun _ _ ↦ a) (τ v c) fun _ ↦ b)
    (by rw [Function.update_of_ne h.symm])
  exact hab (by simpa using congrFun this v)

/-- If the values include two distinct ones, the shift by a family `τ` is a monster if and only if
`τ` is not the identity. -/
theorem isMonster_shiftBy_iff [Nontrivial α] (τ : V → Function.End C) :
    IsMonster (shiftBy τ : Character C V α → Character C V α) ↔ τ ≠ 1 := by
  refine ⟨fun h hτ ↦ h (hτ ▸ isIntensional_id), fun h ↦ ?_⟩
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  obtain ⟨c, hc⟩ := (Function.End.ne_one_iff_exists_smul_ne _).1 hv
  exact isMonster_shiftBy_of_ne hc

/-- If the contents include two distinct ones, the constant shift by `σ` is a monster if and only
if `σ` is not the identity. -/
theorem isMonster_shift_iff [Nontrivial (V → α)] (σ : Function.End C) :
    IsMonster (shift σ : Character C V α → Character C V α) ↔ σ ≠ 1 := by
  have := Function.nontrivial_of_nontrivial V α
  obtain ⟨f, g, h⟩ := exists_pair_ne (V → α)
  obtain ⟨v⟩ : Nonempty V := (Function.ne_iff.1 h).nonempty
  exact (isMonster_shiftBy_iff _).trans
    ⟨fun h hσ ↦ h (hσ ▸ rfl), fun h hσ ↦ h (congrFun hσ v)⟩

end Monster

/-! ### One-dimensional operators and shifts -/

/-- An operator is one-dimensional if and only if it commutes with the constant shift by every
transformation of the context. -/
theorem isOneDimensional_iff_semiconj_shift [Nonempty C]
    {O : Character C V α → Character C V β} :
    IsOneDimensional O ↔ ∀ σ : Function.End C, Function.Semiconj O (shift σ) (shift σ) := by
  refine ⟨fun ⟨o, ho⟩ σ χ ↦ funext fun c ↦ by simp [ho], fun h ↦ ?_⟩
  obtain ⟨c₀⟩ := ‹Nonempty C›
  exact ⟨fun p ↦ O (fun _ ↦ p) c₀, fun χ c ↦ (congrFun (h (fun _ ↦ c) χ) c₀).symm⟩

/-! ### The monoids of operators -/

section Submonoid

variable (C V α)

/-- The intensional operators on characters with values in `α` form a submonoid of the monoid of
all operators on those characters. -/
def intensional : Submonoid (Function.End (Character C V α)) where
  carrier := {O | IsIntensional O}
  one_mem' := isIntensional_id
  mul_mem' h h' := h.comp h'

/-- The one-dimensional operators on characters with values in `α` form a submonoid of the monoid
of all operators on those characters. -/
def oneDimensional : Submonoid (Function.End (Character C V α)) where
  carrier := {O | IsOneDimensional O}
  one_mem' := isOneDimensional_id
  mul_mem' h h' := h.comp h'

variable {C V α} {O : Function.End (Character C V α)}

@[simp] theorem mem_intensional : O ∈ intensional C V α ↔ IsIntensional O := .rfl

@[simp] theorem mem_oneDimensional : O ∈ oneDimensional C V α ↔ IsOneDimensional O := .rfl

theorem oneDimensional_le_intensional : oneDimensional C V α ≤ intensional C V α :=
  fun _ h ↦ h.isIntensional

/-- The one-dimensional operators are the centralizer of the constant shifts. -/
theorem oneDimensional_eq_centralizer [Nonempty C] :
    oneDimensional C V α =
      Submonoid.centralizer (M := Function.End (Character C V α))
        (Set.range (shift (C := C) (V := V) (α := α))) := by
  ext O
  refine isOneDimensional_iff_semiconj_shift.trans ⟨?_, fun h σ χ ↦ ?_⟩
  · rintro h _ ⟨σ, rfl⟩
    exact funext fun χ ↦ (h σ χ).symm
  · exact (congrFun (h _ ⟨σ, rfl⟩) χ).symm

end Submonoid

end Character
