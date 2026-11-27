/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Logic.Function.DependsOn

/-!
# Monsters

An operator on characters is *intensional* when it operates on content: the content it yields at
a context depends only on the content of its argument at that context. The modal and temporal
operators are intensional, and so are *now* and *actually*, whose effect on a content varies with
the context. A *monster* is an operator that is not intensional, one that operates on character.
Kaplan's thesis is that English has none.

A family `τ` of transformations of the context, one for each index, shifts a character `χ` to the
character whose value at a context `c` and an index `v` is the value of `χ` at `τ v c` and `v`.
Such families form a monoid under composition at each index, and shifting by a product is
shifting by each factor in turn. The shifty operators of `Context/Overwrite.lean` are shifts.

## Main definitions

* `Character.IsIntensional O`: for every context `c`, the content `O χ c` depends only on `χ c`.
* `Character.IsMonster O`: `O` is not intensional.
* `Character.shiftBy τ χ`: the character `fun c v ↦ χ (τ v c) v`.
* `Character.shiftByHom`: shifting as a monoid homomorphism from the opposite of the families.

## Main results

* `Character.isIntensional_iff_exists`: an operator is intensional iff it is given, at each
  context, by a function from contents to contents.
* `Character.isMonster_shiftBy_iff`: over values that can differ, shifting by `τ` is a monster iff
  `τ ≠ 1`.

## References

* [kaplan-1989]
* [schlenker-2011]
* [schlenker-2003]
* [anand-nevins-2004]
-/

@[expose] public section

namespace Character

variable {C V α β γ : Type*}

/-! ### Intensional operators -/

section Intensional

variable {O : Character C V α → Character C V β}

/-- An operator on characters is intensional, an operator on content, when the content it yields
at a context depends only on the content of its argument there. The dependence may vary with the
context, as it does for *now* and *actually*. -/
def IsIntensional (O : Character C V α → Character C V β) : Prop :=
  ∀ c, DependsOn (fun χ : Character C V α ↦ O χ c) {c}

/-- An operator given at each context by a function from contents to contents is intensional. -/
theorem IsIntensional.of_apply {o : C → (V → α) → (V → β)} (h : ∀ χ c, O χ c = o c (χ c)) :
    IsIntensional O :=
  fun c χ₁ χ₂ hχ ↦ by simp only [h, hχ c rfl]

theorem isIntensional_iff_exists :
    IsIntensional O ↔ ∃ o : C → (V → α) → (V → β), ∀ χ c, O χ c = o c (χ c) :=
  ⟨fun h ↦ ⟨fun c f ↦ O (fun _ ↦ f) c, fun χ c ↦ h c fun c' hc' ↦ by
    rw [Set.mem_singleton_iff.1 hc']⟩, fun ⟨_, h⟩ ↦ .of_apply h⟩

theorem isIntensional_id : IsIntensional (id : Character C V α → Character C V α) :=
  fun c _ _ h ↦ h c rfl

theorem IsIntensional.comp {O' : Character C V β → Character C V γ} (h' : IsIntensional O')
    (h : IsIntensional O) : IsIntensional (O' ∘ O) :=
  fun c _ _ hχ ↦ h' c fun c' hc' ↦ by
    obtain rfl : c' = c := hc'
    exact h c' hχ

/-- An operator on characters is a monster when it is not intensional: what it yields at a context
is not determined by the content of its argument there ([kaplan-1989]). -/
def IsMonster (O : Character C V α → Character C V β) : Prop := ¬ IsIntensional O

theorem not_isMonster : ¬ IsMonster O ↔ IsIntensional O := not_not

end Intensional

/-! ### Shifts -/

section Shift

/-- The character `χ` shifted by the family `τ` of transformations of the context: its value at
a context `c` and an index `v` is the value of `χ` at the context `τ v c` and the index `v`. -/
def shiftBy (τ : V → Function.End C) (χ : Character C V α) : Character C V α :=
  fun c v ↦ χ (τ v c) v

@[simp] theorem shiftBy_apply (τ : V → Function.End C) (χ : Character C V α) (c : C) (v : V) :
    shiftBy τ χ c v = χ (τ v c) v := rfl

@[simp] theorem shiftBy_one (χ : Character C V α) : shiftBy (1 : V → Function.End C) χ = χ := rfl

/-- Shifting by a product of families is shifting by the first and then by the second. -/
theorem shiftBy_mul (τ₁ τ₂ : V → Function.End C) (χ : Character C V α) :
    shiftBy (τ₁ * τ₂) χ = shiftBy τ₂ (shiftBy τ₁ χ) := rfl

/-- Shifting as a monoid homomorphism: the families of transformations of the context act on
characters by precomposition, which reverses the order of composition. -/
def shiftByHom : (V → Function.End C)ᵐᵒᵖ →* Function.End (Character C V α) where
  toFun τ := shiftBy τ.unop
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem shiftByHom_apply (τ : (V → Function.End C)ᵐᵒᵖ) (χ : Character C V α) :
    shiftByHom τ χ = shiftBy τ.unop χ := rfl

/-- A shift moves some context iff it is not the identity. -/
theorem _root_.Function.End.ne_one_iff_exists_smul_ne (σ : Function.End C) :
    σ ≠ 1 ↔ ∃ c : C, σ • c ≠ c :=
  show (σ : C → C) ≠ id ↔ _ from Function.ne_iff

/-- Over values that can differ, shifting by a family that moves some context at some index is a
monster. -/
theorem isMonster_shiftBy_of_ne [Nontrivial α] {τ : V → Function.End C} {v : V} {c : C}
    (h : τ v c ≠ c) : IsMonster (shiftBy τ : Character C V α → Character C V α) := fun hO ↦ by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hχ : ∀ c' ∈ ({c} : Set C), (fun _ _ ↦ a : Character C V α) c' =
      Function.update (fun _ _ ↦ a) (τ v c) (fun _ ↦ b) c' := fun c' hc' ↦ by
    rw [Set.mem_singleton_iff.1 hc', Function.update_of_ne h.symm]
  exact hab (by simpa using congrFun (hO c hχ) v)

/-- Over values that can differ, shifting by a family of transformations of the context is a
monster iff the family is not the identity. -/
theorem isMonster_shiftBy_iff [Nontrivial α] (τ : V → Function.End C) :
    IsMonster (shiftBy τ : Character C V α → Character C V α) ↔ τ ≠ 1 := by
  refine ⟨fun h hτ ↦ h (hτ ▸ isIntensional_id), fun h ↦ ?_⟩
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  obtain ⟨c, hc⟩ := (Function.End.ne_one_iff_exists_smul_ne _).1 hv
  exact isMonster_shiftBy_of_ne hc

/-- The operator that evaluates a character at the shifted context, the same shift at every
index. -/
def shift (σ : Function.End C) : Character C V α → Character C V α := shiftBy fun _ ↦ σ

@[simp] theorem shift_apply (σ : Function.End C) (χ : Character C V α) (c : C) :
    shift σ χ c = χ (σ • c) := rfl

/-- Over contents that can differ, a shift operator is a monster iff the shift moves some
context. -/
theorem isMonster_shift_iff [Nontrivial (V → α)] (σ : Function.End C) :
    IsMonster (shift σ : Character C V α → Character C V α) ↔ σ ≠ 1 := by
  have := Function.nontrivial_of_nontrivial V α
  obtain ⟨f, g, h⟩ := exists_pair_ne (V → α)
  obtain ⟨v⟩ : Nonempty V := (Function.ne_iff.1 h).nonempty
  exact (isMonster_shiftBy_iff _).trans
    ⟨fun h hσ ↦ h (hσ ▸ rfl), fun h hσ ↦ h (congrFun hσ v)⟩

end Shift

end Character
