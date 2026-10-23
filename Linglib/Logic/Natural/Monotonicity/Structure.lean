/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Monotonicity.Defs
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.Order.Hom.Basic

/-!
# Domains for the monotonicity calculus

This file interprets the marked types of the [icard-moss-tune-2017]
monotonicity calculus as preordered domains: base types by a given
assignment, `+`-arrows as the monotone maps (`→o`), `−`-arrows as the
antitone maps (`·ᵒᵈ →o ·`), unmarked arrows as all maps, each with the
pointwise order. Each subtyping `σ ≤ τ` is interpreted as an
order-preserving coercion, functorial in `≤`.

## Main declarations

* `Ty.Dom`: the domain interpretation of a marked type.
* `Ty.castLE`: the coercion along subtyping — the identity on base
  types, conjugation by the inner coercions on arrows.
* `Ty.castLE_rfl`, `Ty.castLE_castLE`: the functor laws
  ([icard-moss-tune-2017] Definition 3.5's coherence conditions).

## References

* [icard-moss-tune-2017] — Definitions 3.5–3.6.
-/

@[expose] public section

namespace NaturalLogic

open CategoryTheory

instance (D : Bundled Preorder) : Preorder D := D.str

namespace Ty

universe u

variable {B : Type*}

/-- Interpret each marked type as a preordered domain over the base
    assignment `Db` ([icard-moss-tune-2017] Definition 3.6): `+`-arrows
    as the monotone maps, `−`-arrows as the antitone maps, unmarked
    arrows as all maps, ordered pointwise. -/
def Dom (Db : B → Bundled.{u} Preorder) : Ty B → Bundled.{u} Preorder
  | .base b => Db b
  | .arr σ .pos τ => .of (Dom Db σ →o Dom Db τ)
  | .arr σ .neg τ => .of ((Dom Db σ)ᵒᵈ →o Dom Db τ)
  | .arr σ .zero τ => .of (Dom Db σ → Dom Db τ)

variable {Db : B → Bundled.{u} Preorder}

/-- The coercion along subtyping ([icard-moss-tune-2017]
    Definition 3.5): the identity on base types; on arrows, conjugation
    by the inner coercions, forgetting the order-behaviour where the
    marking weakens to `·`. -/
def castLE : ∀ {σ τ : Ty B}, σ ≤ τ → (Dom Db σ →o Dom Db τ)
  | .base _, .base _, h => match base_le_base.mp h with | rfl => OrderHom.id
  | .base _, .arr .., h => absurd h not_base_le_arr
  | .arr .., .base _, h => absurd h not_arr_le_base
  | .arr _ .pos _, .arr _ .neg _, h => absurd (arr_le_arr.mp h).2.2 (by decide)
  | .arr _ .neg _, .arr _ .pos _, h => absurd (arr_le_arr.mp h).2.2 (by decide)
  | .arr _ .zero _, .arr _ .pos _, h => absurd (arr_le_arr.mp h).2.2 (by decide)
  | .arr _ .zero _, .arr _ .neg _, h => absurd (arr_le_arr.mp h).2.2 (by decide)
  | .arr σ₁ .pos τ₁, .arr σ₂ .pos τ₂, h =>
      have h' := arr_le_arr.mp h
      { toFun := λ k => (castLE h'.2.1).comp (k.comp (castLE h'.1))
        monotone' := λ _ _ hk _ => (castLE h'.2.1).monotone (hk _) }
  | .arr σ₁ .neg τ₁, .arr σ₂ .neg τ₂, h =>
      have h' := arr_le_arr.mp h
      { toFun := λ k => (castLE h'.2.1).comp (k.comp (OrderHom.dual (castLE h'.1)))
        monotone' := λ _ _ hk _ => (castLE h'.2.1).monotone (hk _) }
  | .arr σ₁ .pos τ₁, .arr σ₂ .zero τ₂, h =>
      have h' := arr_le_arr.mp h
      show (Dom Db σ₁ →o Dom Db τ₁) →o (Dom Db σ₂ → Dom Db τ₂) from
      { toFun := λ k a => castLE h'.2.1 (k (castLE h'.1 a))
        monotone' := λ _ _ hk _ => (castLE h'.2.1).monotone (hk _) }
  | .arr σ₁ .neg τ₁, .arr σ₂ .zero τ₂, h =>
      have h' := arr_le_arr.mp h
      show ((Dom Db σ₁)ᵒᵈ →o Dom Db τ₁) →o (Dom Db σ₂ → Dom Db τ₂) from
      { toFun := λ k a => castLE h'.2.1 (k (OrderDual.toDual (castLE h'.1 a)))
        monotone' := λ _ _ hk _ => (castLE h'.2.1).monotone (hk _) }
  | .arr σ₁ .zero τ₁, .arr σ₂ .zero τ₂, h =>
      have h' := arr_le_arr.mp h
      show (Dom Db σ₁ → Dom Db τ₁) →o (Dom Db σ₂ → Dom Db τ₂) from
      { toFun := λ k a => castLE h'.2.1 (k (castLE h'.1 a))
        monotone' := λ _ _ hk _ => (castLE h'.2.1).monotone (hk _) }
  termination_by σ τ _ => sizeOf σ + sizeOf τ

variable {σ₁ σ₂ τ₁ τ₂ : Ty B}

/-! ### Application lemmas -/

@[simp] theorem castLE_base {b : B} (h : (Ty.base b : Ty B) ≤ .base b) :
    castLE (Db := Db) h = OrderHom.id := by
  rw [castLE]

@[simp] theorem castLE_one_one (h : (Ty.arr σ₁ 1 τ₁ : Ty B) ≤ .arr σ₂ 1 τ₂)
    (k : Dom Db σ₁ →o Dom Db τ₁) :
    castLE h k =
      (castLE (arr_le_arr.mp h).2.1).comp (k.comp (castLE (arr_le_arr.mp h).1)) := by
  rw [castLE]; rfl

@[simp] theorem castLE_neg_one_neg_one (h : (Ty.arr σ₁ (-1) τ₁ : Ty B) ≤ .arr σ₂ (-1) τ₂)
    (k : (Dom Db σ₁)ᵒᵈ →o Dom Db τ₁) :
    castLE h k =
      (castLE (arr_le_arr.mp h).2.1).comp
        (k.comp (OrderHom.dual (castLE (arr_le_arr.mp h).1))) := by
  rw [castLE]; rfl

@[simp] theorem castLE_one_zero
    (h : (Ty.arr σ₁ 1 τ₁ : Ty B) ≤ .arr σ₂ 0 τ₂)
    (k : Dom Db σ₁ →o Dom Db τ₁) (a : Dom Db σ₂) :
    (castLE h k : Dom Db σ₂ → Dom Db τ₂) a =
      castLE (arr_le_arr.mp h).2.1 (k (castLE (arr_le_arr.mp h).1 a)) := by
  rw [castLE]; rfl

@[simp] theorem castLE_neg_one_zero
    (h : (Ty.arr σ₁ (-1) τ₁ : Ty B) ≤ .arr σ₂ 0 τ₂)
    (k : (Dom Db σ₁)ᵒᵈ →o Dom Db τ₁) (a : Dom Db σ₂) :
    (castLE h k : Dom Db σ₂ → Dom Db τ₂) a =
      castLE (arr_le_arr.mp h).2.1 (k (OrderDual.toDual (castLE (arr_le_arr.mp h).1 a))) := by
  rw [castLE]; rfl

@[simp] theorem castLE_zero_zero
    (h : (Ty.arr σ₁ 0 τ₁ : Ty B) ≤ .arr σ₂ 0 τ₂)
    (k : Dom Db σ₁ → Dom Db τ₁) (a : Dom Db σ₂) :
    (castLE h k : Dom Db σ₂ → Dom Db τ₂) a =
      castLE (arr_le_arr.mp h).2.1 (k (castLE (arr_le_arr.mp h).1 a)) := by
  rw [castLE]; rfl

/-! ### Functor laws -/

/-- The coercion along `le_refl` is the identity. -/
@[simp] theorem castLE_rfl : ∀ σ : Ty B, castLE (le_refl σ) = (OrderHom.id : Dom Db σ →o _)
  | .base _ => castLE_base _
  | .arr σ m τ => by
      cases m <;> refine OrderHom.ext _ _ (funext λ k => ?_) <;>
        first
          | refine OrderHom.ext _ _ (funext λ a => ?_)
          | funext a
      all_goals simp [castLE_rfl σ, castLE_rfl τ]

/-- The coercions compose: casting along `h₁` then `h₂` is casting
    along `h₁.trans h₂`. -/
theorem castLE_castLE :
    ∀ {σ τ μ : Ty B} (h₁ : σ ≤ τ) (h₂ : τ ≤ μ) (a : Dom Db σ),
      castLE h₂ (castLE h₁ a) = castLE (h₁.trans h₂) a
  | .base _, .base _, .base _, h₁, h₂, _ => by
      obtain rfl := base_le_base.mp h₁
      obtain rfl := base_le_base.mp h₂
      simp
  | .base _, .base _, .arr .., _, h₂, _ => absurd h₂ not_base_le_arr
  | .base _, .arr .., _, h₁, _, _ => absurd h₁ not_base_le_arr
  | .arr .., .base _, _, h₁, _, _ => absurd h₁ not_arr_le_base
  | .arr .., .arr .., .base _, _, h₂, _ => absurd h₂ not_arr_le_base
  | .arr σ₁ m₁ τ₁, .arr σ₂ m₂ τ₂, .arr σ₃ m₃ τ₃, h₁, h₂, k => by
      have l₁ := arr_le_arr.mp h₁
      have l₂ := arr_le_arr.mp h₂
      cases m₁ <;> cases m₂ <;> cases m₃ <;>
        first
          | exact absurd l₁.2.2 (by decide)
          | exact absurd l₂.2.2 (by decide)
          | (first
              | refine OrderHom.ext _ _ (funext λ a => ?_)
              | funext a
             simp [castLE_castLE l₂.1 l₁.1, castLE_castLE l₁.2.1 l₂.2.1])
  termination_by σ τ μ _ _ _ => sizeOf σ + sizeOf τ + sizeOf μ

end Ty

end NaturalLogic
