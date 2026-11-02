/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Basic.Sign.Defs
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.Order.Hom.Basic

/-!
# Icard, Moss and Tune (2017): a monotonicity calculus

Icard, Moss and Tune type the monotonicity calculus by simple types over base types whose arrows
are marked monotone (`+`), antitone (`−`) or unmarked (`·`). Markings compose as signs multiply
and are compared by information, `·` lying above both `+` and `−`, and types are ordered by
subtyping, contravariantly in domains and covariantly in codomains and markings. A marked type
denotes a preordered domain, a `+`-arrow the monotone maps, a `−`-arrow the antitone maps and an
unmarked arrow all maps, and each subtyping is an order-preserving coercion,
[functorial](##IcardMossTune2017.Ty.castLE_castLE) in the subtyping order.

## TODO

* The calculus itself, its terms and their typing, and the completeness theorem the paper is
  named for, rest on these types and domains.
* The information order on markings is the dual of the flat order on `Flat Polarity`, `·` being
  `⊥`; `MarkingLE` and `markingSup` could be read off it.

## References

* [icard-moss-tune-2017]
-/

@[expose] public section

namespace IcardMossTune2017

/-! ### Markings -/

/-! A monotonicity marking ([icard-moss-tune-2017] Definition 3.1) is a sign: `1` (`+`,
monotone), `-1` (`−`, antitone) or `0` (`·`, no information), composing as signs multiply. -/

/-- The information order on markings: `+ ⊑ ·` and `− ⊑ ·`. -/
def MarkingLE (m m' : SignType) : Prop := m = m' ∨ m' = 0

instance : DecidableRel MarkingLE := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem MarkingLE.refl (m : SignType) : MarkingLE m m := .inl rfl

theorem MarkingLE.trans {a b c : SignType} (h₁ : MarkingLE a b) (h₂ : MarkingLE b c) :
    MarkingLE a c := by
  revert h₁ h₂; decide +revert

theorem MarkingLE.antisymm {a b : SignType} (h₁ : MarkingLE a b) (h₂ : MarkingLE b a) : a = b := by
  revert h₁ h₂; decide +revert

theorem markingLE_zero (m : SignType) : MarkingLE m 0 := .inr rfl

/-- The join in the information order: a marking with itself, `·` otherwise. -/
def markingSup (m m' : SignType) : SignType := if m = m' then m else 0

@[simp] theorem markingSup_self (m : SignType) : markingSup m m = m := by simp [markingSup]

theorem markingLE_markingSup_left (m m' : SignType) : MarkingLE m (markingSup m m') := by
  revert m m'; decide

/-! ### Marked types -/

/-- Simple types over base types `B`, with marked arrows
    ([icard-moss-tune-2017] Definition 3.1): `arr σ m τ` is the type of
    `m`-behaved functions from `σ` to `τ`. -/
inductive Ty (B : Type*) where
  | base : B → Ty B
  | arr : Ty B → SignType → Ty B → Ty B
  deriving DecidableEq

namespace Ty

variable {B : Type*}

/-- The subtyping order ([icard-moss-tune-2017] Definition 3.2):
    contravariant in domains, covariant in codomains and markings, so
    that every `+`- or `−`-typed function can also be considered
    `·`-typed. -/
protected inductive LE : Ty B → Ty B → Prop
  | base (b : B) : Ty.LE (.base b) (.base b)
  | arr {σ σ' τ τ' : Ty B} {m m' : SignType} :
      Ty.LE σ' σ → Ty.LE τ τ' → MarkingLE m m' →
      Ty.LE (.arr σ m τ) (.arr σ' m' τ')

instance : LE (Ty B) := ⟨Ty.LE⟩

protected theorem LE.refl : ∀ σ : Ty B, Ty.LE σ σ
  | .base b => .base b
  | .arr σ m τ => .arr (Ty.LE.refl σ) (Ty.LE.refl τ) (MarkingLE.refl m)

protected theorem LE.trans :
    ∀ {σ τ μ : Ty B}, Ty.LE σ τ → Ty.LE τ μ →
      Ty.LE σ μ
  | _, _, _, .base b, .base _ => .base b
  | _, _, _, .arr h₁ h₂ hm, .arr h₁' h₂' hm' =>
      .arr (h₁'.trans h₁) (h₂.trans h₂') (hm.trans hm')

protected theorem LE.antisymm :
    ∀ {σ τ : Ty B}, Ty.LE σ τ → Ty.LE τ σ → σ = τ
  | _, _, .base _, .base _ => rfl
  | _, _, .arr h₁ h₂ hm, .arr h₁' h₂' hm' => by
      rw [(h₁.antisymm h₁' : _ = _), h₂.antisymm h₂', hm.antisymm hm']

instance : PartialOrder (Ty B) where
  le_refl := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

@[simp] theorem base_le_base {b b' : B} : (Ty.base b : Ty B) ≤ .base b' ↔ b = b' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .base b⟩

@[simp] theorem not_base_le_arr {b : B} {σ τ : Ty B} {m : SignType} :
    ¬ (Ty.base b : Ty B) ≤ .arr σ m τ := fun h => by cases h

@[simp] theorem not_arr_le_base {b : B} {σ τ : Ty B} {m : SignType} :
    ¬ (Ty.arr σ m τ : Ty B) ≤ .base b := fun h => by cases h

@[simp] theorem arr_le_arr {σ σ' τ τ' : Ty B} {m m' : SignType} :
    (Ty.arr σ m τ : Ty B) ≤ .arr σ' m' τ' ↔ σ' ≤ σ ∧ τ ≤ τ' ∧ MarkingLE m m' :=
  ⟨fun h => by cases h; exact ⟨‹_›, ‹_›, ‹_›⟩, fun ⟨h₁, h₂, hm⟩ => .arr h₁ h₂ hm⟩

set_option warn.classDefReducibility false in
instance decidableLE [DecidableEq B] :
    ∀ σ τ : Ty B, Decidable (σ ≤ τ)
  | .base b, .base b' =>
      if h : b = b' then .isTrue (h ▸ .base b)
      else .isFalse fun hle => by cases hle; exact h rfl
  | .base _, .arr .. => .isFalse fun hle => by cases hle
  | .arr .., .base _ => .isFalse fun hle => by cases hle
  | .arr σ m τ, .arr σ' m' τ' =>
      match decidableLE σ' σ, decidableLE τ τ', (inferInstance : Decidable (MarkingLE m m')) with
      | .isTrue h₁, .isTrue h₂, .isTrue hm => .isTrue (.arr h₁ h₂ hm)
      | .isFalse h₁, _, _ => .isFalse fun hle => by cases hle; exact h₁ ‹_›
      | _, .isFalse h₂, _ => .isFalse fun hle => by cases hle; exact h₂ ‹_›
      | _, _, .isFalse hm => .isFalse fun hle => by cases hle; exact hm ‹_›
  termination_by σ τ => sizeOf σ + sizeOf τ

/-! ### Compatibility join and marking erasure -/

/-- The partial join of compatible types ([icard-moss-tune-2017]
    Definition 3.3): defined when the two types share their unmarked
    skeleton and their domains exactly, joining the markings along the
    codomain spine. -/
def sup? [DecidableEq B] : Ty B → Ty B → Option (Ty B)
  | .base b, .base b' => if b = b' then some (.base b) else none
  | .arr σ m τ, .arr σ' m' τ' =>
      if σ = σ' then (sup? τ τ').map (.arr σ (markingSup m m')) else none
  | _, _ => none

@[simp] theorem sup?_self [DecidableEq B] :
    ∀ σ : Ty B, sup? σ σ = some σ
  | .base b => by simp [sup?]
  | .arr σ m τ => by simp [sup?, sup?_self τ]

theorem le_of_mem_sup?_left [DecidableEq B] :
    ∀ {σ τ μ : Ty B}, sup? σ τ = some μ → σ ≤ μ
  | .base b, .base b', _, h => by
      rw [sup?] at h
      split at h
      · cases h; exact .base b
      · exact absurd h (by simp)
  | .arr σ m τ, .arr σ' m' τ', _, h => by
      rw [sup?] at h
      split at h
      · rcases Option.map_eq_some_iff.mp h with ⟨κ, hκ, rfl⟩
        exact .arr (Ty.LE.refl σ) (le_of_mem_sup?_left hκ) (markingLE_markingSup_left m m')
      · exact absurd h (by simp)

/-- Erase the markings along the codomain spine ([icard-moss-tune-2017]
    Definition 3.3, their `σ̂`). -/
def unmark : Ty B → Ty B
  | .base b => .base b
  | .arr σ _ τ => .arr σ 0 (unmark τ)

theorem le_unmark : ∀ σ : Ty B, σ ≤ unmark σ
  | .base b => .base b
  | .arr σ m τ => .arr (Ty.LE.refl σ) (le_unmark τ) (markingLE_zero m)

end Ty

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

end IcardMossTune2017
