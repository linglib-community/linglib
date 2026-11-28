/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Category.Preord
public import Mathlib.Basic.Sign.Defs

/-!
# Marked types and their domains in the monotonicity calculus

The monotonicity calculus of Icard, Moss and Tune is typed by simple types over a set of base types
in which every arrow carries a marking: `+` for monotone functions, `−` for antitone functions and
`·` for functions about which nothing is known. A marking is a sign, `+` being `1`, `−` being `-1`
and `·` being `0`. The marking `m` lies below `m'` in the information order, `m ⊑ m'`, when
`m = m'` or `m' = ·`, and the types are ordered by the least relation `≼` such that
`σ →ᵐ τ ≼ σ' →ᵐ' τ'` whenever `σ' ≼ σ`, `τ ≼ τ'` and `m ⊑ m'`.

Given a preorder for each base type, the domain of `σ →ᵐ τ` is the set of functions from the domain
of `σ` to the domain of `τ` that are monotone when `m = +` and antitone when `m = −`, ordered
pointwise. For `σ ≼ τ` there is a monotone coercion from the domain of `σ` to the domain of `τ`,
sending a function `k` in the domain of `σ →ᵐ τ` to `π ∘ k ∘ π'` for the coercions `π` and `π'`
of the codomains and the domains. The coercions are the identity along `σ ≼ σ` and compose, so the
domains form a functor from the types to the preorders.

## Main definitions

* `IcardMossTune2017.MonoBy`: a function is monotone under the marking `+`, antitone under `−`,
  and arbitrary under `·`.
* `IcardMossTune2017.Ty`: the marked types, with the subtyping order.
* `IcardMossTune2017.Ty.Dom`: the domain of a type over preorders for the base types.
* `IcardMossTune2017.Ty.castLE`: the coercion along a subtyping.
* `IcardMossTune2017.Ty.domFunctor`: the domains and coercions as a functor to preorders.

## Implementation notes

Markings are `SignType`, so that the composition of markings is the multiplication of signs. The
information order is a relation of its own, since `SignType` carries the order `-1 < 0 < 1`.

## TODO

* The terms of the calculus and their typing, the valence of a variable occurrence, and the
  theorem that a term in which a variable occurs only positively is monotone in that variable.
* The join of two types that differ only in the markings along their codomains, and the erasure
  of those markings, which the equivalence of terms is stated with.
* The proof system and its completeness.

## References

* [icard-moss-tune-2017]
-/

@[expose] public section

namespace IcardMossTune2017

/-! ### Markings -/

/-- The information order on markings: `m ⊑ m'` when `m = m'` or `m'` is `·`. -/
def MarkingLE (m m' : SignType) : Prop := m = m' ∨ m' = 0

instance : DecidableRel MarkingLE := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem MarkingLE.refl (m : SignType) : MarkingLE m m := .inl rfl

theorem MarkingLE.trans {a b c : SignType} (h₁ : MarkingLE a b) (h₂ : MarkingLE b c) :
    MarkingLE a c := by
  revert h₁ h₂; decide +revert

theorem MarkingLE.antisymm {a b : SignType} (h₁ : MarkingLE a b) (h₂ : MarkingLE b a) : a = b := by
  revert h₁ h₂; decide +revert

theorem markingLE_zero (m : SignType) : MarkingLE m 0 := .inr rfl

section MonoBy

variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {m m' : SignType}

/-- A function behaves as the marking `m` says when it is monotone for `m = +` and antitone for
`m = −`; every function behaves as `·` says. -/
def MonoBy : SignType → (α → β) → Prop
  | .zero, _ => True
  | .pos, f => Monotone f
  | .neg, f => Antitone f

@[simp] theorem monoBy_zero {f : α → β} : MonoBy 0 f := trivial

@[simp] theorem monoBy_one {f : α → β} : MonoBy 1 f ↔ Monotone f := .rfl

/-- The composition of a function that behaves as `m` with one that behaves as `m'` behaves as
their product. -/
theorem MonoBy.comp {g : β → γ} {f : α → β} (hg : MonoBy m g) (hf : MonoBy m' f) :
    MonoBy (m * m') (g ∘ f) := by
  cases m <;> cases m'
  exacts [trivial, trivial, trivial, trivial, Antitone.comp (g := g) hg hf,
    Antitone.comp_monotone (g := g) hg hf, trivial, Monotone.comp_antitone (g := g) hg hf,
    Monotone.comp (g := g) hg hf]

theorem MonoBy.mono {f : α → β} (h : MarkingLE m m') (hf : MonoBy m f) : MonoBy m' f := by
  rcases h with rfl | rfl
  exacts [hf, trivial]

theorem MonoBy.conj {k : β → γ} {g : γ → δ} {f : α → β} (hk : MonoBy m k) (hg : Monotone g)
    (hf : Monotone f) : MonoBy m (g ∘ k ∘ f) := by
  simpa using (monoBy_one.2 hg).comp (hk.comp (monoBy_one.2 hf))

/-- The marking `m` lies below `m'` in the information order exactly when every function that
behaves as `m` says behaves as `m'` says. -/
theorem markingLE_iff_forall_monoBy :
    MarkingLE m m' ↔ ∀ f : Prop → Prop, MonoBy m f → MonoBy m' f := by
  refine ⟨fun h _ ↦ .mono h, fun h ↦ ?_⟩
  have hid : ¬Antitone (id : Prop → Prop) := fun h ↦ h (show False ≤ True from False.elim) trivial
  have hnot : ¬Monotone Not := fun h ↦ h (show False ≤ True from False.elim) id trivial
  have anti : Antitone Not := fun _ _ h hn ha ↦ hn (h ha)
  cases m <;> cases m'
  exacts [.inl rfl, absurd (h id trivial) hid, absurd (h Not trivial) hnot, .inr rfl, .inl rfl,
    absurd (h Not anti) hnot, .inr rfl, absurd (h id monotone_id) hid, .inl rfl]

end MonoBy

/-! ### Marked types -/

/-- The simple types over the base types `B` with marked arrows: `arr σ m τ` is the type of the
functions from `σ` to `τ` that behave as `m` says. -/
inductive Ty (B : Type*) where
  | base : B → Ty B
  | arr : Ty B → SignType → Ty B → Ty B
  deriving DecidableEq

namespace Ty

variable {B : Type*}

/-- The subtyping order, contravariant in domains and covariant in codomains and markings. -/
protected inductive LE : Ty B → Ty B → Prop
  | base (b : B) : Ty.LE (.base b) (.base b)
  | arr {σ σ' τ τ' : Ty B} {m m' : SignType} :
      Ty.LE σ' σ → Ty.LE τ τ' → MarkingLE m m' →
      Ty.LE (.arr σ m τ) (.arr σ' m' τ')

instance : LE (Ty B) := ⟨Ty.LE⟩

protected theorem LE.refl : ∀ σ : Ty B, Ty.LE σ σ
  | .base b => .base b
  | .arr σ m τ => .arr (Ty.LE.refl σ) (Ty.LE.refl τ) (MarkingLE.refl m)

protected theorem LE.trans : ∀ {σ τ μ : Ty B}, Ty.LE σ τ → Ty.LE τ μ → Ty.LE σ μ
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
  ⟨fun h ↦ by cases h; rfl, fun h ↦ h ▸ .base b⟩

@[simp] theorem not_base_le_arr {b : B} {σ τ : Ty B} {m : SignType} :
    ¬ (Ty.base b : Ty B) ≤ .arr σ m τ := fun h ↦ by cases h

@[simp] theorem not_arr_le_base {b : B} {σ τ : Ty B} {m : SignType} :
    ¬ (Ty.arr σ m τ : Ty B) ≤ .base b := fun h ↦ by cases h

@[simp] theorem arr_le_arr {σ σ' τ τ' : Ty B} {m m' : SignType} :
    (Ty.arr σ m τ : Ty B) ≤ .arr σ' m' τ' ↔ σ' ≤ σ ∧ τ ≤ τ' ∧ MarkingLE m m' :=
  ⟨fun h ↦ by cases h; exact ⟨‹_›, ‹_›, ‹_›⟩, fun ⟨h₁, h₂, hm⟩ ↦ .arr h₁ h₂ hm⟩

/-- Whether `σ` lies below, and whether it lies above, each type. -/
def decidableLEAux [DecidableEq B] :
    ∀ σ : Ty B, (∀ τ, Decidable (σ ≤ τ)) × (∀ τ, Decidable (τ ≤ σ))
  | .base _ =>
      (fun
        | .base _ => decidable_of_iff _ base_le_base.symm
        | .arr .. => .isFalse not_base_le_arr,
       fun
        | .base _ => decidable_of_iff _ base_le_base.symm
        | .arr .. => .isFalse not_arr_le_base)
  | .arr σ _ τ =>
      (fun
        | .base _ => .isFalse not_arr_le_base
        | .arr σ' _ τ' =>
            have := (decidableLEAux σ).2 σ'
            have := (decidableLEAux τ).1 τ'
            decidable_of_iff _ arr_le_arr.symm,
       fun
        | .base _ => .isFalse not_base_le_arr
        | .arr σ' _ τ' =>
            have := (decidableLEAux σ).1 σ'
            have := (decidableLEAux τ).2 τ'
            decidable_of_iff _ arr_le_arr.symm)

instance [DecidableEq B] : DecidableLE (Ty B) := fun σ τ ↦ (decidableLEAux σ).1 τ

end Ty

/-! ### Domains -/

open CategoryTheory

namespace Ty

universe u

variable {B : Type*}

/-- The domain of a type over the preorders `Db` of the base types: the domain of `arr σ m τ` is
the functions from the domain of `σ` to the domain of `τ` that behave as `m` says, ordered
pointwise. -/
def Dom (Db : B → Preord.{u}) : Ty B → Preord.{u}
  | .base b => Db b
  | .arr σ m τ => .of {f : Dom Db σ → Dom Db τ // MonoBy m f}

variable {Db : B → Preord.{u}} {σ₁ σ₂ τ₁ τ₂ : Ty B} {m₁ m₂ : SignType}

/-- The coercion along a subtyping: the identity on a base type, and on an arrow type the map
sending `k` to `π ∘ k ∘ π'` for the coercions `π` of the codomains and `π'` of the domains. -/
def castLE : ∀ {σ τ : Ty B}, σ ≤ τ → (Dom Db σ →o Dom Db τ)
  | .base _, .base _, h => match base_le_base.mp h with | rfl => OrderHom.id
  | .base _, .arr .., h => absurd h not_base_le_arr
  | .arr .., .base _, h => absurd h not_arr_le_base
  | .arr σ₁ m₁ τ₁, .arr σ₂ m₂ τ₂, h =>
      have h' := arr_le_arr.mp h
      show {f : Dom Db σ₁ → Dom Db τ₁ // MonoBy m₁ f} →o
        {f : Dom Db σ₂ → Dom Db τ₂ // MonoBy m₂ f} from
      { toFun k := ⟨castLE h'.2.1 ∘ k.val ∘ castLE h'.1,
          (k.property.conj (castLE h'.2.1).monotone (castLE h'.1).monotone).mono h'.2.2⟩
        monotone' _ _ hk _ := (castLE h'.2.1).monotone (hk _) }
  termination_by σ τ _ => sizeOf σ + sizeOf τ

@[simp] theorem castLE_base {b : B} (h : (Ty.base b : Ty B) ≤ .base b) :
    castLE (Db := Db) h = OrderHom.id := by
  rw [castLE]

@[simp] theorem castLE_arr_apply (h : (Ty.arr σ₁ m₁ τ₁ : Ty B) ≤ .arr σ₂ m₂ τ₂)
    (k : {f : Dom Db σ₁ → Dom Db τ₁ // MonoBy m₁ f}) (a : Dom Db σ₂) :
    (castLE (Db := Db) h k : {f : Dom Db σ₂ → Dom Db τ₂ // MonoBy m₂ f}).val a =
      castLE (arr_le_arr.mp h).2.1 (k.val (castLE (arr_le_arr.mp h).1 a)) := by
  rw [castLE]; rfl

@[simp] theorem castLE_refl : ∀ σ : Ty B, castLE (le_refl σ) = (OrderHom.id : Dom Db σ →o _)
  | .base _ => castLE_base _
  | .arr σ m τ =>
      OrderHom.ext _ _ <| funext fun k ↦ Subtype.ext <| funext fun a ↦ by
        simp [castLE_refl σ, castLE_refl τ]

/-- The coercions compose: coercing along `σ ≤ τ` and then along `τ ≤ μ` is coercing along
`σ ≤ μ`. -/
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
      refine Subtype.ext <| funext fun a ↦ ?_
      simp [castLE_castLE l₂.1 l₁.1, castLE_castLE l₁.2.1 l₂.2.1]
  termination_by σ τ μ _ _ _ => sizeOf σ + sizeOf τ + sizeOf μ

/-- The domains of the types and the coercions between them, as a functor from the subtyping order
to the preorders. -/
def domFunctor (Db : B → Preord.{u}) : Ty B ⥤ Preord.{u} where
  obj := Dom Db
  map f := Preord.ofHom (castLE f.le)
  map_id σ := by ext a; simp
  map_comp f g := by ext a; exact (castLE_castLE f.le g.le a).symm

/-! ### Functions on one base type -/

section Examples

private abbrev r : Ty Unit := .base ()

example : Ty.arr (.arr r 0 r) 1 r ≤ .arr (.arr r (-1) r) 0 r := by decide

example : ¬Ty.arr r 0 r ≤ .arr r 1 r := by decide

/-- The coercion from the monotone functions to all functions keeps the function. -/
example {Db : Unit → Preord.{u}} (h : Ty.arr r 1 r ≤ .arr r 0 r)
    (k : {f : Dom Db r → Dom Db r // MonoBy 1 f}) (a : Dom Db r) :
    (castLE (Db := Db) h k : {f : Dom Db r → Dom Db r // MonoBy 0 f}).val a = k.val a := by
  simp

end Examples

end Ty

end IcardMossTune2017
