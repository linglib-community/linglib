/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Logic.Function.Basic` for the idempotent form,
`Mathlib.Data.Set.Finite.Range` and `Mathlib.SetTheory.Cardinal.Finite` for the range lemmas.
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Restrict
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Functions that factor through another

Lemmas on mathlib's `Function.FactorsThrough`. A function that factors through `f` takes no more
values than `f`, and factoring through an idempotent function is invariance under it.

Factoring through on a subset `s` needs no predicate of its own. It is
`(s.domRestrict g).FactorsThrough (s.domRestrict f)`, and `Function.factorsThrough_iff` then says
that `g` agrees on `s` with a function of `f`.

## Main results

* `Function.FactorsThrough.finite_range`, `Function.FactorsThrough.card_range_le`: a function that
  factors through another takes no more values, so its range is finite when the other's is.
* `Function.factorsThrough_iff_of_idempotent`: a function factors through an idempotent `f`
  exactly when it is invariant under `f`.
* `Set.Subsingleton.factorsThrough_domRestrict`, `Set.InjOn.factorsThrough_domRestrict`: on a
  subsingleton, or where `f` is injective, every function factors through `f`.
* `Set.factorsThrough_domRestrict_iff_of_subsingleton`: where `f` is constant, a function factors
  through `f` exactly when it is constant too.
-/

@[expose] public section

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*} {g : α → γ} {f : α → β}

theorem factorsThrough_iff_of_idempotent {f : α → α} (hf : ∀ a, f (f a) = f a) :
    FactorsThrough g f ↔ ∀ a, g a = g (f a) :=
  ⟨fun h a ↦ h (hf a).symm, fun h a b hab ↦ (h a).trans ((congrArg g hab).trans (h b).symm)⟩

instance [Fintype α] [DecidableEq β] [DecidableEq γ] : Decidable (FactorsThrough g f) := by
  unfold FactorsThrough; infer_instance

theorem FactorsThrough.card_range_le [Finite α] (h : FactorsThrough g f) :
    Nat.card (Set.range g) ≤ Nat.card (Set.range f) := by
  refine Nat.card_le_card_of_surjective (fun b ↦ ⟨g b.2.choose, b.2.choose, rfl⟩) ?_
  rintro ⟨_, a, rfl⟩
  exact ⟨⟨f a, a, rfl⟩, Subtype.ext (h (⟨a, rfl⟩ : ∃ a', f a' = f a).choose_spec)⟩

theorem FactorsThrough.finite_range (h : FactorsThrough g f) (hf : (Set.range f).Finite) :
    (Set.range g).Finite := by
  have := hf.to_subtype
  refine (Set.finite_range fun b : Set.range f ↦ g b.2.choose).subset ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨f a, a, rfl⟩, h (⟨a, rfl⟩ : ∃ a', f a' = f a).choose_spec⟩

end Function

namespace Set

variable {α β γ : Type*} {s : Set α} {f : α → β} {g : α → γ}

theorem Subsingleton.factorsThrough_domRestrict (hs : s.Subsingleton) :
    (s.domRestrict g).FactorsThrough (s.domRestrict f) :=
  fun a b _ ↦ congrArg (s.domRestrict g) (Subtype.ext (hs a.2 b.2))

theorem InjOn.factorsThrough_domRestrict (hf : s.InjOn f) :
    (s.domRestrict g).FactorsThrough (s.domRestrict f) :=
  fun a b hab ↦ congrArg (s.domRestrict g) (Subtype.ext (hf a.2 b.2 hab))

theorem factorsThrough_domRestrict_iff_of_subsingleton (hf : (f '' s).Subsingleton) :
    (s.domRestrict g).FactorsThrough (s.domRestrict f) ↔ (g '' s).Subsingleton := by
  refine ⟨fun h ↦ ?_, fun h a b _ ↦ h (mem_image_of_mem g a.2) (mem_image_of_mem g b.2)⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact @h ⟨a, ha⟩ ⟨b, hb⟩ (hf (mem_image_of_mem f ha) (mem_image_of_mem f hb))

end Set
