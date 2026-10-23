/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Data.Set.Function`.
-/
module

public import Mathlib.Data.Set.Piecewise

/-!
# Functions agreeing on a set

A function agrees with `g` off `a` exactly when it is an update of `g` at `a`, so quantifying over
the functions that agree with `g` off `a` is quantifying over the values at `a`. Quantifying over
the functions that agree with `g` on `t`, of a property that depends only on their values on `s`,
depends only on the values of `g` on `s ∩ t`.

## Main results

* `Set.eqOn_compl_singleton_iff`: `f` agrees with `g` off `a` iff `f = update g a (f a)`.
* `Set.forall_eqOn_compl_singleton_iff`, `Set.exists_eqOn_compl_singleton_iff`: quantifiers over
  the functions agreeing with `g` off `a` as quantifiers over the values at `a`.
* `Set.exists_eqOn_congr`, `Set.forall_eqOn_congr`: quantifiers over the functions agreeing with
  `g` on `t` are unchanged when `g` is changed off `s ∩ t`, for a property depending on `s` only.
-/

@[expose] public section

open Function

namespace Set

variable {α β : Type*} [DecidableEq α] {f g : α → β} {a : α}

theorem eqOn_compl_singleton_iff : EqOn f g {a}ᶜ ↔ f = update g a (f a) :=
  (eq_update_iff.trans <| and_iff_right rfl).symm

theorem forall_eqOn_compl_singleton_iff {p : (α → β) → Prop} :
    (∀ f, EqOn f g {a}ᶜ → p f) ↔ ∀ b, p (update g a b) :=
  ⟨fun h _ ↦ h _ fun _ hx ↦ update_of_ne hx _ _,
    fun h _ hf ↦ eqOn_compl_singleton_iff.1 hf ▸ h _⟩

theorem exists_eqOn_compl_singleton_iff {p : (α → β) → Prop} :
    (∃ f, EqOn f g {a}ᶜ ∧ p f) ↔ ∃ b, p (update g a b) :=
  ⟨fun ⟨_, hf, hp⟩ ↦ ⟨_, eqOn_compl_singleton_iff.1 hf ▸ hp⟩,
    fun ⟨_, hp⟩ ↦ ⟨_, fun _ hx ↦ update_of_ne hx _ _, hp⟩⟩

section Congr

variable {f g g' : α → β} {s t : Set α}

omit [DecidableEq α] in
theorem exists_eqOn_eqOn_of_eqOn_inter (hg : EqOn g g' (s ∩ t)) (hf : EqOn f g t) :
    ∃ f', EqOn f' g' t ∧ EqOn f f' s := by
  classical
  refine ⟨t.piecewise g' f, piecewise_eqOn _ _ _, fun x hx => ?_⟩
  by_cases hxt : x ∈ t
  · rw [piecewise_eq_of_mem _ _ _ hxt, hf hxt, hg ⟨hx, hxt⟩]
  · rw [piecewise_eq_of_notMem _ _ _ hxt]

omit [DecidableEq α] in
theorem exists_eqOn_congr (hg : EqOn g g' (s ∩ t)) {p : (α → β) → Prop}
    (hp : ∀ f f', EqOn f f' s → (p f ↔ p f')) :
    (∃ f, EqOn f g t ∧ p f) ↔ ∃ f, EqOn f g' t ∧ p f := by
  refine ⟨fun ⟨f, hf, h⟩ => ?_, fun ⟨f, hf, h⟩ => ?_⟩
  · obtain ⟨f', hf', hff'⟩ := exists_eqOn_eqOn_of_eqOn_inter hg hf
    exact ⟨f', hf', (hp _ _ hff').1 h⟩
  · obtain ⟨f', hf', hff'⟩ := exists_eqOn_eqOn_of_eqOn_inter hg.symm hf
    exact ⟨f', hf', (hp _ _ hff').1 h⟩

omit [DecidableEq α] in
theorem forall_eqOn_congr (hg : EqOn g g' (s ∩ t)) {p : (α → β) → Prop}
    (hp : ∀ f f', EqOn f f' s → (p f ↔ p f')) :
    (∀ f, EqOn f g t → p f) ↔ ∀ f, EqOn f g' t → p f := by
  simpa only [not_exists, not_and, not_not] using
    (exists_eqOn_congr hg (p := fun f => ¬ p f) fun f f' h => not_congr (hp f f' h)).not

end Congr

end Set
