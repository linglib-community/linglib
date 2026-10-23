/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith

/-!
# Pareto optimality and linear scalarization

Two objectives to be minimized are compared in the product order on pairs, so the Pareto optimal
points among those satisfying `P` under the objectives `f` are those with `MinimalFor P f`. The
linear scalarization `c.1 + β * c.2` is strictly monotone for `β > 0`, so its minimizers are Pareto
optimal (`MinimalFor.of_strictMonoOn_comp`). As the weight `β` grows, the minimizers trade the
second objective for the first.

## Main statements

* `strictMono_fst_add_mul_snd`: the scalarization is strictly monotone for a positive weight.
* `snd_le_of_fst_add_mul_snd_le`, `fst_le_of_fst_add_mul_snd_le`: of two points, each no worse
  than the other at one of two weights, the one preferred at the larger weight has the smaller
  second objective and, for nonnegative weights, the larger first objective.
* `antitone_snd_of_fst_add_mul_snd_le`, `monotoneOn_fst_of_fst_add_mul_snd_le`: along a curve of
  minimizers the second objective falls and the first rises with the weight.
-/

@[expose] public section

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {β β₁ β₂ : 𝕜}
  {a b : 𝕜 × 𝕜}

theorem strictMono_fst_add_mul_snd (hβ : 0 < β) : StrictMono fun c : 𝕜 × 𝕜 ↦ c.1 + β * c.2 :=
  fun a b h ↦ by
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Prod.lt_iff.1 h
    · exact add_lt_add_of_lt_of_le h₁ (mul_le_mul_of_nonneg_left h₂ hβ.le)
    · exact add_lt_add_of_le_of_lt h₁ (mul_lt_mul_of_pos_left h₂ hβ)

theorem snd_le_of_fst_add_mul_snd_le (hβ : β₁ < β₂) (h₁ : a.1 + β₁ * a.2 ≤ b.1 + β₁ * b.2)
    (h₂ : b.1 + β₂ * b.2 ≤ a.1 + β₂ * a.2) : b.2 ≤ a.2 := by
  nlinarith

theorem fst_le_of_fst_add_mul_snd_le (hβ₁ : 0 ≤ β₁) (hβ : β₁ < β₂)
    (h₁ : a.1 + β₁ * a.2 ≤ b.1 + β₁ * b.2) (h₂ : b.1 + β₂ * b.2 ≤ a.1 + β₂ * a.2) : a.1 ≤ b.1 := by
  nlinarith [mul_le_mul_of_nonneg_left (snd_le_of_fst_add_mul_snd_le hβ h₁ h₂) hβ₁]

variable {c : 𝕜 → 𝕜 × 𝕜}

theorem antitone_snd_of_fst_add_mul_snd_le
    (h : ∀ β β', (c β).1 + β * (c β).2 ≤ (c β').1 + β * (c β').2) :
    Antitone fun β ↦ (c β).2 := fun β₁ β₂ hle ↦ by
  obtain hlt | rfl := hle.lt_or_eq
  · exact snd_le_of_fst_add_mul_snd_le hlt (h β₁ β₂) (h β₂ β₁)
  · rfl

theorem monotoneOn_fst_of_fst_add_mul_snd_le
    (h : ∀ β β', (c β).1 + β * (c β).2 ≤ (c β').1 + β * (c β').2) :
    MonotoneOn (fun β ↦ (c β).1) (Set.Ici 0) := fun β₁ hβ₁ β₂ _ hle ↦ by
  obtain hlt | rfl := hle.lt_or_eq
  · exact fst_le_of_fst_add_mul_snd_le hβ₁ hlt (h β₁ β₂) (h β₂ β₁)
  · rfl
