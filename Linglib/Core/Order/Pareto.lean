/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.Linarith

/-!
# Pareto optimality and linear scalarization

Two objectives to be minimized are compared in the product order on pairs, so the Pareto optimal
points among those satisfying `P` under the objectives `f` are those with `MinimalFor P f`. The
linear scalarization `c.1 + β * c.2` is strictly monotone for `β > 0`, so its minimizers are Pareto
optimal (`MinimalFor.of_fst_add_mul_snd_le`). The converse fails without convexity: a Pareto
optimal point need not minimize the scalarization at any weight. As the weight `β` grows, the
minimizers trade the second objective for the first.

## Main statements

* `strictMono_fst_add_mul_snd`: the scalarization is strictly monotone for a positive weight.
* `MinimalFor.of_fst_add_mul_snd_le`: a minimizer of the scalarization at a positive weight is
  Pareto optimal.
* `exists_minimal_forall_exists_fst_add_mul_snd_lt`: three points of which one is Pareto optimal
  yet beaten under the scalarization at every weight.
* `snd_le_of_fst_add_mul_snd_le`, `fst_le_of_fst_add_mul_snd_le`: of two points, each no worse
  than the other at one of two weights, the one preferred at the larger weight has the smaller
  second objective and, for nonnegative weights, the larger first objective.
* `antitone_snd_of_fst_add_mul_snd_le`, `monotoneOn_fst_of_fst_add_mul_snd_le`: along a curve of
  minimizers the second objective falls and the first rises with the weight.

## References

* [boyd-vandenberghe-2004], the scalarization of vector optimization problems.
-/

@[expose] public section

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {β β₁ β₂ : 𝕜}
  {a b : 𝕜 × 𝕜}

theorem strictMono_fst_add_mul_snd (hβ : 0 < β) : StrictMono fun c : 𝕜 × 𝕜 ↦ c.1 + β * c.2 :=
  fun a b h ↦ by
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Prod.lt_iff.1 h
    · exact add_lt_add_of_lt_of_le h₁ (mul_le_mul_of_nonneg_left h₂ hβ.le)
    · exact add_lt_add_of_le_of_lt h₁ (mul_lt_mul_of_pos_left h₂ hβ)

/-- A minimizer of the scalarization at a positive weight is Pareto optimal. -/
theorem MinimalFor.of_fst_add_mul_snd_le {ι : Type*} {P : ι → Prop} {f : ι → 𝕜 × 𝕜} {i : ι}
    (hβ : 0 < β) (hi : P i) (h : ∀ j, P j → (f i).1 + β * (f i).2 ≤ (f j).1 + β * (f j).2) :
    MinimalFor P f i :=
  .of_strictMonoOn_comp (g := fun c : 𝕜 × 𝕜 ↦ c.1 + β * c.2)
    ((strictMono_fst_add_mul_snd hβ).strictMonoOn _) ⟨hi, fun j hj _ ↦ h j hj⟩

/-- The converse fails without convexity. Of the points `(0, 4)`, `(4, 0)` and `(2, 3)` the last
is Pareto optimal, yet at every weight one of the others has a smaller scalarization. -/
theorem exists_minimal_forall_exists_fst_add_mul_snd_lt :
    ∃ (P : 𝕜 × 𝕜 → Prop) (c : 𝕜 × 𝕜), Minimal P c ∧
      ∀ β : 𝕜, ∃ d, P d ∧ d.1 + β * d.2 < c.1 + β * c.2 := by
  refine ⟨fun c ↦ c = (0, 4) ∨ c = (4, 0) ∨ c = (2, 3), (2, 3), ⟨.inr (.inr rfl), ?_⟩,
    fun β ↦ ?_⟩
  · rintro d (rfl | rfl | rfl) h
    · exact absurd (Prod.mk_le_mk.1 h).2 (by norm_num)
    · exact absurd (Prod.mk_le_mk.1 h).1 (by norm_num)
    · exact le_rfl
  · rcases lt_or_ge β 2 with h | h
    · exact ⟨(0, 4), .inl rfl, by dsimp only; linarith⟩
    · exact ⟨(4, 0), .inr (.inl rfl), by dsimp only; linarith⟩

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
