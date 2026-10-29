module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Tactic.Linarith

/-!
# Measure phrases and the changes of scale they survive

A *differential comparative* (*3 inches taller*) says that two measures differ by a given amount,
and a *factor equative* (*twice as tall*) that one measure is a given multiple of another. A
statement about measures is meaningful when every admissible change of scale preserves it: every
strictly increasing map on an ordinal scale, every positive affine map on an interval scale, every
positive scaling on a ratio scale. A differential needs differences but no zero, and an affine
change of scale carries it to the differential whose amount is the image under the change's linear
part. A factor equative needs a zero, so *twice as hot* is meaningless in degrees Celsius. On an
ordinal scale only the zero differential and the factor $1$ survive.

## Main definitions

* `Degree.DifferentialComparative`: two measures differ by a given amount.
* `Degree.FactorEquative`: one measure is a given multiple of another.

## Main statements

* `Degree.differentialComparative_comp_affineMap`: an affine change of scale acts on the amount of a
  differential by its linear part.
* `Degree.differentialComparative_const_sub`: reversing a scale about a point reverses every
  differential.
* `Degree.differentialComparative_comp_strictMono_iff`: only the zero differential survives every
  strictly increasing change of scale.
* `Degree.factorEquative_add_const_iff`: a translation carries a factor equative to a factor
  equative only when the factor fixes the translation.
* `Degree.factorEquative_comp_strictMono_iff`: only the factor $1$ survives every strictly
  increasing change of scale.

## Implementation notes

A differential takes degrees in an additive torsor and amounts in its group, so dates or degrees
Celsius need no origin; a factor multiplies degrees and so needs a ring. A change of scale
carries one statement to another when it semiconjugates adding the first amount, or multiplying by
the first factor, to the second.

## Errata

* [stevens-1946] gives the interval group as $x' = ax + b$ with no sign condition, but also says it
  lies in the isotonic group of increasing maps, which needs $a > 0$.

## References

* [stevens-1946]
* [krantz-1971]
* [sassoon-2010]
* [van-rooij-2011]
-/

@[expose] public section

namespace Degree

open Function

variable {E : Type*}

/-! ### Differentials -/

section Differential

/-- The differential comparative *a is d-much Adj-er than b* holds when the measure of `a` exceeds
that of `b` by `d`. It uses differences of degrees and no zero, so the degrees may form an affine
space, as on an interval scale. -/
def DifferentialComparative {V P : Type*} [VSub V P] (μ : E → P) (a b : E) (d : V) : Prop :=
  μ a -ᵥ μ b = d

-- [sassoon-2010] (13b)
theorem lt_iff_exists_differentialComparative {D : Type*} [AddGroup D] [LT D]
    [AddRightStrictMono D] {μ : E → D} {a b : E} :
    μ b < μ a ↔ ∃ d, 0 < d ∧ DifferentialComparative μ a b d := by
  simp [DifferentialComparative, sub_pos]

section Torsor

variable {V₁ V₂ P₁ P₂ : Type*} [AddGroup V₁] [AddGroup V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]
  {g : P₁ → P₂} {d : V₁} {d' : V₂}

theorem differentialComparative_comp_of_semiconj (hg : Injective g)
    (h : Semiconj g (d +ᵥ ·) (d' +ᵥ ·)) (μ : E → P₁) (a b : E) :
    DifferentialComparative (g ∘ μ) a b d' ↔ DifferentialComparative μ a b d := by
  have h : g (d +ᵥ μ b) = d' +ᵥ g (μ b) := h (μ b)
  rw [DifferentialComparative, DifferentialComparative, ← eq_vadd_iff_vsub_eq,
    ← eq_vadd_iff_vsub_eq, comp_apply, comp_apply, ← h, hg.eq_iff]

theorem differentialComparative_comp_iff_semiconj [Nontrivial E] (hg : Injective g) :
    (∀ (μ : E → P₁) a b,
      DifferentialComparative (g ∘ μ) a b d' ↔ DifferentialComparative μ a b d) ↔
      Semiconj g (d +ᵥ ·) (d' +ᵥ ·) := by
  refine ⟨fun h x ↦ ?_, fun h μ a b ↦ differentialComparative_comp_of_semiconj hg h μ a b⟩
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := (h (fun e ↦ if e = a then d +ᵥ x else x) a b).2 (by
    simp [DifferentialComparative, hab.symm])
  simpa [DifferentialComparative, hab.symm, eq_vadd_iff_vsub_eq] using this

end Torsor

/-- An injective affine change of scale carries a differential to the differential whose amount is
the image under its linear part, so the differences of an interval scale form a ratio scale. -/
theorem differentialComparative_comp_affineMap {k V₁ V₂ P₁ P₂ : Type*} [Ring k] [AddCommGroup V₁]
    [Module k V₁] [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    (f : P₁ →ᵃ[k] P₂) (hf : Injective f) (μ : E → P₁) (a b : E) (d : V₁) :
    DifferentialComparative (f ∘ μ) a b (f.linear d) ↔ DifferentialComparative μ a b d :=
  differentialComparative_comp_of_semiconj hf (fun x ↦ f.map_vadd x d) μ a b

theorem differentialComparative_const_mul_add_const {k : Type*} [Ring k] [IsDomain k]
    (μ : E → k) {a : k} (ha : a ≠ 0) (b : k) (x y : E) (d : k) :
    DifferentialComparative (fun e ↦ a * μ e + b) x y (a * d) ↔
      DifferentialComparative μ x y d :=
  differentialComparative_comp_of_semiconj (g := (a * · + b))
    ((add_left_injective b).comp (mul_right_injective₀ ha))
    (fun t ↦ by simp only [vadd_eq_add, mul_add, add_assoc]) μ x y

/-- Reversing a scale about a point reverses every differential, so *b is d shorter than a* holds
exactly when *a is d taller than b*, whichever point a negative adjective reverses its antonym
about ([sassoon-2010] (19)). -/
theorem differentialComparative_const_sub {D : Type*} [AddCommGroup D] (μ : E → D) (m : D)
    (a b : E) (d : D) :
    DifferentialComparative (fun e ↦ m - μ e) b a d ↔ DifferentialComparative μ a b d := by
  simp only [DifferentialComparative, vsub_eq_sub, sub_sub_sub_cancel_left]

/-- Every strictly increasing change of scale carries a differential to some differential exactly
when its amount is zero, so a differential needs more than an ordinal scale. -/
theorem differentialComparative_comp_strictMono_iff {k : Type*} [CommRing k] [LinearOrder k]
    [IsStrictOrderedRing k] [Nontrivial E] {d : k} :
    (∀ g : k → k, StrictMono g → ∃ d', ∀ (μ : E → k) a b,
      DifferentialComparative (g ∘ μ) a b d' ↔ DifferentialComparative μ a b d) ↔ d = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hg : StrictMono fun x : k ↦ max x (2 * x) := fun x y hxy ↦
      max_lt (hxy.trans_le (le_max_left _ _))
        ((mul_lt_mul_of_pos_left hxy two_pos).trans_le (le_max_right _ _))
    obtain ⟨d', hd'⟩ := h _ hg
    have hs := (differentialComparative_comp_iff_semiconj hg.injective).1 hd'
    have h₀ : max d (2 * d) = d' + max 0 (2 * 0) := by simpa using hs 0
    have h₁ : max 0 (2 * 0) = d' + max (-d) (2 * -d) := by simpa using hs (-d)
    rw [mul_zero, max_self] at h₀ h₁
    rcases le_total d 0 with hd | hd
    · rw [max_eq_left (by linarith : 2 * d ≤ d)] at h₀
      rw [max_eq_right (by linarith : -d ≤ 2 * -d)] at h₁
      linarith
    · rw [max_eq_right (by linarith : d ≤ 2 * d)] at h₀
      rw [max_eq_left (by linarith : 2 * -d ≤ -d)] at h₁
      linarith
  · rintro rfl g hg
    exact ⟨0, fun μ a b ↦ by
      simp [DifferentialComparative, sub_eq_zero, hg.injective.eq_iff]⟩

end Differential

/-! ### Factors -/

section Factor

variable {D : Type*} {g : D → D} {n n' : D}

/-- The factor equative *a is n times as Adj as b* holds when the measure of `a` is `n` times that
of `b`. It multiplies degrees, so it needs a zero, as on a ratio scale. -/
def FactorEquative [Mul D] (μ : E → D) (a b : E) (n : D) : Prop :=
  μ a = n * μ b

theorem factorEquative_comp_of_semiconj [Mul D] (hg : Injective g)
    (h : Semiconj g (n * ·) (n' * ·)) (μ : E → D) (a b : E) :
    FactorEquative (g ∘ μ) a b n' ↔ FactorEquative μ a b n := by
  have h : g (n * μ b) = n' * g (μ b) := h (μ b)
  simp only [FactorEquative, comp_apply, ← h, hg.eq_iff]

theorem factorEquative_comp_iff_semiconj [Mul D] [Nontrivial E] (hg : Injective g) :
    (∀ (μ : E → D) a b, FactorEquative (g ∘ μ) a b n' ↔ FactorEquative μ a b n) ↔
      Semiconj g (n * ·) (n' * ·) := by
  refine ⟨fun h x ↦ ?_, fun h μ a b ↦ factorEquative_comp_of_semiconj hg h μ a b⟩
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := (h (fun e ↦ if e = a then n * x else x) a b).2 (by simp [FactorEquative, hab.symm])
  simpa [FactorEquative, hab.symm] using this

theorem factorEquative_const_mul [CommMonoidWithZero D] [IsCancelMulZero D] (μ : E → D) {c : D}
    (hc : c ≠ 0) (a b : E) (n : D) :
    FactorEquative (fun x ↦ c * μ x) a b n ↔ FactorEquative μ a b n :=
  factorEquative_comp_of_semiconj (g := (c * ·)) (mul_right_injective₀ hc)
    (fun x ↦ mul_left_comm c n x) μ a b

/-- Translating a scale by `c` carries the factor equative of factor `n` to that of factor `n'`
exactly when `n' = n` and `n` fixes `c`, so moving the zero of a scale destroys ratios. -/
theorem factorEquative_add_const_iff [Ring D] [Nontrivial E] (c n n' : D) :
    (∀ (μ : E → D) a b, FactorEquative (fun x ↦ μ x + c) a b n' ↔ FactorEquative μ a b n) ↔
      n' = n ∧ n * c = c := by
  refine (factorEquative_comp_iff_semiconj (E := E) (add_left_injective c)).trans
    ⟨fun h ↦ ?_, fun ⟨hn, hc⟩ x ↦ by simp [hn, mul_add, hc]⟩
  have h₀ : c = n' * c := by simpa using h 0
  have h₁ : n + c = n' * (1 + c) := by simpa using h 1
  rw [mul_add, mul_one, ← h₀, add_left_inj] at h₁
  exact ⟨h₁.symm, h₁ ▸ h₀.symm⟩

/-- Every strictly increasing change of scale carries a factor equative to some factor equative
exactly when its factor is `1`, so a factor equative needs more than an ordinal scale. -/
theorem factorEquative_comp_strictMono_iff [Ring D] [LinearOrder D] [IsStrictOrderedRing D]
    [Nontrivial E] :
    (∀ g : D → D, StrictMono g → ∃ n', ∀ (μ : E → D) a b,
      FactorEquative (g ∘ μ) a b n' ↔ FactorEquative μ a b n) ↔ n = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨n', hn'⟩ := h (· + 1) (strictMono_id.add_const 1)
    simpa using ((factorEquative_add_const_iff (E := E) 1 n n').1 hn').2
  · rintro rfl g hg
    exact ⟨1, fun μ a b ↦ by simp [FactorEquative, hg.injective.eq_iff]⟩

end Factor

end Degree
