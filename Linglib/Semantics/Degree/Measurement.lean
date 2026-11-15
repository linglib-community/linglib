module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Tactic.Linarith

/-!
# Differentials and factors under changes of scale

A *differential comparative* (*3 inches taller*) says that one measure is another moved by a
difference, and a *factor equative* (*twice as tall*) that it is another scaled by a ratio. A
statement about measures is meaningful when it is [invariant](##Invariant) under every admissible
change of scale. [A change of scale that is equivariant along a map of
amounts](##factorEquative_comp_iff) carries each statement to the one at the image amount, so [an
affine change of scale acts on a differential by its linear
part](##differentialComparative_comp_affineMap), and [an action that commutes with the
amounts](##factorEquative_const_smul) preserves the statement, as a common unit does for ratios and
a common origin for differences. A factor equative needs a zero, since [a translation preserves it
only when the factor fixes the translation](##factorEquative_add_const_iff). On an ordinal scale
[only the zero differential](##differentialComparative_comp_strictMono_iff) and [the factor
$1$](##factorEquative_comp_strictMono_iff) survive.

## Implementation notes

Amounts act on degrees, ratios by `SMul` and differences by `VAdd`, so a ratio need not itself be a
degree, and dates or degrees Celsius need no origin. The differential comparative is the additive
form of the factor equative.

## TODO

The admissible changes of scale are taken as given. Measurement theory derives them from the
representations of a qualitative structure, and `Aggregation` consumes `Invariant` from here only
for want of that theory.

## References

* [stevens-1946]
* [krantz-1971]
* [sassoon-2010]
* [van-rooij-2011]
-/

@[expose] public section

open Function

variable {E M N C D D' : Type*}

/-! ### Differentials and factors -/

/-- The factor equative *a is n times as Adj as b* holds when the measure of `a` is that of `b`
scaled by `n`. -/
@[to_additive DifferentialComparative
/-- The differential comparative *a is d-much Adj-er than b* holds when the measure of `a` is that
of `b` moved by `d`. -/]
def FactorEquative [SMul M D] (μ : E → D) (a b : E) (n : M) : Prop :=
  μ a = n • μ b

theorem differentialComparative_iff_vsub_eq {V P : Type*} [AddGroup V] [AddTorsor V P]
    {μ : E → P} {a b : E} {d : V} : DifferentialComparative μ a b d ↔ μ a -ᵥ μ b = d :=
  eq_vadd_iff_vsub_eq _ _ _

/-! ### Changes of scale -/

section Comp

variable [SMul M D] [SMul N D'] {g : D → D'} {σ : M → N} {n : M} {n' : N}

@[to_additive differentialComparative_comp_of_semiconj]
theorem factorEquative_comp_of_semiconj (hg : Injective g)
    (h : Semiconj g (n • ·) (n' • ·)) (μ : E → D) (a b : E) :
    FactorEquative (g ∘ μ) a b n' ↔ FactorEquative μ a b n := by
  have h : g (n • μ b) = n' • g (μ b) := h (μ b)
  simp only [FactorEquative, comp_apply, ← h, hg.eq_iff]

@[to_additive differentialComparative_comp_iff_semiconj]
theorem factorEquative_comp_iff_semiconj [Nontrivial E] (hg : Injective g) :
    (∀ (μ : E → D) a b, FactorEquative (g ∘ μ) a b n' ↔ FactorEquative μ a b n) ↔
      Semiconj g (n • ·) (n' • ·) := by
  refine ⟨fun h x ↦ ?_, fun h μ a b ↦ factorEquative_comp_of_semiconj hg h μ a b⟩
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := (h (fun e ↦ if e = a then n • x else x) a b).2 (by simp [FactorEquative, hab.symm])
  simpa [FactorEquative, hab.symm] using this

/-- An injective change of scale that is equivariant along a map `σ` of amounts carries each
statement to the statement whose amount is the image under `σ`. -/
@[to_additive differentialComparative_comp_iff]
theorem factorEquative_comp_iff (hg : Injective g) (h : ∀ m x, g (m • x) = σ m • g x)
    (μ : E → D) (a b : E) (n : M) :
    FactorEquative (g ∘ μ) a b (σ n) ↔ FactorEquative μ a b n :=
  factorEquative_comp_of_semiconj hg (h n) μ a b

end Comp

/-- An action on degrees that commutes with the amounts preserves every statement, as a common
unit does for ratios and a common origin for differences. -/
@[to_additive differentialComparative_const_vadd]
theorem factorEquative_const_smul [SMul M D] [SMul C D] [SMulCommClass C M D] {c : C}
    (hc : Injective (c • · : D → D)) (μ : E → D) (a b : E) (n : M) :
    FactorEquative (fun x ↦ c • μ x) a b n ↔ FactorEquative μ a b n :=
  factorEquative_comp_iff (g := (c • ·)) (σ := id) hc (fun m x ↦ smul_comm c m x) μ a b n

/-- An injective affine change of scale carries a differential to the differential whose amount is
the image under its linear part, so the differences of an interval scale form a ratio scale. -/
theorem differentialComparative_comp_affineMap {k V₁ V₂ P₁ P₂ : Type*} [Ring k] [AddCommGroup V₁]
    [Module k V₁] [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    (f : P₁ →ᵃ[k] P₂) (hf : Injective f) (μ : E → P₁) (a b : E) (d : V₁) :
    DifferentialComparative (f ∘ μ) a b (f.linear d) ↔ DifferentialComparative μ a b d :=
  differentialComparative_comp_iff hf (fun d x ↦ f.map_vadd x d) μ a b d

/-! ### Invariance -/

/-- A function of measures is invariant under a class of changes of scale when none of them
changes its value. A statement invariant under the changes of a scale is meaningful on it. -/
def Invariant {β : Type*} (S : Set (D → D)) (a : (E → D) → β) : Prop :=
  ∀ g ∈ S, ∀ μ, a (g ∘ μ) = a μ

theorem Invariant.mono {β : Type*} {S T : Set (D → D)} (h : S ⊆ T) {a : (E → D) → β}
    (ha : Invariant T a) : Invariant S a :=
  fun g hg ↦ ha g (h hg)

/-- Comparing two measures is meaningful on an ordinal scale. -/
theorem invariant_strictMono_lt [LinearOrder D] (a b : E) :
    Invariant {u : D → D | StrictMono u} fun μ ↦ μ b < μ a :=
  fun _ hu _ ↦ propext (StrictMono.lt_iff_lt hu)

/-! ### Numerical scales -/

-- [sassoon-2010] (13b)
theorem lt_iff_exists_differentialComparative [AddGroup D] [LT D] [AddRightStrictMono D]
    {μ : E → D} {a b : E} : μ b < μ a ↔ ∃ d : D, 0 < d ∧ DifferentialComparative μ a b d := by
  simp [differentialComparative_iff_vsub_eq, sub_pos]

/-- Reversing a scale about a point reverses every differential, so *b is d shorter than a* holds
exactly when *a is d taller than b*, whichever point a negative adjective reverses its antonym
about ([sassoon-2010] (19)). -/
theorem differentialComparative_const_sub [AddCommGroup D] (μ : E → D) (m : D) (a b : E) (d : D) :
    DifferentialComparative (fun e ↦ m - μ e) b a d ↔ DifferentialComparative μ a b d := by
  simp only [differentialComparative_iff_vsub_eq, vsub_eq_sub, sub_sub_sub_cancel_left]

/-- Every strictly increasing change of scale carries a differential to some differential exactly
when its amount is zero, so a differential needs more than an ordinal scale. -/
theorem differentialComparative_comp_strictMono_iff {k : Type*} [CommRing k] [LinearOrder k]
    [IsStrictOrderedRing k] [Nontrivial E] {d : k} :
    (∀ g : k → k, StrictMono g → ∃ d' : k, ∀ (μ : E → k) a b,
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
    exact ⟨0, fun μ a b ↦ by simp [DifferentialComparative, hg.injective.eq_iff]⟩

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
    [Nontrivial E] {n : D} :
    (∀ g : D → D, StrictMono g → ∃ n' : D, ∀ (μ : E → D) a b,
      FactorEquative (g ∘ μ) a b n' ↔ FactorEquative μ a b n) ↔ n = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨n', hn'⟩ := h (· + 1) (strictMono_id.add_const 1)
    simpa using ((factorEquative_add_const_iff (E := E) 1 n n').1 hn').2
  · rintro rfl g hg
    exact ⟨1, fun μ a b ↦ by simp [FactorEquative, hg.injective.eq_iff]⟩
