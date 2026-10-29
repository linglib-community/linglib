module

public import Linglib.Core.SocialChoice.Rules
public import Linglib.Semantics.Degree.MeasurePhrase
public import Linglib.Semantics.Degree.UniversalScale

/-!
# van Rooij (2011): Measurement and Interadjective Comparisons

A measure is unique up to a group of transformations, and a statement about measures is
meaningful when every such transformation preserves its truth. Van Rooij measures
individual–adjective pairs on one scale, so that *x is P-er than y is Q* compares two values of a
single measure, and asks which transformations that measure is unique up to when one
transformation applies to every adjective: comparing pairs needs only a co-ordinal scale, a
differential across adjectives a co-interval scale, and a factor across adjectives a co-ratio scale.
If each adjective's scale is unique up to its own transformations, no comparison across adjectives
is meaningful. Bale's universal degrees normalize each adjective's ranking, and so make even ratios
across adjectives meaningful from merely ordinal measures, which van Rooij counts against them.

## Implementation notes

* A measure on individual–adjective pairs is a profile of `SocialChoice` with adjectives as its
  individuals, following the paper's analogy with interpersonal comparisons of utility. The
  co-ordinal, co-interval and co-ratio scales are Sen's comparability classes `ordinalLevel`,
  `cardinalFull` and `ratioFull`, and separate scales per adjective are `ordinal`.
* Measures are real-valued, as in the paper; universal degrees are rational.

## TODO

* Section 2's choice structures, after van Benthem, and section 4.3's constructions of a
  co-ordinal scale from a choice function on pairs and from Klein's modifiers.

## References

* [van-rooij-2011]
* [bale-2008]
* [sassoon-2010]
* [sen-1970]
-/

@[expose] public section

namespace VanRooij2011

open Degree SocialChoice Finset

variable {X Ad K : Type*}

/-- The measure a profile assigns individual–adjective pairs. -/
def pairs (v : Profile Ad X K) (p : X × Ad) : K := v p.1 p.2

theorem pairs_transform (f : Ad → K → K) (v : Profile Ad X K) (p : X × Ad) :
    pairs (v.transform f) p = f p.2 (pairs v p) := rfl

/-! ### Comparisons across adjectives -/

/-- *x is P-er than y is Q* holds when the pair of `x` and P measures more than the pair of `y`
and Q. -/
def comparative (x : X) (P : Ad) (y : X) (Q : Ad) (v : Profile Ad X ℝ) : Prop :=
  (x, P) ∈ (pairs v) ⁻¹' Set.Ioi (pairs v (y, Q))

/-- *x is d-much P-er than y is Q*. -/
def differential (x : X) (P : Ad) (y : X) (Q : Ad) (d : ℝ) (v : Profile Ad X ℝ) : Prop :=
  DifferentialComparative (pairs v) (x, P) (y, Q) d

/-- *x is n times as P as y is Q*. -/
def factor (x : X) (P : Ad) (y : X) (Q : Ad) (n : ℝ) (v : Profile Ad X ℝ) : Prop :=
  FactorEquative (pairs v) (x, P) (y, Q) n

/-- *x is P-er than y by more than z is Q-er than w*. -/
def differenceComparative (x y : X) (P : Ad) (z w : X) (Q : Ad) (v : Profile Ad X ℝ) : Prop :=
  pairs v (z, Q) - pairs v (w, Q) < pairs v (x, P) - pairs v (y, P)

section Sentences

variable (x y z w : X) (P Q : Ad)

/-- Comparing across adjectives needs only a co-ordinal scale. -/
theorem comparative_ordinalLevel : Invariant ordinalLevel (comparative x P y Q) := by
  rintro f ⟨u, hu, hf⟩ v
  have : pairs (v.transform f) = u ∘ pairs v := funext fun p ↦ by
    rw [pairs_transform, hf]; rfl
  simp only [comparative, this]
  exact propext hu.lt_iff_lt

/-- With a separate strictly increasing map for each adjective, comparing across two adjectives
is not meaningful. -/
theorem not_comparative_ordinal [DecidableEq Ad] (hPQ : P ≠ Q) :
    ¬ Invariant ordinal (comparative x P y Q) := by
  intro h
  let v : Profile Ad X ℝ := fun _ i ↦ if i = P then 1 else 0
  let f : Ad → ℝ → ℝ := fun i t ↦ if i = Q then t + 2 else t
  have hf : f ∈ (ordinal : Set (Ad → ℝ → ℝ)) := fun i a b hab ↦ by
    by_cases hi : i = Q <;> simp [f, hi, hab]
  have h₁ : comparative x P y Q v := by
    simp [comparative, pairs, v, hPQ.symm]
  have h₂ : ¬ comparative x P y Q (v.transform f) := by
    simp [comparative, pairs, Profile.transform, v, f, hPQ, hPQ.symm]
  exact h₂ (h f hf v ▸ h₁)

/-- A differential across adjectives holds up to a common change of unit and origin, once its
amount is rescaled by the unit. -/
theorem differential_cardinalFull {f : Ad → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hf : ∀ i t, f i t = a * t + b) (d : ℝ) (v : Profile Ad X ℝ) :
    differential x P y Q (a * d) (v.transform f) ↔ differential x P y Q d v := by
  have : pairs (v.transform f) = fun p ↦ a * pairs v p + b := funext fun p ↦ by
    rw [pairs_transform, hf]
  rw [differential, differential, this]
  exact differentialComparative_const_mul_add_const _ ha.ne' b _ _ d

/-- A factor across adjectives holds up to a common change of unit. -/
theorem factor_ratioFull (n : ℝ) : Invariant ratioFull (factor x P y Q n) := by
  rintro f ⟨a, ha, hf⟩ v
  have : pairs (v.transform f) = fun p ↦ a * pairs v p := funext fun p ↦ by
    rw [pairs_transform, hf]
  simp only [factor, this]
  exact propext (factorEquative_const_mul _ ha.ne' _ _ n)

/-- A factor across adjectives does not survive a common change of origin. -/
theorem not_factor_cardinalFull [DecidableEq X] [DecidableEq Ad] (hne : (x, P) ≠ (y, Q)) :
    ¬ Invariant cardinalFull (factor x P y Q 2) := by
  intro h
  have hyQ : ¬ (y = x ∧ Q = P) := fun ⟨h₁, h₂⟩ ↦ hne (by rw [h₁, h₂])
  let v : Profile Ad X ℝ := fun z i ↦ if z = x ∧ i = P then 2 else 1
  let f : Ad → ℝ → ℝ := fun _ t ↦ 1 * t + 1
  have hf : f ∈ (cardinalFull : Set (Ad → ℝ → ℝ)) := ⟨1, one_pos, 1, fun _ _ ↦ rfl⟩
  have h₁ : factor x P y Q 2 v := by
    simp [factor, FactorEquative, pairs, v, hyQ]
  have h₂ : ¬ factor x P y Q 2 (v.transform f) := by
    simp [factor, FactorEquative, pairs, Profile.transform, v, f, hyQ]; norm_num
  exact h₂ (h f hf v ▸ h₁)

/-- Comparing differences on two adjectives survives a common unit with a separate origin per
adjective, since each origin cancels within its own difference; the paper defines this scale in
note 17 without drawing the consequence. -/
theorem differenceComparative_cardinalUnit :
    Invariant cardinalUnit (differenceComparative x y P z w Q) := by
  rintro f ⟨a, ha, b, hf⟩ v
  simp only [differenceComparative, pairs, Profile.transform, hf]
  rw [show ∀ s t c : ℝ, a * s + c - (a * t + c) = a * (s - t) from fun _ _ _ ↦ by ring,
    show ∀ s t c : ℝ, a * s + c - (a * t + c) = a * (s - t) from fun _ _ _ ↦ by ring,
    mul_lt_mul_iff_of_pos_left ha]

end Sentences

/-! ### Bale's universal degrees -/

section Universal

/-- Bale's universal degrees of a profile on the comparison class `C`, adjective by adjective. -/
noncomputable def universal (v : Profile Ad X ℝ) (C : Finset X) : Profile Ad X ℚ :=
  fun x P ↦ universalDegree (v · P) C x

theorem universal_transform {f : Ad → ℝ → ℝ} (hf : f ∈ (ordinal : Set (Ad → ℝ → ℝ)))
    (v : Profile Ad X ℝ) (C : Finset X) : universal (v.transform f) C = universal v C :=
  funext₂ fun x P ↦ congrFun (universalDegree_comp (OrderEmbedding.ofStrictMono (f P) (hf P))
    (v · P) C) x

/-- Read through universal degrees, *x is n times as P as y is Q* survives a separate strictly
increasing map per adjective, so a ratio across adjectives becomes meaningful although each
adjective's measure is only ordinal. -/
theorem factor_universal_ordinal (C : Finset X) (x y : X) (P Q : Ad) (n : ℚ) :
    Invariant ordinal fun v : Profile Ad X ℝ ↦
      FactorEquative (pairs (universal v C)) (x, P) (y, Q) n := by
  intro f hf v
  simp only [universal_transform hf]

theorem universal_not_affine :
    ¬ ∃ a b : ℚ, ∀ i, universalDegree ![(1 : ℕ), 2, 4] univ i = a * ![(1 : ℚ), 2, 4] i + b := by
  rintro ⟨a, b, h⟩
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  rw [show universalDegree ![(1 : ℕ), 2, 4] univ 0 = 1 / 3 by decide +kernel] at h₀
  rw [show universalDegree ![(1 : ℕ), 2, 4] univ 1 = 2 / 3 by decide +kernel] at h₁
  rw [show universalDegree ![(1 : ℕ), 2, 4] univ 2 = 1 by decide +kernel] at h₂
  simp at h₀ h₁ h₂
  linarith

end Universal

/-! ### Negative adjectives and multidimensional adjectives -/

theorem shorter_iff_taller {E : Type*} (height : E → ℝ) (m : ℝ) (x y : E) (d : ℝ) :
    DifferentialComparative (fun z ↦ m - height z) y x d ↔
      DifferentialComparative height x y d :=
  differentialComparative_const_sub height m x y d

theorem three_times_as_short_not_meaningful :
    FactorEquative ![(-6 : ℝ), -2] 0 1 3 ∧ ¬ FactorEquative (fun i ↦ ![(-6 : ℝ), -2] i + 1) 0 1 3 :=
  ⟨by norm_num [FactorEquative], by norm_num [FactorEquative]⟩

theorem not_utilitarian_ordinalLevel :
    ¬ Invariant ordinalLevel (utilitarian ![(1 : ℚ), 1] : Rule (Fin 2) (Fin 2) ℚ) := by
  intro h
  let v : Profile (Fin 2) (Fin 2) ℚ := ![![0, 3], ![2, 2]]
  have hf : (fun _ t ↦ t ^ 3 : Fin 2 → ℚ → ℚ) ∈ (ordinalLevel : Set (Fin 2 → ℚ → ℚ)) :=
    ⟨(· ^ 3), Odd.strictMono_pow (by decide), fun _ ↦ rfl⟩
  have := congrFun₂ (h _ hf v) 0 1
  simp [utilitarian, Profile.transform, v, dotProduct, Fin.sum_univ_two] at this
  norm_num at this

end VanRooij2011
