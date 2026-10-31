module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Linglib.Semantics.Aggregation.Basic

/-!
# Classical aggregation rules

This file defines five classical aggregation rules and the conditions they meet or fail. Majority
rule, after May, meets every Arrow condition except weak-ordering outputs. The Pareto rule, after
Weymark, is a quasi-ordering that leaves every trade-off incomparable. The utilitarian rule meets
every Arrow condition except ordinal invariance, failing even ratio-scale invariance. The
Cobb–Douglas rule, after Tsui and Weymark, is ratio-scale invariant on non-negative profiles, and
the maximin rule needs only ordinal level comparability. The Pareto rule is the unanimous verdict
of the utilitarian rules with positive weights, so a trade-off is exactly a pair that two positive
weightings rank oppositely.

## Main definitions

* `Aggregation.majority`: majority rule.
* `Aggregation.paretoRule`: the Pareto rule.
* `Aggregation.utilitarian`: weighted sums of values.
* `Aggregation.maximin`: the lowest value.
* `Aggregation.cobbDouglas`: weighted products of values.

## Main statements

* `Aggregation.paretoRule_iff_forall_utilitarian`: the Pareto rule is the unanimous verdict of
  the positively weighted utilitarian rules.
* `Aggregation.not_ordinalInvariant_utilitarian`: the utilitarian rule needs cardinal
  information.
* `Aggregation.maximin_ordinalLevelInvariant`: the maximin rule needs only ordinal level
  comparability.

## References

* [may-1952]
* [sen-1970]
* [tsui-weymark-1997]
* [weymark-1984]
-/

@[expose] public section

namespace Aggregation

open Finset Function

variable {ι α K : Type*}

/-! ### Majority rule -/

section Majority

variable [Fintype ι] [LinearOrder K] {v : Profile ι α K} {x y : α}

/-- Under majority rule `x ⪰ y` iff at least as many individuals rank `x` weakly above `y` as rank
`y` weakly above `x`. -/
def majority : Rule ι α K := fun v ↦ v ⁻¹'o fun p q ↦ #{i | p i ≤ q i} ≤ #{i | q i ≤ p i}

@[simp]
theorem majority_apply : majority v x y ↔ #{i | v x i ≤ v y i} ≤ #{i | v y i ≤ v x i} :=
  Iff.rfl

instance (v : Profile ι α K) : DecidableRel (majority v) :=
  Order.Preimage.decidable v _

theorem majority_weakPareto [Nonempty ι] : WeakPareto (majority : Rule ι α K) := by
  intro v x y h
  have h₁ : ({i | v x i ≤ v y i} : Finset ι) = ∅ := filter_false_of_mem fun i _ ↦ (h i).not_ge
  have h₂ : ({i | v y i ≤ v x i} : Finset ι) = univ := filter_true_of_mem fun i _ ↦ (h i).le
  simp [AsymmRel, h₁, h₂, Fintype.card_ne_zero]

theorem majority_independent : Independent (majority : Rule ι α K) :=
  independent_preimage _

theorem majority_paretoIndifferent : ParetoIndifferent (majority : Rule ι α K) :=
  paretoIndifferent_preimage fun _ ↦ le_rfl

theorem majority_ordinalInvariant : Invariant ordinal (majority : Rule ι α K) :=
  invariant_preimage fun f hf ↦ funext₂ fun p q ↦ by
    simp only [Order.Preimage, Pi.map_apply, (mem_ordinal.1 hf _).le_iff_le]

theorem majority_anonymous : Anonymous (majority : Rule ι α K) :=
  anonymous_preimage fun σ ↦ funext₂ fun p q ↦ by
    have h : ∀ p q : ι → K, #{i | p (σ i) ≤ q (σ i)} = #{i | p i ≤ q i} :=
      fun p q ↦ card_equiv σ (by simp)
    simp only [Order.Preimage, comp_apply, h]

theorem majority_nonDictatorial [Nontrivial ι] [Nontrivial α] [Nontrivial K] :
    NonDictatorial (majority : Rule ι α K) := by
  intro i hi
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  obtain ⟨k, k', hk⟩ : ∃ k k' : K, k < k' := by
    obtain ⟨k, k', h⟩ := exists_pair_ne K
    exact h.lt_or_gt.elim (fun h ↦ ⟨k, k', h⟩) (fun h ↦ ⟨k', k, h⟩)
  classical
  let v : Profile ι α K := fun z l ↦ if (z = x ∧ l = i) ∨ (z = y ∧ l = j) then k' else k
  have hv : v y i < v x i := by simp [v, hxy.symm, hj.symm, hk]
  have e₁ : ({l | v x l ≤ v y l} : Finset ι) = univ.erase i := by
    rw [← filter_ne']
    refine filter_congr fun l _ ↦ ?_
    by_cases hl : l = i <;> by_cases hl' : l = j <;>
      simp [v, hl, hl', hxy, hxy.symm, hj, hj.symm, hk.le, hk.not_ge]
  have e₂ : ({l | v y l ≤ v x l} : Finset ι) = univ.erase j := by
    rw [← filter_ne']
    refine filter_congr fun l _ ↦ ?_
    by_cases hl : l = i <;> by_cases hl' : l = j <;>
      simp [v, hl, hl', hxy, hxy.symm, hj, hj.symm, hk.le, hk.not_ge]
  have hcard : #(univ.erase i) = #(univ.erase j) := by
    rw [card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_univ _)]
  have := hi v x y hv
  simp only [AsymmRel, majority_apply, e₁, e₂, hcard, le_refl, not_true, and_false] at this

end Majority

/-! ### The Pareto rule -/

section Pareto

variable [Preorder K] {v : Profile ι α K} {x y : α}

/-- Under the Pareto rule `x ⪰ y` iff every individual ranks `x` weakly above `y`, so that the
rule ranks objects by the product order on their vectors. -/
def paretoRule : Rule ι α K := fun v ↦ v ⁻¹'o (· ≥ ·)

@[simp]
theorem paretoRule_apply : paretoRule v x y ↔ v y ≤ v x :=
  Iff.rfl

/-- The Pareto rule ranks `x` strictly above `y` iff the vector of `x` lies strictly above that of
`y`. -/
@[simp]
theorem asymmRel_paretoRule_iff : AsymmRel (paretoRule v) x y ↔ v y < v x :=
  lt_iff_le_not_ge.symm

theorem paretoRule_quasiOrderValued : QuasiOrderValued (paretoRule : Rule ι α K) :=
  quasiOrderValued_preimage

theorem paretoRule_strongPareto : StrongPareto (paretoRule : Rule ι α K) :=
  fun _ _ _ ↦ ⟨id, asymmRel_paretoRule_iff.2⟩

theorem paretoRule_paretoIndifferent : ParetoIndifferent (paretoRule : Rule ι α K) :=
  paretoIndifferent_preimage fun _ ↦ le_rfl

theorem paretoRule_independent : Independent (paretoRule : Rule ι α K) :=
  independent_preimage _

theorem paretoRule_anonymous : Anonymous (paretoRule : Rule ι α K) :=
  anonymous_preimage fun σ ↦ funext₂ fun p q ↦ propext
    ⟨fun h i ↦ by simpa using h (σ.symm i), fun h i ↦ h _⟩

theorem paretoRule_incomparable {i j : ι} (hi : v y i < v x i) (hj : v x j < v y j) :
    ¬ paretoRule v x y ∧ ¬ paretoRule v y x :=
  ⟨fun h ↦ (h j).not_gt hj, fun h ↦ (h i).not_gt hi⟩

end Pareto

theorem paretoRule_ordinalInvariant [LinearOrder K] :
    Invariant ordinal (paretoRule : Rule ι α K) :=
  invariant_preimage fun f hf ↦ funext₂ fun p q ↦ by
    simp only [Order.Preimage, ge_iff_le, Pi.le_def, Pi.map_apply, (mem_ordinal.1 hf _).le_iff_le]

/-! ### The utilitarian rule -/

section Utilitarian

variable [Fintype ι] [Field K] [LinearOrder K] (c : ι → K) {v : Profile ι α K} {x y : α}

/-- Under the utilitarian rule with weights `c`, `x ⪰ y` iff the weighted sum of values favours
`x`: the rule ranks vectors by the linear functional `c ⬝ᵥ ·`. -/
def utilitarian : Rule ι α K := fun v ↦ v ⁻¹'o ((c ⬝ᵥ ·) ⁻¹'o (· ≥ ·))

@[simp]
theorem utilitarian_apply : utilitarian c v x y ↔ c ⬝ᵥ v y ≤ c ⬝ᵥ v x :=
  Iff.rfl

theorem utilitarian_weakOrderValued : WeakOrderValued (utilitarian c : Rule ι α K) :=
  weakOrderValued_preimage

theorem utilitarian_paretoIndifferent : ParetoIndifferent (utilitarian c : Rule ι α K) :=
  paretoIndifferent_preimage fun _ ↦ le_rfl

theorem utilitarian_independent : Independent (utilitarian c : Rule ι α K) :=
  independent_preimage _

variable [IsStrictOrderedRing K]

theorem utilitarian_weakPareto (hc : ∀ i, 0 ≤ c i) (hpos : ∃ i, 0 < c i) :
    WeakPareto (utilitarian c : Rule ι α K) := by
  intro v x y h
  obtain ⟨i, hi⟩ := hpos
  have : c ⬝ᵥ v y < c ⬝ᵥ v x :=
    sum_lt_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (h i).le (hc i))
      ⟨i, mem_univ _, mul_lt_mul_of_pos_left (h i) hi⟩
  exact ⟨this.le, this.not_ge⟩

theorem utilitarian_cardinalUnitInvariant :
    Invariant cardinalUnit (utilitarian c : Rule ι α K) := by
  refine invariant_preimage ?_
  rintro f ⟨s, hs, b, hf⟩
  have key : ∀ p, Pi.map f p = s • p + b := fun p ↦ funext fun i ↦ by simp [hf]
  funext p q
  simp only [Order.Preimage, ge_iff_le, key, dotProduct_add, dotProduct_smul, smul_eq_mul,
    add_le_add_iff_right, mul_le_mul_iff_of_pos_left hs]

theorem utilitarian_nonDictatorial [Nontrivial α] (h₂ : ∀ i, ∃ j, j ≠ i ∧ 0 < c j) :
    NonDictatorial (utilitarian c : Rule ι α K) := by
  intro i hi
  obtain ⟨j, hji, hj⟩ := h₂ i
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  let v : Profile ι α K := fun z ↦
    if z = x then Pi.single i (c j) else if z = y then Pi.single j (c i + c j) else 0
  have hv : v y i < v x i := by simp [v, hxy.symm, hji.symm, hj]
  have hx : c ⬝ᵥ v x = c i * c j := by simp [v]
  have hy : c ⬝ᵥ v y = c j * (c i + c j) := by simp [v, hxy.symm]
  have := (hi v x y hv).1
  simp only [utilitarian_apply, hx, hy, mul_add, mul_comm (c j) (c i)] at this
  exact (lt_add_of_pos_right _ (mul_pos hj hj)).not_ge this

theorem not_ratioInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant ratio (utilitarian c : Rule ι α K) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  let v : Profile ι α K := fun z ↦
    if z = x then Pi.single i (c j) else if z = y then Pi.single j (c i) else 0
  let f : ι → K → K := fun l t ↦ if l = j then 2 * t else t
  have hf : f ∈ ratio := mem_ratio.2 fun l ↦ ⟨if l = j then 2 else 1,
    by split_ifs <;> norm_num, fun t ↦ by simp only [f]; split_ifs <;> simp⟩
  have hx : (v.transform f) x = Pi.single i (c j) := funext fun l ↦ by
    simp only [Profile.transform, v, f, ite_true, Pi.single_apply]
    split_ifs <;> simp_all
  have hy : (v.transform f) y = Pi.single j (2 * c i) := funext fun l ↦ by
    simp only [Profile.transform, v, f, hxy.symm, ite_false, ite_true, Pi.single_apply]
    split_ifs <;> simp_all
  have := congrFun (congrFun (h f hf v) x) y
  simp only [utilitarian_apply, hx, hy, v, ite_true, hxy.symm, ite_false, dotProduct_single,
    mul_comm (c j) (c i), eq_iff_iff] at this
  have hpos := mul_pos hi hj
  exact (this.2 le_rfl).not_gt (by linarith)

theorem not_ordinalInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant ordinal (utilitarian c : Rule ι α K) :=
  fun h ↦ not_ratioInvariant_utilitarian c hij hi hj (h.mono ratio_subset_ordinal)

omit c

/-- The Pareto rule ranks `x` weakly above `y` iff every utilitarian rule with positive weights
does. -/
theorem paretoRule_iff_forall_utilitarian :
    paretoRule v x y ↔ ∀ c : ι → K, (∀ i, 0 < c i) → utilitarian c v x y := by
  refine ⟨fun h c hc ↦ dotProduct_le_dotProduct_of_nonneg_left h fun i ↦ (hc i).le, fun h ↦ ?_⟩
  by_contra hxy
  obtain ⟨i, hi⟩ : ∃ i, v x i < v y i := by simpa [Pi.le_def] using hxy
  classical
  set d := v y - v x
  have hd : 0 < d i := sub_pos.2 hi
  -- weight individual `i` heavily enough to outweigh all the others
  set M := |1 ⬝ᵥ d| / d i + 1
  have hc : ∀ j, 0 < (1 + Pi.single i M : ι → K) j := fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using add_pos one_pos (by positivity : 0 < M)
    · simp [hj]
  have h' := h _ hc
  rw [utilitarian_apply, ← sub_nonpos, ← dotProduct_sub, add_dotProduct, single_dotProduct] at h'
  have : M * d i = |1 ⬝ᵥ d| + d i := by simp only [M, add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
  linarith [neg_abs_le (1 ⬝ᵥ d)]

theorem asymmRel_paretoRule_iff_forall_utilitarian :
    AsymmRel (paretoRule v) x y ↔
      ∀ c : ι → K, (∀ i, 0 < c i) → AsymmRel (utilitarian c v) x y := by
  refine ⟨fun ⟨h, h'⟩ c hc ↦ ?_, fun h ↦ ⟨?_, fun h' ↦ ?_⟩⟩
  · obtain ⟨i, hi⟩ : ∃ i, v y i < v x i := by simpa [Pi.le_def] using h'
    have : c ⬝ᵥ v y < c ⬝ᵥ v x :=
      sum_lt_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (h j) (hc j).le)
        ⟨i, mem_univ _, mul_lt_mul_of_pos_left hi (hc i)⟩
    exact ⟨this.le, this.not_ge⟩
  · exact paretoRule_iff_forall_utilitarian.2 fun c hc ↦ (h c hc).1
  · exact (h 1 fun _ ↦ one_pos).2 (paretoRule_iff_forall_utilitarian.1 h' 1 fun _ ↦ one_pos)

end Utilitarian

/-! ### The maximin rule -/

section Maximin

variable [Fintype ι] [Nonempty ι] [LinearOrder K] {v : Profile ι α K} {x y : α}

/-- Under the maximin rule, `x ⪰ y` iff the lowest value of `x` is at least the lowest value of
`y`. -/
def maximin : Rule ι α K := fun v ↦ v ⁻¹'o ((univ.inf' univ_nonempty ·) ⁻¹'o (· ≥ ·))

@[simp]
theorem maximin_apply :
    maximin v x y ↔ univ.inf' univ_nonempty (v y) ≤ univ.inf' univ_nonempty (v x) :=
  Iff.rfl

/-- The maximin rule needs only ordinal level comparability, since a common strictly increasing
map moves every lowest value alike. -/
theorem maximin_ordinalLevelInvariant : Invariant ordinalLevel (maximin : Rule ι α K) := by
  refine invariant_preimage ?_
  rintro _ ⟨u, hu : StrictMono u, rfl⟩
  have key (p : ι → K) :
      univ.inf' univ_nonempty (Pi.map (const ι u) p) = u (univ.inf' univ_nonempty p) := by
    rw [apply_inf'_eq_inf'_comp univ_nonempty u fun a b ↦ hu.monotone.map_min]
    rfl
  funext p q
  simp only [Order.Preimage, ge_iff_le, key, hu.le_iff_le]

end Maximin

/-! ### The Cobb–Douglas rule -/

section CobbDouglas

variable [Fintype ι] (c : ι → ℝ) {v : Profile ι α ℝ} {x y : α}

/-- Under the Cobb–Douglas rule with exponents `c`, `x ⪰ y` iff the weighted geometric product of
values favours `x`. -/
def cobbDouglas : Rule ι α ℝ := fun v ↦ v ⁻¹'o ((fun p ↦ ∏ i, p i ^ c i) ⁻¹'o (· ≥ ·))

@[simp]
theorem cobbDouglas_apply : cobbDouglas c v x y ↔ ∏ i, v y i ^ c i ≤ ∏ i, v x i ^ c i :=
  Iff.rfl

theorem cobbDouglas_weakOrderValued : WeakOrderValued (cobbDouglas c : Rule ι α ℝ) :=
  weakOrderValued_preimage

theorem cobbDouglas_paretoIndifferent : ParetoIndifferent (cobbDouglas c : Rule ι α ℝ) :=
  paretoIndifferent_preimage fun _ ↦ le_rfl

theorem cobbDouglas_independent : Independent (cobbDouglas c : Rule ι α ℝ) :=
  independent_preimage _

theorem cobbDouglas_transform_of_nonneg {f : ι → ℝ → ℝ} (hf : f ∈ ratio)
    (hv : ∀ x i, 0 ≤ v x i) : cobbDouglas c (v.transform f) = cobbDouglas c v := by
  choose s hs hf using mem_ratio.1 hf
  funext x y
  simp only [cobbDouglas_apply, Profile.transform, hf, Real.mul_rpow (hs _).le (hv _ _),
    prod_mul_distrib]
  exact propext (mul_le_mul_iff_of_pos_left (prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hs i) _))

end CobbDouglas

end Aggregation
