module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Comparable
public import Linglib.Core.LinearAlgebra.Matrix.DotProduct
public import Linglib.Semantics.Aggregation.Basic

/-!
# Classical aggregation rules

This file defines six classical aggregation rules, each ranking objects by a relation on their
vectors of values, and the conditions they meet or fail. Majority rule, after May, meets every
Arrow condition except weak-ordering outputs. The Pareto rule, after Weymark, is a quasi-ordering
that leaves every trade-off incomparable, and Sen's Pareto extension rule makes those
incomparabilities indifferences. The utilitarian rule and the maximin rule each meet Arrow's
conditions once values are comparable across individuals, the first [with a common
unit](##Aggregation.utilitarian_arrovian_cardinalUnit) and the second [with a common ordinal
scale](##Aggregation.maximin_arrovian_ordinalLevel); the Cobb–Douglas rule, after Tsui and
Weymark, is ratio-scale invariant on non-negative profiles. The Pareto rule is [the infimum of the
utilitarian rules with positive weights](##Aggregation.paretoRule_eq_iInf_utilitarian) and the
Pareto extension rule their supremum, by the self-duality of the nonnegative orthant.

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
def majority : Rule ι α K := ofRel fun p q ↦ #{i | p i ≤ q i} ≤ #{i | q i ≤ p i}

@[simp]
theorem majority_apply : majority v x y ↔ #{i | v x i ≤ v y i} ≤ #{i | v y i ≤ v x i} :=
  Iff.rfl

instance (v : Profile ι α K) : DecidableRel (majority v) :=
  inferInstanceAs (DecidableRel (ofRel _ v))

theorem majority_completeValued : CompleteValued (majority : Rule ι α K) :=
  fun _ ↦ ⟨fun _ _ ↦ le_total _ _⟩

theorem majority_weakPareto [Nonempty ι] : WeakPareto (majority : Rule ι α K) := by
  intro v x y h
  have h₁ : ({i | v x i ≤ v y i} : Finset ι) = ∅ := filter_false_of_mem fun i _ ↦ (h i).not_ge
  have h₂ : ({i | v y i ≤ v x i} : Finset ι) = univ := filter_true_of_mem fun i _ ↦ (h i).le
  simp [AsymmRel, h₁, h₂, Fintype.card_ne_zero]

theorem majority_independent : Independent (majority : Rule ι α K) :=
  independent_ofRel _

theorem majority_paretoIndifferent : ParetoIndifferent (majority : Rule ι α K) :=
  paretoIndifferent_ofRel fun _ ↦ le_rfl

theorem majority_ordinalInvariant : Invariant (ordinal ι K) (majority : Rule ι α K) :=
  invariant_ofRel fun f _ ↦ by
    funext p q
    simp only [Order.Preimage, Pi.smul_apply', OrderEmbedding.smul_def, OrderEmbedding.le_iff_le]

theorem majority_anonymous : Anonymous (majority : Rule ι α K) :=
  anonymous_ofRel fun σ ↦ funext₂ fun p q ↦ by
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
def paretoRule : Rule ι α K := ofRel (· ≥ ·)

@[simp]
theorem paretoRule_apply : paretoRule v x y ↔ v y ≤ v x :=
  Iff.rfl

/-- The Pareto rule ranks `x` strictly above `y` iff the vector of `x` lies strictly above that of
`y`. -/
@[simp]
theorem asymmRel_paretoRule_iff : AsymmRel (paretoRule v) x y ↔ v y < v x :=
  lt_iff_le_not_ge.symm

/-- Under Sen's Pareto extension rule `x ⪰ y` iff the vector of `x` does not lie strictly below that
of `y`: the Pareto rule with every incomparability made an indifference. -/
def paretoExtension : Rule ι α K := ofRel fun p q ↦ ¬ p < q

@[simp]
theorem paretoExtension_apply : paretoExtension v x y ↔ ¬ v x < v y :=
  Iff.rfl

theorem paretoRule_quasiOrderValued : QuasiOrderValued (paretoRule : Rule ι α K) :=
  quasiOrderValued_ofRel

theorem paretoRule_strongPareto : StrongPareto (paretoRule : Rule ι α K) :=
  fun _ _ _ ↦ ⟨id, asymmRel_paretoRule_iff.2⟩

theorem paretoRule_paretoIndifferent : ParetoIndifferent (paretoRule : Rule ι α K) :=
  paretoIndifferent_ofRel fun _ ↦ le_rfl

theorem paretoRule_independent : Independent (paretoRule : Rule ι α K) :=
  independent_ofRel _

theorem paretoRule_anonymous : Anonymous (paretoRule : Rule ι α K) :=
  anonymous_ofRel fun σ ↦ funext₂ fun p q ↦ propext
    ⟨fun h i ↦ by simpa using h (σ.symm i), fun h i ↦ h _⟩

theorem paretoRule_incomparable {i j : ι} (hi : v y i < v x i) (hj : v x j < v y j) :
    IncompRel (paretoRule v) x y :=
  ⟨fun h ↦ (h j).not_gt hj, fun h ↦ (h i).not_gt hi⟩

end Pareto

section Linear

variable [LinearOrder K]

theorem paretoRule_ordinalInvariant : Invariant (ordinal ι K) (paretoRule : Rule ι α K) :=
  invariant_ofRel fun f _ ↦ by
    funext p q
    simp only [Order.Preimage, ge_iff_le, Pi.le_def, Pi.smul_apply', OrderEmbedding.smul_def,
      OrderEmbedding.le_iff_le]

variable [Nontrivial ι] [Nontrivial K]

/-- Two distinct objects make a trade-off at some profile on which individual `i` ranks `x` strictly
above `y`. -/
theorem exists_incompRel_paretoRule {x y : α} (hxy : x ≠ y) (i : ι) :
    ∃ v : Profile ι α K, v y i < v x i ∧ IncompRel (paretoRule v) x y := by
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨k, k', hk⟩ := exists_pair_lt K
  classical
  let v : Profile ι α K := fun z l ↦ if (z = x ↔ l = i) then k' else k
  have hi : v y i < v x i := by simp [v, hxy.symm, hk]
  exact ⟨v, hi, paretoRule_incomparable hi (j := j) (by simp [v, hj, hxy.symm, hk])⟩

variable [Nontrivial α]

theorem not_completeValued_paretoRule : ¬ CompleteValued (paretoRule : Rule ι α K) := fun h ↦
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  let ⟨v, _, hv⟩ := exists_incompRel_paretoRule (K := K) hxy (Classical.arbitrary ι)
  hv.1 (((h v).total x y).resolve_right hv.2)

theorem paretoRule_nonDictatorial : NonDictatorial (paretoRule : Rule ι α K) := fun i hi ↦
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  let ⟨v, hv, h⟩ := exists_incompRel_paretoRule (K := K) hxy i
  h.1 (hi v x y hv).1

end Linear

/-! ### The utilitarian rule -/

section Utilitarian

variable [Fintype ι] [Field K] [LinearOrder K] (c : ι → K) {v : Profile ι α K} {x y : α}

/-- Under the utilitarian rule with weights `c`, `x ⪰ y` iff the weighted sum of values favours
`x`: the rule ranks vectors by the linear functional `c ⬝ᵥ ·`. -/
def utilitarian : Rule ι α K := ofRel ((c ⬝ᵥ ·) ⁻¹'o (· ≥ ·))

@[simp]
theorem utilitarian_apply : utilitarian c v x y ↔ c ⬝ᵥ v y ≤ c ⬝ᵥ v x :=
  Iff.rfl

theorem utilitarian_weakOrderValued : WeakOrderValued (utilitarian c : Rule ι α K) :=
  weakOrderValued_ofRel

theorem utilitarian_paretoIndifferent : ParetoIndifferent (utilitarian c : Rule ι α K) :=
  paretoIndifferent_ofRel fun _ ↦ le_rfl

theorem utilitarian_independent : Independent (utilitarian c : Rule ι α K) :=
  independent_ofRel _

/-- Weighting a single individual makes it a dictator. -/
theorem isDictator_utilitarian_single [DecidableEq ι] (i : ι) :
    IsDictator (utilitarian (Pi.single i 1) : Rule ι α K) i := fun v x y h ↦ by
  simp only [AsymmRel, utilitarian_apply, single_dotProduct, one_mul]
  exact ⟨h.le, h.not_ge⟩

variable [IsStrictOrderedRing K]

theorem utilitarian_weakPareto (hc : ∀ i, 0 ≤ c i) (hpos : ∃ i, 0 < c i) :
    WeakPareto (utilitarian c : Rule ι α K) := by
  intro v x y h
  obtain ⟨i, hi⟩ := hpos
  have := dotProduct_lt_dotProduct_of_nonneg_left (fun j ↦ (h j).le) hc ⟨i, hi, h i⟩
  exact ⟨this.le, this.not_ge⟩

theorem utilitarian_cardinalUnitInvariant :
    Invariant (cardinalUnit ι K) (utilitarian c : Rule ι α K) := by
  refine invariant_ofRel ?_
  rintro f ⟨s, hs, b, hf⟩
  have key : ∀ p : ι → K, f • p = s • p + b := fun p ↦ funext fun i ↦ by simp [hf]
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

/-- With positive weights on two or more individuals the utilitarian rule meets Arrow's conditions
with cardinal unit comparability in place of ordinal non-comparability ([sen-1970]). -/
theorem utilitarian_arrovian_cardinalUnit [Nontrivial ι] [Nontrivial α] (hc : ∀ i, 0 < c i) :
    Arrovian (cardinalUnit ι K) (utilitarian c : Rule ι α K) :=
  ⟨utilitarian_cardinalUnitInvariant c, utilitarian_weakOrderValued c,
    utilitarian_weakPareto c (fun i ↦ (hc i).le) ⟨Classical.arbitrary ι, hc _⟩,
    utilitarian_independent c,
    utilitarian_nonDictatorial c fun i ↦ let ⟨j, hj⟩ := exists_ne i; ⟨j, hj, hc j⟩⟩

theorem not_weakPareto_utilitarian_zero [Nontrivial α] :
    ¬ WeakPareto (utilitarian 0 : Rule ι α K) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  exact (h (fun z _ ↦ if z = x then 1 else 0) x y fun _ ↦ by simp [hxy.symm]).2 (by simp)

theorem not_ratioInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant (ratio ι K) (utilitarian c : Rule ι α K) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  let v : Profile ι α K := fun z ↦
    if z = x then Pi.single i (c j) else if z = y then Pi.single j (c i) else 0
  obtain ⟨e, he⟩ : ∃ e : K ↪o K, ∀ t, e t = 2 * t :=
    ⟨OrderEmbedding.ofStrictMono (2 * ·) fun _ _ h ↦ mul_lt_mul_of_pos_left h two_pos,
      fun _ ↦ rfl⟩
  let f : ι → K ↪o K := fun l ↦ if l = j then e else RelEmbedding.refl _
  have hf : f ∈ ratio ι K := mem_ratio.2 fun l ↦ ⟨if l = j then 2 else 1,
    by split_ifs <;> norm_num, fun t ↦ by simp only [f]; split_ifs <;> simp [he]⟩
  have hx : f • v x = Pi.single i (c j) := funext fun l ↦ by
    simp only [Pi.smul_apply', OrderEmbedding.smul_def, v, f, ite_true, Pi.single_apply]
    split_ifs <;> simp_all
  have hy : f • v y = Pi.single j (2 * c i) := funext fun l ↦ by
    simp only [Pi.smul_apply', OrderEmbedding.smul_def, v, f, hxy.symm, ite_false, ite_true,
      Pi.single_apply]
    split_ifs <;> simp_all
  have := congrFun (congrFun (h _ hf v) x) y
  simp only [utilitarian_apply, Pi.smul_apply, hx, hy, eq_iff_iff] at this
  simp only [v, ite_true, hxy.symm, ite_false, dotProduct_single, mul_comm (c j) (c i)] at this
  have hpos := mul_pos hi hj
  exact (this.2 le_rfl).not_gt (by linarith)

theorem not_ordinalInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant (ordinal ι K) (utilitarian c : Rule ι α K) :=
  fun h ↦ not_ratioInvariant_utilitarian c hij hi hj (h.mono (Set.subset_univ _))

/-- The utilitarian rule needs differences of values: a strictly increasing map applied to every
individual alike already changes it. -/
theorem not_ordinalLevelInvariant_utilitarian [Nontrivial α] {i j : ι} (hij : i ≠ j) (hi : 0 < c i)
    (hj : 0 < c j) : ¬ Invariant (ordinalLevel ι K) (utilitarian c : Rule ι α K) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  obtain ⟨u, hu₀, hu₁, hu₂⟩ : ∃ u : K ↪o K,
      u 0 = 0 ∧ u (-c j) = -c j ∧ u (c i) = 2 * c i :=
    ⟨OrderEmbedding.ofStrictMono (fun t ↦ max t (2 * t)) fun s t hst ↦
      max_lt (hst.trans_le (le_max_left _ _))
        ((mul_lt_mul_of_pos_left hst two_pos).trans_le (le_max_right _ _)), by simp,
      max_eq_left (by linarith), max_eq_right (by linarith)⟩
  classical
  let v : Profile ι α K := fun z ↦
    if z = x then Pi.single i (-c j) + Pi.single j (c i) else 0
  have hx : const ι u • v x = Pi.single i (-c j) + Pi.single j (2 * c i) :=
    funext fun l ↦ by
      by_cases h₁ : l = i
      · subst h₁; simp [v, hij, hu₁]
      · by_cases h₂ : l = j
        · subst h₂; simp [v, h₁, hu₂]
        · simp [v, h₁, h₂, hu₀]
  have hy : const ι u • v y = 0 := funext fun l ↦ by
    simp [v, hxy.symm, hu₀]
  have := (congrFun₂ (h _ ⟨u, Set.mem_univ _, rfl⟩ v) y x).mpr (by simp [v, hxy.symm, mul_comm])
  simp only [utilitarian_apply, Pi.smul_apply] at this
  rw [hx, hy] at this
  simp only [dotProduct_add, dotProduct_single, dotProduct_zero] at this
  nlinarith [mul_pos hi hj]

omit c

/-- The Pareto rule ranks `x` weakly above `y` iff every utilitarian rule with positive weights
does. -/
theorem paretoRule_iff_forall_utilitarian :
    paretoRule v x y ↔ ∀ c : ι → K, (∀ i, 0 < c i) → utilitarian c v x y :=
  le_iff_forall_pos_dotProduct_le

theorem asymmRel_paretoRule_iff_forall_utilitarian :
    AsymmRel (paretoRule v) x y ↔
      ∀ c : ι → K, (∀ i, 0 < c i) → AsymmRel (utilitarian c v) x y := by
  simp only [AsymmRel, utilitarian_apply, ← lt_iff_le_not_ge]
  exact lt_iff_forall_pos_dotProduct_lt

/-- The Pareto rule is the infimum of the positively weighted utilitarian rules. -/
theorem paretoRule_eq_iInf_utilitarian :
    (paretoRule : Rule ι α K) = ⨅ (c : ι → K) (_ : ∀ i, 0 < c i), utilitarian c := by
  simp only [paretoRule, utilitarian, ← ofRel_iInf]
  congr 1
  funext p q
  simp only [iInf_apply, iInf_Prop_eq, Order.Preimage, ge_iff_le, le_iff_forall_pos_dotProduct_le]

/-- Sen's Pareto extension rule is the supremum of the positively weighted utilitarian rules. -/
theorem paretoExtension_eq_iSup_utilitarian :
    (paretoExtension : Rule ι α K) = ⨆ (c : ι → K) (_ : ∀ i, 0 < c i), utilitarian c := by
  simp only [paretoExtension, utilitarian, ← ofRel_iSup]
  congr 1
  funext p q
  simp only [iSup_apply, iSup_Prop_eq, Order.Preimage, ge_iff_le, lt_iff_forall_pos_dotProduct_lt,
    not_forall, not_lt, exists_prop]

end Utilitarian

/-! ### The maximin rule -/

section Maximin

variable [Fintype ι] [Nonempty ι] [LinearOrder K] {v : Profile ι α K} {x y : α}

/-- Under the maximin rule, `x ⪰ y` iff the lowest value of `x` is at least the lowest value of
`y`. -/
def maximin : Rule ι α K := ofRel ((univ.inf' univ_nonempty ·) ⁻¹'o (· ≥ ·))

@[simp]
theorem maximin_apply :
    maximin v x y ↔ univ.inf' univ_nonempty (v y) ≤ univ.inf' univ_nonempty (v x) :=
  Iff.rfl

/-- The maximin rule needs only ordinal level comparability, since a common strictly increasing
map moves every lowest value alike. -/
theorem maximin_ordinalLevelInvariant : Invariant (ordinalLevel ι K) (maximin : Rule ι α K) := by
  refine invariant_ofRel ?_
  rintro _ ⟨u, -, rfl⟩
  have key (p : ι → K) :
      univ.inf' univ_nonempty (const ι u • p) = u (univ.inf' univ_nonempty p) :=
    (apply_inf'_eq_inf'_comp univ_nonempty u fun a b ↦ u.monotone.map_min).symm
  funext p q
  simp only [Order.Preimage, ge_iff_le, key, u.le_iff_le]

theorem maximin_weakOrderValued : WeakOrderValued (maximin : Rule ι α K) :=
  weakOrderValued_ofRel

theorem maximin_independent : Independent (maximin : Rule ι α K) :=
  independent_ofRel _

theorem maximin_weakPareto : WeakPareto (maximin : Rule ι α K) := by
  intro v x y h
  have : univ.inf' univ_nonempty (v y) < univ.inf' univ_nonempty (v x) :=
    (lt_inf'_iff _).2 fun i _ ↦ (inf'_le _ (mem_univ i)).trans_lt (h i)
  exact ⟨this.le, this.not_ge⟩

theorem maximin_nonDictatorial [Nontrivial ι] [Nontrivial α] [Nontrivial K] :
    NonDictatorial (maximin : Rule ι α K) := by
  intro i hi
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  obtain ⟨k, k', hk⟩ := exists_pair_lt K
  classical
  let v : Profile ι α K := fun z l ↦ if z = x ∧ l = i then k' else k
  refine (hi v x y (by simp [v, hxy.symm, hk])).2 ?_
  exact (inf'_le _ (mem_univ j)).trans (le_inf' _ _ fun l _ ↦ by simp [v, hj, hxy.symm])

theorem maximin_anonymous : Anonymous (maximin : Rule ι α K) :=
  anonymous_ofRel fun σ ↦ funext₂ fun p q ↦ by
    have key (p : ι → K) : univ.inf' univ_nonempty (p ∘ σ) = univ.inf' univ_nonempty p :=
      le_antisymm (le_inf' _ _ fun i _ ↦ by simpa using inf'_le (p ∘ σ) (mem_univ (σ.symm i)))
        (le_inf' _ _ fun i _ ↦ inf'_le p (mem_univ (σ i)))
    simp only [Order.Preimage, key]

/-- With two or more individuals the maximin rule meets Arrow's conditions with ordinal level
comparability in place of ordinal non-comparability ([sen-1970]). -/
theorem maximin_arrovian_ordinalLevel [Nontrivial ι] [Nontrivial α] [Nontrivial K] :
    Arrovian (ordinalLevel ι K) (maximin : Rule ι α K) :=
  ⟨maximin_ordinalLevelInvariant, maximin_weakOrderValued, maximin_weakPareto,
    maximin_independent, maximin_nonDictatorial⟩

end Maximin

/-! ### The Cobb–Douglas rule -/

section CobbDouglas

variable [Fintype ι] (c : ι → ℝ) {v : Profile ι α ℝ} {x y : α}

/-- Under the Cobb–Douglas rule with exponents `c`, `x ⪰ y` iff the weighted geometric product of
values favours `x`. -/
def cobbDouglas : Rule ι α ℝ := ofRel ((fun p ↦ ∏ i, p i ^ c i) ⁻¹'o (· ≥ ·))

@[simp]
theorem cobbDouglas_apply : cobbDouglas c v x y ↔ ∏ i, v y i ^ c i ≤ ∏ i, v x i ^ c i :=
  Iff.rfl

theorem cobbDouglas_weakOrderValued : WeakOrderValued (cobbDouglas c : Rule ι α ℝ) :=
  weakOrderValued_ofRel

theorem cobbDouglas_paretoIndifferent : ParetoIndifferent (cobbDouglas c : Rule ι α ℝ) :=
  paretoIndifferent_ofRel fun _ ↦ le_rfl

theorem cobbDouglas_independent : Independent (cobbDouglas c : Rule ι α ℝ) :=
  independent_ofRel _

theorem cobbDouglas_smul_of_nonneg {f : ι → ℝ ↪o ℝ} (hf : f ∈ ratio ι ℝ)
    (hv : ∀ x i, 0 ≤ v x i) : cobbDouglas c (f • v) = cobbDouglas c v := by
  choose s hs hf using mem_ratio.1 hf
  funext x y
  simp only [cobbDouglas_apply, Pi.smul_apply, Pi.smul_apply', OrderEmbedding.smul_def, hf,
    Real.mul_rpow (hs _).le (hv _ _), prod_mul_distrib]
  exact propext (mul_le_mul_iff_of_pos_left (prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hs i) _))

end CobbDouglas

end Aggregation
