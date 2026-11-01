module

public import Linglib.Core.Basic.Sign
public import Linglib.Core.LinearAlgebra.Matrix.Farkas
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Logic.ComparativeProbability.Cancellation
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Basic.Sign.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Scott's theorem

This file proves Scott's theorem: a relation on the subsets of a finite `W` is
[induced by a probability measure](##ComparativeProbability.representable_iff) iff `W` is strictly
more likely than `∅`, every set is at least as likely as `∅`, any two sets compare, and
cancellation holds. The proof restricts cancellation to comparisons of disjoint sets, written as
sign vectors: a comparison `A ≿ B` is a vector `v : W → SignType` with positive support `A` and
negative support `B`, and the sign-vector form of cancellation says that when valid comparisons
sum to zero as integer vectors, each holds reversed.

## Main declarations

* `comparisonSum`: the sum of a multiset of comparisons as integer vectors; a comparison's two
  sides are the supports `posSupport` and `negSupport` of `Core/Basic/Sign.lean`.
* `SignCancellation`: cancellation in sign-vector form, the form the proofs use.
* `Cancellation.signCancellation`: cancellation gives its sign-vector form.
* `SignCancellation.representable`: the Farkas direction.
* `representable_iff`: Scott's theorem.
* `representable_iff_cancellation`: Scott's theorem for a qualitative probability.
* `signCancellation_of_null_atom`: a null atom reduces cancellation to representability one atom
  down.

## Implementation notes

The hard direction is linear-programming duality over `ℚ` (`Matrix.farkas`), on `Fin n` and
transported along `Fintype.equivFin`. The weight vectors representing the order form a
polyhedron, whose normalized points weight the Dirac measures of a representing measure; it is
nonempty unless a Farkas certificate exists, a nonnegative weighting of valid comparisons that
sums to zero yet weights a strict one. Clearing denominators turns the certificate into a
multiset violating `SignCancellation`.

## References

* [scott-1964]
* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

variable {W : Type*}

/-! ### Sign vectors as comparisons -/

private theorem signCast_eq_ite (s : SignType) :
    (s : ℤ) = (if s = 1 then 1 else 0) - (if s = -1 then 1 else 0) := by
  cases s <;> rfl

/-- `comparisonSum M` sums a multiset of sign vectors as an integer vector. -/
def comparisonSum (M : Multiset (W → SignType)) (i : W) : ℤ := (M.map fun v ↦ (v i : ℤ)).sum

@[simp] theorem comparisonSum_zero (i : W) : comparisonSum (0 : Multiset (W → SignType)) i = 0 :=
  rfl

@[simp] theorem comparisonSum_cons (v : W → SignType) (M : Multiset (W → SignType)) (i : W) :
    comparisonSum (v ::ₘ M) i = v i + comparisonSum M i := by
  simp [comparisonSum]

@[simp] theorem comparisonSum_add (M N : Multiset (W → SignType)) (i : W) :
    comparisonSum (M + N) i = comparisonSum M i + comparisonSum N i := by
  simp [comparisonSum]

theorem comparisonSum_coe (L : List (W → SignType)) (i : W) :
    comparisonSum (L : Multiset (W → SignType)) i = (L.map fun v ↦ (v i : ℤ)).sum := by
  simp [comparisonSum]

/-! ### Scott's condition -/

/-- Cancellation in **sign-vector form** says that when a multiset of valid comparisons of
    disjoint sets sums to zero as integer vectors, every comparison in it also holds reversed. -/
def SignCancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ M : Multiset (W → SignType), (∀ v ∈ M, ge (posSupport v) (negSupport v)) →
    comparisonSum M = 0 → ∀ v ∈ M, ge (negSupport v) (posSupport v)

/-- Sign-vector cancellation pulls back along an equivalence of carriers. -/
theorem SignCancellation.transport {α : Type*} (e : W ≃ α) {r : Set W → Set W → Prop}
    (h : SignCancellation r) : SignCancellation (Set.preimage e ⁻¹'o r) := by
  intro M hvalid hsum v hv
  refine h (M.map (· ∘ e)) ?_ ?_ (v ∘ e) (Multiset.mem_map_of_mem _ hv)
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    exact hvalid u hu
  · funext w
    simpa [comparisonSum, Multiset.map_map, Function.comp_def] using congrFun hsum (e w)

section Bridge

private theorem comparisonSum_coe_eq (L : List (W → SignType)) (s : W) :
    comparisonSum (L : Multiset (W → SignType)) s =
      ((L.map fun w ↦ (posSupport w).indicator (1 : W → ℕ) s).sum : ℤ) -
        (L.map fun w ↦ (negSupport w).indicator (1 : W → ℕ) s).sum := by
  classical
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [← Multiset.cons_coe, comparisonSum_cons, ih, List.map_cons, List.sum_cons,
      Set.indicator_apply, mem_posSupport, mem_negSupport, Pi.one_apply, signCast_eq_ite (w s)]
    push_cast
    split_ifs <;> ring

/-- Cancellation gives its sign-vector form, listing the comparisons of a multiset with the
    chosen one first. -/
theorem Cancellation.signCancellation {r : Set W → Set W → Prop} (h : Cancellation r) :
    SignCancellation r := by
  classical
  intro M hge hsum v hv
  have hM : M = ((v :: (M.erase v).toList : List (W → SignType)) : Multiset (W → SignType)) := by
    rw [← Multiset.cons_coe, Multiset.coe_toList, Multiset.cons_erase hv]
  set L := (M.erase v).toList
  refine h L.length (Fin.cons (posSupport v) fun i ↦ posSupport L[i.1])
    (Fin.cons (negSupport v) fun i ↦ negSupport L[i.1]) (fun s ↦ ?_) fun i ↦ ?_
  · have := congrFun hsum s
    rw [hM, comparisonSum_coe_eq, Pi.zero_apply] at this
    simp only [List.map_cons, List.sum_cons] at this
    have hp : ∑ i : Fin L.length, (posSupport L[i.1]).indicator (1 : W → ℕ) s =
        (L.map fun w ↦ (posSupport w).indicator 1 s).sum :=
      Fin.sum_univ_fun_getElem L fun w ↦ (posSupport w).indicator 1 s
    have hn : ∑ i : Fin L.length, (negSupport L[i.1]).indicator (1 : W → ℕ) s =
        (L.map fun w ↦ (negSupport w).indicator 1 s).sum :=
      Fin.sum_univ_fun_getElem L fun w ↦ (negSupport w).indicator 1 s
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hp, hn]
    omega
  · simpa using hge _ (Multiset.mem_of_mem_erase (Multiset.mem_toList.mp (List.getElem_mem _)))

end Bridge

/-! ### Weighted cancellation

The Farkas certificate is a rational weighting of comparisons; `SignCancellation`
handles it once the weights are cleared to natural multiplicities. -/

section Weighted

variable {n : ℕ}

private theorem exists_nat_mul {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) :
    ∃ (D : ℕ) (m : ι → ℕ), 0 < D ∧ ∀ i, (m i : ℚ) = D * w i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ w
  choose z hz using fun i ↦ hb i (Finset.mem_univ i)
  refine ⟨(b : ℤ).natAbs, fun i ↦ (z i).natAbs,
    Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero b), fun i ↦ ?_⟩
  have : ((z i : ℤ) : ℚ) = (b : ℤ) * w i := by simpa [zsmul_eq_mul] using hz i
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, this, abs_mul,
    abs_of_nonneg (hw i)]

private theorem SignCancellation.weighted {ge : Set (Fin n) → Set (Fin n) → Prop}
    (h : SignCancellation ge) (w : (Fin n → SignType) → ℚ) (hw : ∀ v, 0 ≤ w v)
    (hvalid : ∀ v, 0 < w v → ge (posSupport v) (negSupport v))
    (hsum : ∀ i, ∑ v, w v * (v i : ℚ) = 0) {v : Fin n → SignType} (hv : 0 < w v) :
    ge (negSupport v) (posSupport v) := by
  obtain ⟨D, m, hD, hm⟩ := exists_nat_mul w hw
  have hpos : ∀ u, 0 < w u ↔ 0 < m u := fun u ↦ by
    rw [← Nat.cast_pos (α := ℚ), hm]
    exact ⟨fun h ↦ by positivity, fun h ↦ pos_of_mul_pos_right h (Nat.cast_nonneg D)⟩
  -- the multiset with `m u` copies of each comparison `u`
  set M := Finset.univ.val.bind fun u ↦ Multiset.replicate (m u) u
  have hmem : ∀ u, u ∈ M ↔ 0 < w u := fun u ↦ by
    simp [M, Multiset.mem_bind, Multiset.mem_replicate, hpos, Nat.pos_iff_ne_zero]
  refine h M (fun u hu ↦ hvalid u ((hmem u).mp hu)) (funext fun i ↦ ?_) v ((hmem v).mpr hv)
  have hM : comparisonSum M i = ∑ u, (m u : ℤ) * (u i : ℤ) := by
    simp [M, comparisonSum, Multiset.map_bind, Multiset.sum_bind, Multiset.map_replicate,
      Multiset.sum_replicate, Finset.sum_map_val]
  have : ((comparisonSum M i : ℤ) : ℚ) = D * ∑ u, w u * (u i : ℚ) := by
    rw [hM, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun u _ ↦ by rw [hm]; ring
  rw [hsum, mul_zero] at this
  exact_mod_cast this

end Weighted

/-! ### The Farkas direction -/

section Farkas

open scoped Classical Matrix
open MeasureTheory

variable {n : ℕ} (r : Set (Fin n) → Set (Fin n) → Prop)

/-- `coeffs r` has a row for each comparison `v`, `-v` if `v` holds in `r` and `0`
    otherwise. -/
private noncomputable def coeffs : Matrix (Fin n → SignType) (Fin n) ℚ :=
  Matrix.of fun v j ↦ if r (posSupport v) (negSupport v) then -(v j : ℚ) else 0

/-- `bound r v` is `-1` when `v` holds strictly in `r` and `0` otherwise, so that
    `coeffs r *ᵥ x ≤ bound r` asks `v ⬝ᵥ x ≥ 1` of each strict comparison and `v ⬝ᵥ x ≥ 0`
    of each other valid one. -/
private noncomputable def bound (v : Fin n → SignType) : ℚ :=
  if r (posSupport v) (negSupport v) ∧ ¬r (negSupport v) (posSupport v) then -1 else 0

private theorem le_sum_of_mulVec_le {x : Fin n → ℚ} (hx : coeffs r *ᵥ x ≤ bound r)
    {v : Fin n → SignType} (hv : r (posSupport v) (negSupport v)) :
    (if r (negSupport v) (posSupport v) then 0 else 1) ≤ ∑ j, (v j : ℚ) * x j := by
  have h := hx v
  simp only [coeffs, bound, Matrix.mulVec, dotProduct, Matrix.of_apply, hv, ite_true, true_and,
    neg_mul, Finset.sum_neg_distrib] at h
  split_ifs at h ⊢ <;> linarith

/-- `ofSets A B` is the sign vector `+1` on `A` and `-1` on `B`. -/
private noncomputable def ofSets (A B : Set (Fin n)) (i : Fin n) : SignType :=
  if i ∈ A then 1 else if i ∈ B then -1 else 0

private theorem posSupport_ofSets (A B : Set (Fin n)) : posSupport (ofSets A B) = A := by
  ext i
  simp only [mem_posSupport, ofSets]
  split_ifs <;> simp_all

private theorem negSupport_ofSets {A B : Set (Fin n)} (h : Disjoint A B) :
    negSupport (ofSets A B) = B := by
  ext i
  simp only [mem_negSupport, ofSets]
  split_ifs <;> simp_all [Set.disjoint_left.mp h]

private theorem sum_ofSets_mul {A B : Set (Fin n)} (h : Disjoint A B) (x : Fin n → ℚ) :
    ∑ j, (ofSets A B j : ℚ) * x j =
      (∑ j, if j ∈ A then x j else 0) - ∑ j, if j ∈ B then x j else 0 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hA : j ∈ A <;> by_cases hB : j ∈ B
  · exact absurd hB (Set.disjoint_left.mp h hA)
  all_goals simp [ofSets, hA, hB]

private theorem representable_of_feasible [IsQualitativeProbability r] {x : Fin n → ℚ}
    (hx : coeffs r *ᵥ x ≤ bound r) : Representable r := by
  have hsets : ∀ A B : Set (Fin n), Disjoint A B → r A B →
      (if r B A then 0 else 1) ≤
        (∑ j, if j ∈ A then x j else 0) - ∑ j, if j ∈ B then x j else 0 := fun A B hd hg ↦ by
    have := le_sum_of_mulVec_le r hx (by rwa [posSupport_ofSets, negSupport_ofSets hd])
    rwa [posSupport_ofSets, negSupport_ofSets hd, sum_ofSets_mul hd] at this
  have hnn : ∀ j, 0 ≤ x j := fun j ↦ by
    have := hsets {j} ∅ disjoint_bot_right (rel_empty _)
    simp only [Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Set.mem_empty_iff_false, ite_false, Finset.sum_const_zero, sub_zero] at this
    split_ifs at this <;> linarith
  have hσ : 0 < ∑ j, x j := by
    have := hsets Set.univ ∅ disjoint_bot_right (rel_empty _)
    have hnt : ¬r ∅ Set.univ := not_rel_empty_univ
    simp only [Set.mem_univ, ite_true, Set.mem_empty_iff_false, ite_false, Finset.sum_const_zero,
      sub_zero, ite_eq_right hnt] at this
    linarith
  -- the probability measure with masses proportional to `x`
  have hσR : (0 : ℝ) < ∑ j, (x j : ℝ) := by exact_mod_cast hσ
  have hw (j : Fin n) : 0 ≤ (x j : ℝ) / ∑ j, (x j : ℝ) :=
    div_nonneg (by exact_mod_cast hnn j) hσR.le
  have := Measure.isProbabilityMeasure_sum_ofReal_smul_dirac hw
    (by rw [← Finset.sum_div, div_self hσR.ne'])
  have hm (A : Set (Fin n)) :
      (∑ j, ENNReal.ofReal ((x j : ℝ) / ∑ j, (x j : ℝ)) • Measure.dirac j).real A =
        ((∑ j, if j ∈ A then x j else 0 : ℚ) : ℝ) / ((∑ j, x j : ℚ) : ℝ) := by
    rw [Measure.sum_ofReal_smul_dirac_real_apply hw]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j ∈ A <;> simp [hj]
  refine ⟨_, this, reduce_to_disjoint _ fun C D hCD ↦ ?_⟩
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, hm, hm, div_le_div_iff_of_pos_right (by exact_mod_cast hσ), Rat.cast_le]
  constructor
  · intro h
    have := hsets C D hCD h
    split_ifs at this <;> linarith
  · intro h
    by_contra hCD'
    have := hsets D C hCD.symm ((total_of r C D).resolve_left hCD')
    rw [ite_eq_right hCD'] at this
    linarith

private theorem not_signCancellation_of_certificate {y : (Fin n → SignType) → ℚ} (hy : 0 ≤ y)
    (hyA : y ᵥ* coeffs r = 0) (hyb : y ⬝ᵥ bound r < 0) : ¬SignCancellation r := by
  intro hcancel
  -- the weight of a comparison: its certificate weight if it holds
  let w : (Fin n → SignType) → ℚ := fun v ↦ if r (posSupport v) (negSupport v) then y v else 0
  have hw : ∀ v, 0 ≤ w v := fun v ↦ by
    simp only [w]; split_ifs
    exacts [hy v, le_rfl]
  have hvalid : ∀ v, 0 < w v → r (posSupport v) (negSupport v) := fun v hv ↦ by
    by_contra h
    simp only [w, h, ite_false, lt_self_iff_false] at hv
  have hsum : ∀ j, ∑ v, w v * (v j : ℚ) = 0 := fun j ↦ by
    have h := congrFun hyA j
    simp only [Matrix.vecMul, dotProduct, coeffs, Matrix.of_apply, Pi.zero_apply] at h
    have : ∑ v, w v * (v j : ℚ) = -∑ v, y v *
        (if r (posSupport v) (negSupport v) then -(v j : ℚ) else 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun v _ ↦ by simp only [w]; split_ifs <;> ring
    rw [this, h, neg_zero]
  -- some strict comparison carries positive weight
  obtain ⟨v, hyv, hv, hstr⟩ : ∃ v, 0 < y v ∧ r (posSupport v) (negSupport v) ∧
      ¬r (negSupport v) (posSupport v) := by
    by_contra! hall
    refine hyb.not_ge (Finset.sum_nonneg fun v _ ↦ ?_)
    simp only [bound]
    split_ifs with h
    · rw [le_antisymm (not_lt.mp fun hlt ↦ h.2 (hall v hlt h.1)) (hy v), zero_mul]
    · rw [mul_zero]
  exact hstr (hcancel.weighted w hw hvalid hsum (by simp only [w, hv, ite_true]; exact hyv))

private theorem representable_of_signCancellation_fin [IsQualitativeProbability r]
    (h : SignCancellation r) : Representable r :=
  (Matrix.farkas (coeffs r) (bound r)).elim (fun ⟨_, hx⟩ ↦ representable_of_feasible r hx)
    fun ⟨_, hy, hyA, hyb⟩ ↦ absurd h (not_signCancellation_of_certificate r hy hyA hyb)

end Farkas

/-! ### Scott's theorem -/

/-- **Scott's theorem**, hard direction. A qualitative probability on a finite carrier
    satisfying sign-vector cancellation is represented by a probability measure. -/
theorem SignCancellation.representable [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {r : Set W → Set W → Prop} [IsQualitativeProbability r] (h : SignCancellation r) :
    Representable r := by
  classical
  exact (representable_of_signCancellation_fin _ (h.transport (Fintype.equivFin W))).of_preimage
    (Fintype.equivFin W).injective

/-- **Scott's theorem** for a qualitative probability. -/
theorem representable_iff_cancellation [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    (r : Set W → Set W → Prop) [IsQualitativeProbability r] :
    Representable r ↔ Cancellation r :=
  ⟨Representable.cancellation, fun h ↦ h.signCancellation.representable⟩

/-- **Scott's theorem**. A relation on the subsets of a finite set is induced by a probability
    measure iff the whole space is strictly more likely than `∅`, every set is at least as likely
    as `∅`, any two sets compare, and cancellation holds ([scott-1964] Theorem 4.1). -/
theorem representable_iff [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {r : Set W → Set W → Prop} :
    Representable r ↔ IsNontrivial r ∧ (∀ A, r A ∅) ∧ Std.Total r ∧ Cancellation r := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hnn, _, h⟩ ↦ ?_⟩
  · have hc := h.cancellation
    obtain ⟨μ, _, rfl⟩ := h
    exact ⟨inferInstance, rel_empty, inferInstance, hc⟩
  · have := h.isQualitativeProbability hnn
    exact h.signCancellation.representable

/-- A null atom and representability one cardinality down yield sign-vector cancellation: the
    other atoms embed by `Fin.succAbove`, and the null atom drops out (`Representable.of_image`). -/
theorem signCancellation_of_null_atom {n : ℕ} (r : Set (Fin (n + 2)) → Set (Fin (n + 2)) → Prop)
    [IsQualitativeProbability r] {j : Fin (n + 2)} (hj : r ∅ {j})
    (sub : ∀ r' : Set (Fin (n + 1)) → Set (Fin (n + 1)) → Prop,
      IsQualitativeProbability r' → Representable r') :
    SignCancellation r := by
  have hnt : ¬r ∅ (Set.range j.succAbove) := fun h ↦ by
    obtain ⟨k, hk⟩ := exists_not_rel_empty_singleton r
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq fun hkj : k = j ↦ hk (hkj ▸ hj)
    exact hk (trans_of r h (mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_range_self i))))
  refine (Representable.of_image ?_
    (sub _ (isQualitativeProbability_image Fin.succAbove_right_injective hnt))).cancellation
    |>.signCancellation
  rwa [Fin.range_succAbove, compl_compl]

end ComparativeProbability
