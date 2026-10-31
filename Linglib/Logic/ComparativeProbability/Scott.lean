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

Scott's theorem says that a relation on the subsets of a finite `W` is
[induced by a probability measure](##ComparativeProbability.representable_iff) iff `W` is strictly
more likely than `∅`, every set is at least as likely as `∅`, any two sets compare, and finite
cancellation holds. A comparison `A ≿ B` of disjoint sets is a **sign vector** `v : W → SignType`
with positive support `A` and negative support `B`, and in this form cancellation says that when
valid comparisons sum to zero as integer vectors, each holds reversed. It compares only disjoint
sets, and agrees with finite cancellation
[on a qualitative probability](##ComparativeProbability.cancellation_iff_finiteCancellation).

## Main declarations

* `comparisonSum`: the sum of a multiset of comparisons as integer vectors; a comparison's two
  sides are the supports `posSupport` and `negSupport` of `Core/Basic/Sign.lean`.
* `Cancellation`: Scott's condition in sign-vector form.
* `FiniteCancellation.cancellation`, `Cancellation.finiteCancellation`,
  `cancellation_iff_finiteCancellation`: the two forms agree on a qualitative probability.
* `Cancellation.transport`: cancellation along an equivalence of carriers.
* `cancellation_implies_representable`: the Farkas direction.
* `representable_iff`: Scott's theorem.
* `representable_iff_cancellation`, `representable_iff_finiteCancellation`: its two forms for a
  qualitative probability.
* `cancellation_of_null_atom`: a null atom reduces cancellation to representability one atom
  down.

## Implementation notes

The hard direction is linear-programming duality over `ℚ` (`Matrix.farkas`), on `Fin n` and
transported along `Fintype.equivFin`. The weight vectors representing the order form a
polyhedron, whose normalized points weight the Dirac measures of a representing measure; it is
nonempty unless a Farkas certificate exists, a nonnegative weighting of valid comparisons that
sums to zero yet weights a strict one. Clearing denominators turns the certificate into a
multiset violating `Cancellation`.

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

/-- **Scott's cancellation condition** says that when a multiset of valid comparisons sums to
    zero as integer vectors, every comparison in it also holds reversed. -/
def Cancellation (ge : Set W → Set W → Prop) : Prop :=
  ∀ M : Multiset (W → SignType), (∀ v ∈ M, ge (posSupport v) (negSupport v)) →
    comparisonSum M = 0 → ∀ v ∈ M, ge (negSupport v) (posSupport v)

/-- Cancellation pulls back along an equivalence of carriers. -/
theorem Cancellation.transport {α : Type*} (e : W ≃ α) {r : Set W → Set W → Prop}
    (h : Cancellation r) : Cancellation (Set.preimage e ⁻¹'o r) := by
  intro M hvalid hsum v hv
  refine h (M.map (· ∘ e)) ?_ ?_ (v ∘ e) (Multiset.mem_map_of_mem _ hv)
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    exact hvalid u hu
  · funext w
    simpa [comparisonSum, Multiset.map_map, Function.comp_def] using congrFun hsum (e w)

section Bridge

open scoped Classical

private theorem comparisonSum_eq_seqCount (L : List (W → SignType)) (i : W) :
    comparisonSum (L : Multiset (W → SignType)) i =
      seqCount i (L.map posSupport) - seqCount i (L.map negSupport) := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [← Multiset.cons_coe, List.map_cons, seqCount_cons, comparisonSum_cons, ih,
      mem_posSupport, mem_negSupport, signCast_eq_ite (v i)]
    push_cast
    split_ifs <;> ring

/-- The balanced-sequence form implies the sign-vector form. -/
theorem FiniteCancellation.cancellation {ge : Set W → Set W → Prop}
    (h : FiniteCancellation ge) : Cancellation ge := by
  intro M hge hsum v hv
  set L := (M.erase v).toList
  refine h (L.map fun w ↦ (posSupport w, negSupport w)) (posSupport v) (negSupport v)
    (fun i ↦ ?_) fun p hp ↦ ?_
  · have hM : ((v :: L : List (W → SignType)) : Multiset (W → SignType)) = M := by
      rw [← Multiset.cons_coe, Multiset.coe_toList, Multiset.cons_erase hv]
    have := congrFun hsum i
    rw [← hM, comparisonSum_eq_seqCount, List.map_cons, List.map_cons, Pi.zero_apply] at this
    simp only [List.map_map]
    show seqCount i (posSupport v :: L.map posSupport) =
      seqCount i (negSupport v :: L.map negSupport)
    omega
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
    exact hge w (Multiset.mem_of_mem_erase (Multiset.mem_toList.1 hw))

private theorem seqCount_sub_seqCount (P : List (Set W × Set W)) (i : W) :
    (seqCount i (P.map Prod.fst) : ℤ) - seqCount i (P.map Prod.snd) =
      (P.map fun p ↦ ((if i ∈ p.1 then 1 else 0) - (if i ∈ p.2 then 1 else 0) : ℤ)).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, seqCount_cons, List.sum_cons]
    push_cast
    rw [← ih]
    ring

/-- `normalize p` is the sign vector of a comparison of sets, `+1` on `A \ B` and `-1` on
    `B \ A`. -/
private noncomputable def normalize (p : Set W × Set W) (i : W) : SignType :=
  SignType.sign ((if i ∈ p.1 then 1 else 0) - (if i ∈ p.2 then 1 else 0) : ℤ)

private theorem coe_normalize (p : Set W × Set W) (i : W) :
    (normalize p i : ℤ) = (if i ∈ p.1 then 1 else 0) - (if i ∈ p.2 then 1 else 0) := by
  unfold normalize; split_ifs <;> simp

private theorem posSupport_normalize (p : Set W × Set W) :
    posSupport (normalize p) = p.1 \ p.2 := by
  ext i
  simp only [mem_posSupport, normalize, sign_eq_one_iff, Set.mem_sdiff]
  split_ifs <;> simp_all

private theorem negSupport_normalize (p : Set W × Set W) :
    negSupport (normalize p) = p.2 \ p.1 := by
  ext i
  simp only [mem_negSupport, normalize, sign_eq_neg_one_iff, Set.mem_sdiff]
  split_ifs <;> simp_all

/-- For a qualitative probability the sign-vector form implies the balanced-sequence form, by
    normalizing every comparison with additivity. -/
theorem Cancellation.finiteCancellation (r : Set W → Set W → Prop) [IsQualitativeProbability r]
    (h : Cancellation r) : FiniteCancellation r := by
  intro prem X Y hbal hprem
  by_contra hYX
  have hXY : r X Y := (total_of r Y X).resolve_left hYX
  have key := h (((X, Y) :: prem).map normalize : List (W → SignType)) ?_ ?_ (normalize (X, Y))
    (Multiset.mem_coe.2 (List.mem_cons_self ..))
  · rw [negSupport_normalize, posSupport_normalize] at key
    exact hYX ((qadd (r := r) Y X).mpr key)
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.1 hv)
    rw [posSupport_normalize, negSupport_normalize]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (qadd (r := r) X Y).mp hXY
    · exact (qadd (r := r) p.1 p.2).mp (hprem p hp)
  · funext i
    have key := seqCount_sub_seqCount ((X, Y) :: prem) i
    simp only [List.map_cons, hbal i, sub_self, List.sum_cons] at key
    simp only [comparisonSum_coe, List.map_map, List.map_cons, Function.comp_def, coe_normalize,
      Pi.zero_apply, List.sum_cons]
    omega

/-- The two forms of Scott's condition agree on a qualitative probability. -/
theorem cancellation_iff_finiteCancellation (r : Set W → Set W → Prop)
    [IsQualitativeProbability r] : Cancellation r ↔ FiniteCancellation r :=
  ⟨Cancellation.finiteCancellation r, FiniteCancellation.cancellation⟩

end Bridge

/-! ### Weighted cancellation

The Farkas certificate is a rational weighting of comparisons; `Cancellation`
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

private theorem Cancellation.weighted {ge : Set (Fin n) → Set (Fin n) → Prop}
    (h : Cancellation ge) (w : (Fin n → SignType) → ℚ) (hw : ∀ v, 0 ≤ w v)
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

private theorem not_cancellation_of_certificate {y : (Fin n → SignType) → ℚ} (hy : 0 ≤ y)
    (hyA : y ᵥ* coeffs r = 0) (hyb : y ⬝ᵥ bound r < 0) : ¬Cancellation r := by
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

private theorem representable_of_cancellation_fin [IsQualitativeProbability r]
    (h : Cancellation r) : Representable r :=
  (Matrix.farkas (coeffs r) (bound r)).elim (fun ⟨_, hx⟩ ↦ representable_of_feasible r hx)
    fun ⟨_, hy, hyA, hyb⟩ ↦ absurd h (not_cancellation_of_certificate r hy hyA hyb)

end Farkas

/-! ### Scott's theorem -/

section Scott

variable [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
  (r : Set W → Set W → Prop) [IsQualitativeProbability r]

/-- **Scott's theorem**, hard direction. A qualitative probability on a finite carrier
    satisfying cancellation is represented by a probability measure. -/
theorem cancellation_implies_representable (h : Cancellation r) : Representable r := by
  classical
  exact (representable_of_cancellation_fin _ (h.transport (Fintype.equivFin W))).of_preimage
    (Fintype.equivFin W).injective

/-- **Scott's theorem** in sign-vector form, for a qualitative probability. -/
theorem representable_iff_cancellation : Representable r ↔ Cancellation r :=
  ⟨fun h ↦ h.finiteCancellation.cancellation, cancellation_implies_representable r⟩

/-- **Scott's theorem** in balanced-sequence form, for a qualitative probability. -/
theorem representable_iff_finiteCancellation : Representable r ↔ FiniteCancellation r :=
  (representable_iff_cancellation r).trans (cancellation_iff_finiteCancellation r)

end Scott

/-- **Scott's theorem**. A relation on the subsets of a finite set is induced by a probability
    measure iff the whole space is strictly more likely than `∅`, every set is at least as likely
    as `∅`, any two sets compare, and finite cancellation holds ([scott-1964] Theorem 4.1). -/
theorem representable_iff [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {r : Set W → Set W → Prop} :
    Representable r ↔ IsNontrivial r ∧ (∀ A, r A ∅) ∧ Std.Total r ∧ FiniteCancellation r := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hnn, _, h⟩ ↦ ?_⟩
  · have hfc := h.finiteCancellation
    obtain ⟨μ, _, rfl⟩ := h
    exact ⟨inferInstance, rel_empty, inferInstance, hfc⟩
  · have := h.isQualitativeProbability hnn
    exact cancellation_implies_representable r h.cancellation

/-- A null atom and representability one cardinality down yield cancellation: the other atoms
    embed by `Fin.succAbove`, and the null atom drops out (`Representable.of_image`). -/
theorem cancellation_of_null_atom {n : ℕ} (r : Set (Fin (n + 2)) → Set (Fin (n + 2)) → Prop)
    [IsQualitativeProbability r] {j : Fin (n + 2)} (hj : r ∅ {j})
    (sub : ∀ r' : Set (Fin (n + 1)) → Set (Fin (n + 1)) → Prop,
      IsQualitativeProbability r' → Representable r') :
    Cancellation r := by
  have hnt : ¬r ∅ (Set.range j.succAbove) := fun h ↦ by
    obtain ⟨k, hk⟩ := exists_not_rel_empty_singleton r
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq fun hkj : k = j ↦ hk (hkj ▸ hj)
    exact hk (trans_of r h (mono _ _ (Set.singleton_subset_iff.mpr (Set.mem_range_self i))))
  refine (representable_iff_cancellation r).mp (Representable.of_image ?_
    (sub _ (isQualitativeProbability_image Fin.succAbove_right_injective hnt)))
  rwa [Fin.range_succAbove, compl_compl]

end ComparativeProbability
