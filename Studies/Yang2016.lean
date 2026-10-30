module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.Int
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity
public import Linglib.Data.Experiments.Yang2016

/-!
# Yang (2016): The Price of Linguistic Productivity

This file formalizes the Tolerance Principle of [yang-2016]. Items ranked by frequency are searched
serially, so under [the Zipfian law](##isProbabilityMeasure_zipf) reaching one of `N` items takes
[`N / H_N` steps on average](##listTime_eq). A rule lists its `e` exceptions before itself, [at a
cost](##ruleTime_eq), and is productive when it beats the list. Yang's closed form, productive if
and only if `e ≤ N / ln N`, holds of the cost from right to left [when some item follows the
rule](##productive_of_tolerates), and from left to right only approximately: [81 exceptions among
500 items](##not_forall_productive_imp_tolerates) are productive though not tolerated. The German
feminine *-(e)n* plural is [tolerated and productive](##tolerates_productive_femininePlural).

## Implementation notes

* `Productive` is the book's comparison of costs, which is strict, so a rule all of whose items
  are exceptions is unproductive (`not_productive_self`). The book's introduction states the
  principle in one direction, that the exceptions of a productive rule fall under the threshold;
  the closed form is the biconditional, derived by approximating `H_N` by `ln N`.
* `productive_of_tolerates` bounds the rule's cost by `3eN / (3N + 2e)`, which lies under the
  list's since `H_N < ln N + 2 / 3` from `N = 6` on and tolerance puts `ln N` under `N / e`. The
  bound needs `N (3 - H_e) ≤ 2e (H_e - 1)`, which holds for eleven or more exceptions; for fewer,
  the list's cost, which grows with `N`, exceeds `e` beyond a point where the bound still holds,
  except at nine rules over at most twelve items, compared in exact arithmetic, and two that are
  not tolerated. The rule over two items both of which are exceptions is tolerated and costs as
  much as the list (`not_forall_tolerates_imp_productive`), hence the hypothesis that some item
  follows the rule.
* Yang's simplification of the rule's cost, that a random subset of a Zipfian list is again
  Zipfian, is what the Zipfian exceptions of `ruleLaw` encode: the search stops at an exception
  with probability `e / N`, at the rank the Zipfian law on the `e` exceptions gives it, and at the
  rule otherwise. For `e > N` the weight `1 - e / N` is truncated at zero, so `ruleTime_eq`
  assumes `e ≤ N`, as does every statement about the cost.
* The threshold is stated with the natural logarithm as in the book. Mathlib's convention that
  division by zero is zero makes the threshold vanish at `N ≤ 1` (`threshold_eq_zero_of_le_one`).
* The counts of the German feminine plurals are the book's (`Data.Experiments.Yang2016`); the
  exceptions are the items whose plural does not take *-(e)n*.

## Errata

* The table of thresholds for rules of varying sizes prints `θ_100 = 23` (23.0%), though
  `100 / ln 100 < 22` (`threshold_100_lt`), against its other rows, which are `N / ln N`
  rounded. Twenty-three is the count the cost itself allows at `N = 100`: a rule over 100 items
  is productive with 23 exceptions and not with 24 (`productive_100_23`,
  `not_productive_100_24`).

## References

* [yang-2016]
* [yang-2005]
-/

@[expose] public section

namespace Yang2016

open Finset MeasureTheory

/-! ### The tolerance threshold -/

/-- (11): the tolerance threshold for a rule applicable to `n` items. -/
noncomputable def threshold (n : ℕ) : ℝ := (n : ℝ) / Real.log n

/-- (3), pp. 8–9: a rule with `n` items in scope and `e` exceptions is tolerated when the
exceptions fit under the threshold, as the Tolerance Principle requires of a productive rule. -/
def Tolerates (n e : ℕ) : Prop := (e : ℝ) ≤ threshold n

theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n :=
  div_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n)

theorem threshold_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : threshold n = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;> simp [threshold]

theorem tolerates_zero (n : ℕ) : Tolerates n 0 := by
  simpa [Tolerates] using threshold_nonneg n

/-! ### Serial access under Zipf -/

private theorem harmonic_nonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact_mod_cast (harmonic_pos hn.ne').le

private theorem harmonic_eq_sum (n : ℕ) : (harmonic n : ℝ) = ∑ i : Fin n, ((i : ℝ) + 1)⁻¹ := by
  have h : (harmonic n : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by simp [harmonic]
  exact h.trans (Fin.sum_univ_eq_sum_range (fun i ↦ ((i : ℝ) + 1)⁻¹) n).symm

/-- The Zipfian law on a frequency-ranked list of `n` items: the item of rank `i + 1` has
probability `1 / ((i + 1) H_n)`. -/
noncomputable def zipf (n : ℕ) : Measure (Fin n) :=
  ∑ i : Fin n, (((i : ℝ) + 1) * harmonic n)⁻¹.toNNReal • Measure.dirac i

instance (n : ℕ) : IsFiniteMeasure (zipf n) := by
  unfold zipf
  infer_instance

theorem integral_zipf {n : ℕ} (f : Fin n → ℝ) :
    ∫ i, f i ∂zipf n = ∑ i : Fin n, (((i : ℝ) + 1) * harmonic n)⁻¹ * f i := by
  rw [zipf, integral_finsetSum_measure fun i _ ↦ .of_finite]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (inv_nonneg.2 (mul_nonneg (by positivity) (harmonic_nonneg n)))]

theorem isProbabilityMeasure_zipf {n : ℕ} (hn : n ≠ 0) : IsProbabilityMeasure (zipf n) := by
  have h := integral_zipf (n := n) fun _ ↦ 1
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [isProbabilityMeasure_iff_real, h]
  simp only [mul_one, mul_inv, ← sum_mul, ← harmonic_eq_sum]
  exact mul_inv_cancel₀ (by exact_mod_cast (harmonic_pos hn).ne')

/-- The expected time to reach an item of a frequency-ranked list of `n` items searched serially,
the item of rank `i + 1` reached in `i + 1` steps. -/
noncomputable def listTime (n : ℕ) : ℝ := ∫ i : Fin n, ((i : ℝ) + 1) ∂zipf n

private theorem one_le_harmonic_succ : ∀ n : ℕ, 1 ≤ harmonic (n + 1)
  | 0 => by simp [harmonic_succ]
  | n + 1 => by
    rw [harmonic_succ]
    have := one_le_harmonic_succ n
    have : (0 : ℚ) ≤ (↑(n + 1 + 1) : ℚ)⁻¹ := by positivity
    linarith

theorem listTime_eq (n : ℕ) : listTime n = n / harmonic n := by
  have h : ∀ i : Fin n, (((i : ℝ) + 1) * harmonic n)⁻¹ * ((i : ℝ) + 1) = (harmonic n : ℝ)⁻¹ :=
    fun i ↦ by rw [mul_inv, mul_right_comm, inv_mul_cancel₀ (by positivity), one_mul]
  rw [listTime, integral_zipf]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

theorem listTime_le_self (n : ℕ) : listTime n ≤ n := by
  rw [listTime_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h1 : (1 : ℝ) ≤ harmonic (k + 1) := by exact_mod_cast one_le_harmonic_succ k
    exact div_le_self (Nat.cast_nonneg _) h1

/-- The law of the entry at which the search of a rule with `m` exceptions among `n` items stops:
with probability `m / n` an exception, Zipfian among the exceptions, and otherwise the rule
itself, `Fin.last m`, reached after all `m` exceptions have been rejected. -/
noncomputable def ruleLaw (n m : ℕ) : Measure (Fin (m + 1)) :=
  (m / n : ℝ).toNNReal • (zipf m).map Fin.castSucc +
    (1 - m / n : ℝ).toNNReal • Measure.dirac (Fin.last m)

instance (n m : ℕ) : IsFiniteMeasure (ruleLaw n m) := by
  unfold ruleLaw
  infer_instance

/-- The steps of a search that stops at an entry: `i + 1` at the exception of rank `i + 1`, and
`m` at the rule. -/
def ruleSteps (m : ℕ) (j : Fin (m + 1)) : ℝ :=
  Fin.lastCases (motive := fun _ ↦ ℝ) m (fun i ↦ (i : ℝ) + 1) j

/-- The expected access time of a rule with `m` exceptions among `n` items. -/
noncomputable def ruleTime (n m : ℕ) : ℝ := ∫ j, ruleSteps m j ∂ruleLaw n m

private theorem div_le_one_of_le {n m : ℕ} (hmn : m ≤ n) : (m / n : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hmn

theorem isProbabilityMeasure_ruleLaw {n m : ℕ} (hn : n ≠ 0) (hmn : m ≤ n) :
    IsProbabilityMeasure (ruleLaw n m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [ruleLaw, isProbabilityMeasure_iff]
  · have := isProbabilityMeasure_zipf hm.ne'
    rw [isProbabilityMeasure_iff_real, ruleLaw, measureReal_add_apply,
      measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply, probReal_univ, probReal_univ,
      Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (sub_nonneg.2 (div_le_one_of_le hmn))]
    ring

theorem ruleTime_eq {n m : ℕ} (hmn : m ≤ n) :
    ruleTime n m = m / n * listTime m + (1 - m / n) * m := by
  rw [ruleTime, ruleLaw, integral_add_measure .of_finite .of_finite, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure,
    integral_map Measurable.of_discrete.aemeasurable AEStronglyMeasurable.of_discrete,
    integral_dirac, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul,
    Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (sub_nonneg.2 (div_le_one_of_le hmn)), listTime]
  simp [ruleSteps]

/-- (10): a rule is productive when it costs less than listing everything, and otherwise
unproductive. -/
def Productive (n m : ℕ) : Prop := ruleTime n m < listTime n

theorem ruleTime_self {n : ℕ} (hn : n ≠ 0) : ruleTime n n = listTime n := by
  rw [ruleTime_eq le_rfl, div_self (by exact_mod_cast hn)]
  ring

theorem not_productive_self (n : ℕ) : ¬ Productive n n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Productive, ruleTime_eq le_rfl, listTime_eq]
  · exact (ruleTime_self hn).not_lt

theorem ruleTime_le {n m : ℕ} (hmn : m ≤ n) : ruleTime n m ≤ m := by
  rw [ruleTime_eq hmn]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : m = 0 := by omega
    subst this; simp
  · have hx : (0 : ℝ) ≤ m / n := by positivity
    have hx1 : (m / n : ℝ) ≤ 1 := div_le_one_of_le hmn
    have := listTime_le_self m
    nlinarith

theorem productive_of_lt_listTime {n m : ℕ} (hmn : m ≤ n) (h : (m : ℝ) < listTime n) :
    Productive n m :=
  (ruleTime_le hmn).trans_lt h

/-! ### Tolerated rules are productive -/

private theorem harmonic_mono : Monotone harmonic :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [harmonic_succ]
    exact le_add_of_nonneg_right (by positivity)

-- from `n = 6` on, the harmonic number exceeds the logarithm by less than `2 / 3`
private theorem harmonic_lt_log_add {n : ℕ} (hn : 6 ≤ n) :
    (harmonic n : ℝ) < Real.log n + 2 / 3 := by
  have h := (Real.strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', show n ≠ 0 by omega, ↓reduceIte] at h
  linarith

-- a rational lower bound on the logarithm, through `γ < 2 / 3`
private theorem harmonic_pred_sub_lt_log {n : ℕ} (hn : n ≠ 0) :
    (harmonic (n - 1) : ℝ) - 2 / 3 < Real.log n := by
  have h := (Real.eulerMascheroniSeq_lt_eulerMascheroniSeq' (n - 1) 6).trans
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  rw [Real.eulerMascheroniSeq, Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel] at h
  linarith

private theorem tolerates_lt {n m : ℕ} (hn : n ≠ 0) (h : Tolerates n m) :
    (m : ℚ) * (harmonic (n - 1) - 2 / 3) < n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using Nat.pos_of_ne_zero hn
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have h' : (m : ℝ) ≤ threshold n := h
    rw [threshold_eq_zero_of_le_one (by omega)] at h'
    have : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have : (m : ℝ) * (harmonic (n - 1) - 2 / 3) < n :=
    (mul_lt_mul_of_pos_left (harmonic_pred_sub_lt_log hn) (by exact_mod_cast hm)).trans_le
      ((le_div_iff₀ hL).1 h)
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  exact this

-- the rule beats the list when `n (3 - K) ≤ 2 m (K - 1)`, `K` the exceptions' harmonic number,
-- since `H_n < L + 2 / 3` and tolerance puts `L` under `n / m`
private theorem cost_lt {n m L H K : ℝ} (hn : 0 < n) (hm : 0 < m) (hL : 0 < L)
    (hmL : m * L ≤ n) (hK : 0 < K) (hc : n * (3 - K) ≤ 2 * m * (K - 1)) (hH : 0 < H)
    (hHL : H < L + 2 / 3) : m / n * (m / K) + (1 - m / n) * m < n / H := by
  have hn' : n ≠ 0 := hn.ne'
  have hK' : K ≠ 0 := hK.ne'
  have hD : 3 * n + 2 * m ≠ 0 := by positivity
  have h1 : m / n * (m / K) + (1 - m / n) * m ≤ 3 * m * n / (3 * n + 2 * m) := by
    have e : 3 * m * n / (3 * n + 2 * m) - (m / n * (m / K) + (1 - m / n) * m) =
        m ^ 2 * (2 * m * (K - 1) - n * (3 - K)) / (n * K * (3 * n + 2 * m)) := by
      field_simp
      ring
    have : 0 ≤ m ^ 2 * (2 * m * (K - 1) - n * (3 - K)) / (n * K * (3 * n + 2 * m)) :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    linarith
  have h2 : 3 * m * n / (3 * n + 2 * m) ≤ n / (L + 2 / 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hmL (by positivity : (0 : ℝ) ≤ 3 * n)]
  have h3 : n / (L + 2 / 3) < n / H := div_lt_div_of_pos_left hn hH hHL
  linarith

private theorem productive_of_harmonic {n m : ℕ} (hn : 6 ≤ n) (hm : 0 < m) (hmn : m ≤ n)
    (h : Tolerates n m) (hc : (n : ℚ) * (3 - harmonic m) ≤ 2 * m * (harmonic m - 1)) :
    Productive n m := by
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hc' := (Rat.cast_le (K := ℝ)).2 hc
  push_cast at hc'
  unfold Productive
  rw [ruleTime_eq hmn, listTime_eq, listTime_eq]
  exact cost_lt (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hm) hL
    ((le_div_iff₀ hL).1 h) (by exact_mod_cast harmonic_pos hm.ne') hc'
    (by exact_mod_cast harmonic_pos (by omega : n ≠ 0)) (harmonic_lt_log_add hn)

private theorem listTime_mono : Monotone listTime := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [listTime_eq, listTime_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (1 : ℝ) ≤ harmonic n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact_mod_cast one_le_harmonic_succ k
  have hs : (harmonic (n + 1) : ℝ) = harmonic n + 1 / (n + 1) := by
    rw [harmonic_succ]
    push_cast
    ring
  have hp : (0 : ℝ) < 1 / (n + 1) := by positivity
  rw [hs, div_le_div_iff₀ (by linarith) (by linarith)]
  have e : (n : ℝ) * (harmonic n + 1 / (n + 1)) = n * harmonic n + n / (n + 1) := by ring
  have hle : (n : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  rw [e]
  push_cast
  linarith

-- from `k` items on, the list costs more than `m` steps
private theorem lt_listTime_of_le {n m k : ℕ} (hk : (m : ℚ) < k / harmonic k) (hkn : k ≤ n) :
    (m : ℝ) < listTime n := by
  refine lt_of_lt_of_le ?_ (listTime_mono hkn)
  have h := (Rat.cast_lt (K := ℝ)).2 hk
  push_cast at h
  rw [listTime_eq]
  exact h

private theorem cond_mono {n k m : ℕ} (hnk : n ≤ k) (hH : harmonic m ≤ 3)
    (hc : (k : ℚ) * (3 - harmonic m) ≤ 2 * m * (harmonic m - 1)) :
    (n : ℚ) * (3 - harmonic m) ≤ 2 * m * (harmonic m - 1) :=
  (mul_le_mul_of_nonneg_right (by exact_mod_cast hnk) (by linarith)).trans hc

-- a rule with `m` exceptions is productive over `n ≥ k` items by the list's cost, and below `k`
-- by the bound of `cost_lt`, once both hold at `k`
private theorem productive_of_cover {n m k : ℕ} (hn : 6 ≤ n) (hm : 0 < m) (hmn : m < n)
    (h : Tolerates n m) (hk : (m : ℚ) < k / harmonic k) (hH : harmonic m ≤ 3)
    (hc : ((k - 1 : ℕ) : ℚ) * (3 - harmonic m) ≤ 2 * m * (harmonic m - 1)) :
    Productive n m := by
  rcases le_or_gt k n with hkn | hkn
  · exact productive_of_lt_listTime hmn.le (lt_listTime_of_le hk hkn)
  · exact productive_of_harmonic hn hm hmn.le h (cond_mono (by omega) hH hc)

-- the comparison of `Productive` in exact rational arithmetic
private theorem productive_iff {n m : ℕ} (hmn : m ≤ n) : Productive n m ↔
    (m : ℚ) / n * (m / harmonic m) + (1 - m / n) * m < n / harmonic n := by
  rw [Productive, ruleTime_eq hmn, listTime_eq, listTime_eq, ← Rat.cast_lt (K := ℝ)]
  push_cast
  rfl

private theorem not_tolerates_4_3 : ¬ Tolerates 4 3 := by
  unfold Tolerates threshold
  have h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4, not_le, div_lt_iff₀ (by linarith [Real.log_two_gt_d9])]
  push_cast
  linarith [Real.log_two_gt_d9]

/-- The sufficient half of the closed form, under the cost of rule access: a rule that some item
follows and whose exceptions fall under the threshold is productive. -/
theorem productive_of_tolerates {n m : ℕ} (hmn : m < n) (h : Tolerates n m) :
    Productive n m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact productive_of_lt_listTime hmn.le (lt_listTime_of_le (k := 1) (by decide +kernel) hmn)
  rcases le_or_gt 11 m with hm11 | hm11
  · refine productive_of_harmonic (by omega) hm hmn.le h ?_
    have h3 : (3 : ℚ) ≤ harmonic m := (by decide +kernel : (3 : ℚ) ≤ harmonic 11).trans
      (harmonic_mono hm11)
    have : (n : ℚ) * (3 - harmonic m) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have : 0 ≤ 2 * (m : ℚ) * (harmonic m - 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  interval_cases m
  · exact productive_of_lt_listTime hmn.le (lt_listTime_of_le (k := 2) (by decide +kernel) hmn)
  · rcases le_or_gt 5 n with hn | hn
    · exact productive_of_lt_listTime hmn.le (lt_listTime_of_le (k := 5) (by decide +kernel) hn)
    interval_cases n <;> exact (productive_iff (by omega)).2 (by decide +kernel)
  · rcases le_or_gt 9 n with hn | hn
    · exact productive_of_lt_listTime hmn.le (lt_listTime_of_le (k := 9) (by decide +kernel) hn)
    interval_cases n
    · exact absurd h not_tolerates_4_3
    all_goals exact (productive_iff (by omega)).2 (by decide +kernel)
  · rcases le_or_gt 13 n with hn | hn
    · exact productive_of_lt_listTime hmn.le (lt_listTime_of_le (k := 13) (by decide +kernel) hn)
    rcases le_or_gt 10 n with hn' | hn'
    · interval_cases n <;> exact (productive_iff (by omega)).2 (by decide +kernel)
    rcases eq_or_lt_of_le (show 5 ≤ n by omega) with rfl | hn5
    · exact absurd (tolerates_lt (by norm_num) h) (by decide +kernel)
    · exact productive_of_harmonic (by omega) (by norm_num) (by omega) h
        (cond_mono (k := 9) (by omega) (by decide +kernel) (by decide +kernel))
  · exact productive_of_cover (k := 18) (by omega) (by norm_num) hmn h (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact productive_of_cover (k := 23) (by omega) (by norm_num) hmn h (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact productive_of_cover (k := 28) (by omega) (by norm_num) hmn h (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact productive_of_cover (k := 33) (by omega) (by norm_num) hmn h (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact productive_of_cover (k := 39) (by omega) (by norm_num) hmn h (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact productive_of_cover (k := 44) (by omega) (by norm_num) hmn h (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem tolerates_two_two : Tolerates 2 2 := by
  unfold Tolerates threshold
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  push_cast
  linarith [Real.log_two_lt_d9]

-- some item must follow the rule: over two items that are both exceptions, the rule is tolerated
-- and costs as much as the list
theorem not_forall_tolerates_imp_productive : ¬ ∀ n m, Tolerates n m → Productive n m :=
  fun h ↦ not_productive_self 2 (h 2 2 tolerates_two_two)

/-! ### Bounds on the logarithm and the harmonic numbers -/

private theorem log_lt_of_le_pow {n k : ℕ} (hk : k ≠ 0) (h0 : 0 < n)
    (h : (n : ℝ) ≤ 2.7182818283 ^ k) : Real.log n < k := by
  rw [Real.log_lt_iff_lt_exp (by exact_mod_cast h0), show (k : ℝ) = k * 1 by ring,
    Real.exp_nat_mul]
  exact h.trans_lt (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) hk)

private theorem tolerates_of_log_lt {n e : ℕ} {b : ℝ} (hn : 2 ≤ n) (hb : Real.log n < b)
    (h : (e : ℝ) * b ≤ n) : Tolerates n e := by
  unfold Tolerates threshold
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [le_div_iff₀ hl]
  nlinarith [Nat.cast_nonneg (α := ℝ) e]

private theorem log_500_lt : Real.log 500 < 25 / 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h6 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 :=
    pow_le_pow_left₀ (by norm_num) h1.le 6
  have h6' : (403 : ℝ) ≤ Real.exp 1 ^ 6 := le_trans (by norm_num) h6
  have hq : (5 / 4 : ℝ) ≤ Real.exp (1 / 4) := by
    have := Real.add_one_le_exp (1 / 4 : ℝ); linarith
  have heq : Real.exp (25 / 4) = Real.exp 1 ^ 6 * Real.exp (1 / 4) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [heq]
  nlinarith [mul_le_mul h6' hq (by norm_num) (by linarith)]

private theorem log_500_gt : 500 / 81 < Real.log 500 := by
  have h : Real.log 500 = Real.log ((2 : ℝ) ^ 9 * (500 / 512)) := by norm_num
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h
  have h3 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 500 / 512 by norm_num)
  have h2 := Real.log_two_gt_d9
  push_cast at h
  norm_num at h h3
  linarith

private theorem harmonic_500_lt : (harmonic 500 : ℝ) < 83 / 12 := by
  have h := (Real.strictAnti_eulerMascheroniSeq' (show 6 < 500 by norm_num)).trans
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', show (500 : ℕ) ≠ 0 by norm_num, ↓reduceIte,
    Nat.cast_ofNat] at h
  linarith [log_500_lt]

private theorem log_100_bounds : 4604 / 1000 < Real.log 100 ∧ Real.log 100 < 46056 / 10000 := by
  have h : Real.log (100 ^ 3) = Real.log ((2 : ℝ) ^ 20 * (1000000 / 1048576)) := by norm_num
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h
  have l1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1000000 / 1048576 by norm_num)
  have l2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1000000 / 1048576 by norm_num)
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  push_cast at h
  norm_num at h l1 l2
  constructor <;> linarith

private theorem harmonic_100_bounds :
    51 / 10 < (harmonic 100 : ℝ) ∧ (harmonic 100 : ℝ) < 52138 / 10000 := by
  have hl := Real.one_half_lt_eulerMascheroniConstant.trans
    (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 100)
  have hu := Real.strictAnti_eulerMascheroniSeq' (show 16 < 100 by norm_num)
  simp only [Real.eulerMascheroniSeq', show (100 : ℕ) ≠ 0 by norm_num,
    show (16 : ℕ) ≠ 0 by norm_num, ↓reduceIte, Nat.cast_ofNat] at hl hu
  have h16 : harmonic 16 = 2436559 / 720720 := by norm_num [harmonic, Finset.sum_range_succ]
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  rw [h16, hlog16] at hu
  push_cast at hu
  have h2 := Real.log_two_gt_d9
  obtain ⟨b1, b2⟩ := log_100_bounds
  constructor <;> linarith

/-! ### The threshold as an approximation -/

private theorem four_le_harmonic {n : ℕ} (hn : 80 ≤ n) : (4 : ℝ) ≤ harmonic n := by
  refine le_trans ?_ (log_add_one_le_harmonic n)
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
  have hn' : (80 : ℝ) ≤ n := by exact_mod_cast hn
  rw [he4]
  push_cast
  linarith [show (2.7182818286 : ℝ) ^ 4 < 80 by norm_num]

-- a rule over 500 items is productive when its cost, with `harmonic m` bounded below by 4, is
-- under the list's
private theorem productive_500 {m : ℕ} (hm : 80 ≤ m) (hm' : m ≤ 500)
    (h : (m / 500 : ℝ) * (m / 4) + (1 - m / 500) * m < 6000 / 83) : Productive 500 m := by
  unfold Productive
  rw [ruleTime_eq hm', listTime_eq, listTime_eq]
  push_cast
  have hl : (m : ℝ) / harmonic m ≤ m / 4 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by norm_num) (four_le_harmonic hm)
  have hr : (6000 / 83 : ℝ) ≤ 500 / harmonic 500 := by
    have hpos : (0 : ℝ) < harmonic 500 := by exact_mod_cast harmonic_pos (by norm_num)
    rw [le_div_iff₀ hpos]
    linarith [harmonic_500_lt]
  linarith [mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ m / 500)]

theorem not_tolerates_500_81 : ¬ Tolerates 500 81 := by
  unfold Tolerates threshold
  push_cast
  rw [le_div_iff₀ (Real.log_pos (by norm_num)), not_le]
  linarith [log_500_gt]

theorem productive_500_81 : Productive 500 81 :=
  productive_500 (by norm_num) (by norm_num) (by norm_num)

/-- The closed form holds of the cost of rule access only approximately: a rule with 81
exceptions among 500 items is productive by the cost, though the threshold tolerates at most 80. -/
theorem not_forall_productive_imp_tolerates : ¬ ∀ n m, Productive n m → Tolerates n m :=
  fun h ↦ not_tolerates_500_81 (h 500 81 productive_500_81)

-- Table 3.1: `θ_500 = 80`
theorem floor_threshold_500 : ⌊threshold 500⌋₊ = 80 := by
  rw [Nat.floor_eq_iff (threshold_nonneg 500)]
  refine ⟨?_, (not_le.mp not_tolerates_500_81).trans_le (by norm_num)⟩
  unfold threshold
  push_cast
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  linarith [log_500_lt]

theorem threshold_100_lt : threshold 100 < 22 := by
  unfold threshold
  push_cast
  rw [div_lt_iff₀ (Real.log_pos (by norm_num))]
  linarith [log_100_bounds.1]

private theorem harmonic_23_eq : (harmonic 23 : ℝ) = 444316699 / 118982864 := by
  rw [show harmonic 23 = 444316699 / 118982864 by norm_num [harmonic, Finset.sum_range_succ]]
  norm_num

private theorem harmonic_24_eq : (harmonic 24 : ℝ) = 1347822955 / 356948592 := by
  rw [show harmonic 24 = 1347822955 / 356948592 by norm_num [harmonic, Finset.sum_range_succ]]
  norm_num

theorem productive_100_23 : Productive 100 23 := by
  unfold Productive
  rw [ruleTime_eq (by norm_num), listTime_eq, listTime_eq, harmonic_23_eq]
  obtain ⟨h1, h2⟩ := harmonic_100_bounds
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  linarith

theorem not_productive_100_24 : ¬ Productive 100 24 := by
  unfold Productive
  rw [ruleTime_eq (by norm_num), listTime_eq, listTime_eq, harmonic_24_eq]
  obtain ⟨h1, h2⟩ := harmonic_100_bounds
  rw [not_lt, div_le_iff₀ (by linarith)]
  push_cast
  linarith

/-! ### The German feminine plural -/

/-- The *-(e)n* plural of the German feminine nouns is tolerated and productive in both of
Yang's counts, the items whose plural takes another suffix being its exceptions. -/
theorem tolerates_productive_femininePlural (c : Corpus) :
    Tolerates (femininePlural c).items ((femininePlural c).items - (femininePlural c).enPlurals) ∧
      Productive (femininePlural c).items
        ((femininePlural c).items - (femininePlural c).enPlurals) := by
  have ht : Tolerates (femininePlural c).items
      ((femininePlural c).items - (femininePlural c).enPlurals) := by
    cases c <;> simp only [femininePlural, Nat.reduceSub]
    · exact tolerates_of_log_lt (by norm_num)
        (log_lt_of_le_pow (n := 166) (k := 6) (by norm_num) (by norm_num) (by norm_num))
        (by norm_num)
    · exact tolerates_of_log_lt (by norm_num)
        (log_lt_of_le_pow (n := 1549) (k := 8) (by norm_num) (by norm_num) (by norm_num))
        (by norm_num)
  exact ⟨ht, productive_of_tolerates (by cases c <;> decide) ht⟩

end Yang2016
