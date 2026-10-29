module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.Int
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Positivity
public import Linglib.Data.Experiments.Yang2016

/-!
# Yang (2016): The Price of Linguistic Productivity

This file formalizes the Tolerance Principle of [yang-2016]. A rule applicable to `N` items, `e`
of them exceptions, is productive when reaching an item through the rule, after its exceptions,
takes less expected time than finding it in a list of all `N` items (`Productive`). The items are
ranked by frequency and searched serially, so under a Zipfian distribution the expected time to
reach an item in a list of `N` is `N / H_N`, with `H_N` the harmonic number (`listTime`). A rule
lists its `e` exceptions before itself, so an exception is found in expected time `T(e, e)` and a
regular item after all `e` exceptions have been rejected (`ruleTime`). Yang's closed form, that a
rule is productive if and only if `e ≤ θ_N = N / ln N` (`threshold`, `tolerates`), replaces the
harmonic number by the logarithm it approximates, and holds of the cost only approximately: a rule
with 81 exceptions among 500 items is
[productive though not tolerated](##not_forall_productive_imp_tolerates), and over 100 items the
cost allows 23 exceptions but not 24 (`productive_100_23`, `not_productive_100_24`) against
`θ_100 ≈ 21.7` (`threshold_100_lt`). The other half of the closed form, that a tolerated rule
some item follows is productive, is stated against the cost
([tolerated rules](##productive_of_tolerates)); proved here is the same conclusion at the lower
bound `N / (1 + ln N)` (`productive_of_le_div_one_add_log`), since the rule's cost never exceeds
`e` (`ruleTime_le`). The *-(e)n* plural of the German feminine nouns, with 20 exceptions among 166
nouns in child-directed speech and 103 among 1,549 plurals in a newspaper corpus, is
[tolerated and productive](##tolerates_productive_femininePlural).

## Implementation notes

* `Productive` is the book's comparison of costs, which is strict, so a rule all of whose items
  are exceptions is unproductive (`not_productive_self`). The book's introduction states the
  principle in one direction, that the exceptions of a productive rule fall under the threshold;
  the closed form is the biconditional, derived by approximating `H_N` by `ln N` and dropping a
  term that vanishes for large `N`, and offered as a very good approximation of the critical
  threshold. Under the cost a rule over 500 items stays productive up to 85 exceptions by
  numerical evaluation, against `θ_500 ≈ 80.5`.
* Yang's simplification of the rule's cost, that the exceptions are themselves Zipfian, is taken
  as the definition of `ruleTime`. The threshold is stated with the natural logarithm as in the
  book. Mathlib's convention that division by zero is zero makes the threshold vanish at `N ≤ 1`.
* `productive_of_tolerates` asks that some item follow the rule. The rule over two items both of
  which are exceptions is tolerated, `θ_2 ≈ 2.9`, and costs exactly as much as the list.
* The counts of the German feminine plurals are the book's (`Data.Experiments.Yang2016`); the
  exceptions are the nouns whose plural does not take *-(e)n*.

## Errata

* The table of thresholds for rules of varying sizes prints `θ_100 = 23` (23.0%), though
  `100 / ln 100 ≈ 21.7` (`threshold_100_lt`), against its other rows, which are `N / ln N`
  rounded. Twenty-three is where the cost itself puts the threshold at `N = 100`: a rule over 100
  items is productive with 23 exceptions and not with 24 (`productive_100_23`,
  `not_productive_100_24`), and the text reads the crossover of the cost curves there as roughly
  22.

## TODO

* Prove `productive_of_tolerates`.

## References

* [yang-2016]
* [yang-2005]
-/

@[expose] public section

namespace Yang2016

open Finset

/-! ### The tolerance threshold -/

/-- (11): the tolerance threshold for a rule applicable to `n` items. -/
noncomputable def threshold (n : ℕ) : ℝ := (n : ℝ) / Real.log n

/-- (3), pp. 8–9: a rule with `n` items in scope and `e` exceptions is tolerated when the
exceptions fit under the threshold, as the Tolerance Principle requires of a productive rule. -/
def tolerates (n e : ℕ) : Prop := (e : ℝ) ≤ threshold n

theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n := by
  unfold threshold
  apply div_nonneg (Nat.cast_nonneg n)
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

theorem tolerates_zero (n : ℕ) : tolerates n 0 := by
  simpa [tolerates] using threshold_nonneg n

/-! ### Serial access under Zipf -/

/-- The expected time to reach an item in a frequency-ranked list of `n` items whose
frequencies are Zipfian: the `i`-th item has probability `1 / (i H_n)` and is reached in
`i` steps. -/
noncomputable def listTime (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (1 / ((i + 1 : ℝ) * harmonic n)) * (i + 1 : ℝ)

private theorem one_le_harmonic' : ∀ n : ℕ, 1 ≤ harmonic (n + 1)
  | 0 => by simp [harmonic_succ]
  | n + 1 => by
    rw [harmonic_succ]
    have := one_le_harmonic' n
    have : (0 : ℚ) ≤ (↑(n + 1 + 1) : ℚ)⁻¹ := by positivity
    linarith

theorem listTime_eq (n : ℕ) : listTime n = n / harmonic n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [listTime]
  · have h : (harmonic n : ℝ) ≠ 0 := by exact_mod_cast (harmonic_pos hn.ne').ne'
    unfold listTime
    have hterm : ∀ i ∈ range n,
        (1 / (((i : ℝ) + 1) * harmonic n)) * ((i : ℝ) + 1) = 1 / harmonic n := by
      intro i _
      have : ((i : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul, div_eq_mul_one_div]
    ring

theorem listTime_le_self (n : ℕ) : listTime n ≤ n := by
  rw [listTime_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h1 : (1 : ℝ) ≤ harmonic (k + 1) := by exact_mod_cast one_le_harmonic' k
    exact div_le_self (Nat.cast_nonneg _) h1

/-- The expected access time of a productive rule with `m` exceptions among `n` items: with
probability `m / n` the item is an exception, found in a list of `m`; otherwise it is
reached after the `m` exceptions have been rejected. -/
noncomputable def ruleTime (n m : ℕ) : ℝ :=
  (m / n : ℝ) * listTime m + (1 - m / n : ℝ) * m

/-- (10): a rule is productive when it costs less than listing everything, and otherwise
unproductive. -/
def Productive (n m : ℕ) : Prop := ruleTime n m < listTime n

theorem ruleTime_self (n : ℕ) (hn : 0 < n) : ruleTime n n = listTime n := by
  unfold ruleTime
  rw [div_self (by exact_mod_cast hn.ne')]
  ring

theorem not_productive_self (n : ℕ) : ¬ Productive n n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Productive, ruleTime, listTime]
  · exact (ruleTime_self n hn).not_lt

theorem ruleTime_le {n m : ℕ} (hmn : m ≤ n) : ruleTime n m ≤ m := by
  unfold ruleTime
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : m = 0 := by omega
    subst this; simp
  · have hx : (0 : ℝ) ≤ m / n := by positivity
    have hx1 : (m / n : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hmn
    have := listTime_le_self m
    nlinarith

theorem productive_of_lt_listTime {n m : ℕ} (hmn : m ≤ n) (h : (m : ℝ) < listTime n) :
    Productive n m :=
  (ruleTime_le hmn).trans_lt h

private theorem harmonic_lt_one_add_log {n : ℕ} (hn : 2 ≤ n) :
    (harmonic n : ℝ) < 1 + Real.log n := by
  have h := Real.strictAnti_eulerMascheroniSeq' (show 1 < n by omega)
  rw [Real.eulerMascheroniSeq'_one] at h
  simp only [Real.eulerMascheroniSeq', show n ≠ 0 by omega, ↓reduceIte] at h
  linarith

theorem div_one_add_log_lt_listTime {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / (1 + Real.log n) < listTime n := by
  have hn0 : 0 < n := by omega
  rw [listTime_eq]
  exact div_lt_div_of_pos_left (by exact_mod_cast hn0)
    (by exact_mod_cast harmonic_pos hn0.ne') (harmonic_lt_one_add_log hn)

theorem productive_of_le_div_one_add_log {n m : ℕ} (hn : 2 ≤ n) (hmn : m ≤ n)
    (h : (m : ℝ) ≤ n / (1 + Real.log n)) : Productive n m :=
  productive_of_lt_listTime hmn (h.trans_lt (div_one_add_log_lt_listTime hn))

theorem div_one_add_log_le_threshold {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / (1 + Real.log n) ≤ threshold n :=
  div_le_div_of_nonneg_left (Nat.cast_nonneg n)
    (Real.log_pos (by exact_mod_cast hn)) (by linarith)

/-- The sufficient half of the closed form, under the cost of rule access: a rule that some item
follows and whose exceptions fall under the threshold is productive. -/
theorem productive_of_tolerates {n m : ℕ} (hmn : m < n) (h : tolerates n m) :
    Productive n m := by
  -- TODO: for `n ≥ 6`, `strictAnti_eulerMascheroniSeq'` and `eulerMascheroniSeq'_six_lt_two_thirds`
  -- give `harmonic n < log n + 2 / 3`, so a rule with `m ≤ n / (log n + 2 / 3)` is productive by
  -- `productive_of_lt_listTime`. Above that, `log_add_one_le_harmonic` gives
  -- `log n - log (log n + 2 / 3) < harmonic m`, and the saving `(m² / n) (1 - 1 / harmonic m)` of
  -- `ruleTime` over `m` closes the gap once `log n ≥ 6`. The cases `n < 404` are a finite check;
  -- for each of them every `m < n` under the threshold has been checked numerically.
  sorry

/-! ### Bounds on the logarithm and the harmonic numbers -/

private theorem log_lt_of_le_pow {n k : ℕ} (hk : k ≠ 0) (h0 : 0 < n)
    (h : (n : ℝ) ≤ 2.7182818283 ^ k) : Real.log n < k := by
  rw [Real.log_lt_iff_lt_exp (by exact_mod_cast h0), show (k : ℝ) = k * 1 by ring,
    Real.exp_nat_mul]
  exact h.trans_lt (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) hk)

private theorem tolerates_of_log_lt {n e : ℕ} {b : ℝ} (hn : 2 ≤ n) (hb : Real.log n < b)
    (h : (e : ℝ) * b ≤ n) : tolerates n e := by
  unfold tolerates threshold
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [le_div_iff₀ hl]
  nlinarith [Nat.cast_nonneg (α := ℝ) e]

private theorem productive_of_log_lt {n m : ℕ} {b : ℝ} (hn : 2 ≤ n) (hmn : m ≤ n)
    (hb : Real.log n < b) (h : (m : ℝ) * (1 + b) ≤ n) : Productive n m := by
  refine productive_of_le_div_one_add_log hn hmn ?_
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  rw [le_div_iff₀ (by linarith)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

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
private theorem productive_500 {m : ℕ} (hm : 80 ≤ m)
    (h : (m / 500 : ℝ) * (m / 4) + (1 - m / 500) * m < 6000 / 83) : Productive 500 m := by
  unfold Productive ruleTime
  rw [listTime_eq, listTime_eq]
  push_cast
  have hl : (m : ℝ) / harmonic m ≤ m / 4 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by norm_num) (four_le_harmonic hm)
  have hr : (6000 / 83 : ℝ) ≤ 500 / harmonic 500 := by
    have hpos : (0 : ℝ) < harmonic 500 := by exact_mod_cast harmonic_pos (by norm_num)
    rw [le_div_iff₀ hpos]
    linarith [harmonic_500_lt]
  linarith [mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ m / 500)]

theorem not_tolerates_500_81 : ¬ tolerates 500 81 := by
  unfold tolerates threshold
  push_cast
  rw [le_div_iff₀ (Real.log_pos (by norm_num)), not_le]
  linarith [log_500_gt]

theorem productive_500_81 : Productive 500 81 :=
  productive_500 (by norm_num) (by norm_num)

/-- The closed form holds of the cost of rule access only approximately: a rule with 81
exceptions among 500 items is productive by the cost, though the threshold tolerates at most 80. -/
theorem not_forall_productive_imp_tolerates : ¬ ∀ n m, Productive n m → tolerates n m :=
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
  unfold Productive ruleTime
  rw [listTime_eq, listTime_eq, harmonic_23_eq]
  obtain ⟨h1, h2⟩ := harmonic_100_bounds
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  linarith

theorem not_productive_100_24 : ¬ Productive 100 24 := by
  unfold Productive ruleTime
  rw [listTime_eq, listTime_eq, harmonic_24_eq]
  obtain ⟨h1, h2⟩ := harmonic_100_bounds
  rw [not_lt, div_le_iff₀ (by linarith)]
  push_cast
  linarith

/-! ### The German feminine plural -/

/-- The *-(e)n* plural of the German feminine nouns is tolerated and productive in both of
Yang's counts, the nouns whose plural takes another suffix being its exceptions. -/
theorem tolerates_productive_femininePlural (c : Corpus) :
    tolerates (femininePlural c).nouns ((femininePlural c).nouns - (femininePlural c).enPlurals) ∧
      Productive (femininePlural c).nouns
        ((femininePlural c).nouns - (femininePlural c).enPlurals) := by
  cases c
  · show tolerates 166 20 ∧ Productive 166 20
    have hb := log_lt_of_le_pow (n := 166) (k := 6) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨tolerates_of_log_lt (by norm_num) hb (by norm_num),
      productive_of_log_lt (by norm_num) (by norm_num) hb (by norm_num)⟩
  · show tolerates 1549 103 ∧ Productive 1549 103
    have hb := log_lt_of_le_pow (n := 1549) (k := 8) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨tolerates_of_log_lt (by norm_num) hb (by norm_num),
      productive_of_log_lt (by norm_num) (by norm_num) hb (by norm_num)⟩

end Yang2016
