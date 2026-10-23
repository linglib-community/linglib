module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.Int
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Positivity

/-!
# Yang (2016): The Price of Linguistic Productivity

This file formalizes the Tolerance Principle of [yang-2016]: a rule applicable to `N` items
is productive only if its exceptions number at most `N / ln N` (`threshold`, `tolerates`).
The principle is derived from the cost of rule access under the Elsewhere Condition, in the
form first given in [yang-2005]. The `N` items are ranked by frequency and searched serially,
so under a Zipfian distribution the expected time to reach an item in a list of `N` is
`N / H_N`, with `H_N` the harmonic number (`listTime`). A productive rule lists its `M`
exceptions before the rule, so an exception is found in expected time `T(M, M)` and a
regular item after all `M` exceptions have been rejected (`ruleTime`); listing everything
costs `T(N, N)`, and the rule is productive when the former does not exceed the latter
(`Productive`). Since the rule's cost never exceeds `M` (`ruleTime_le`), any rule with at
most `N / H_N` exceptions is productive (`productive_of_le_listTime`), hence any rule with at
most `N / (1 + ln N)` exceptions (`productive_of_le_div_one_add_log`); the threshold of the
principle replaces the harmonic number by the logarithm it approximates. The German
feminine plural, with some eighty exceptions among at least five hundred nouns, is tolerated
(`tolerates_500_80`).

## Implementation notes

Yang's simplification of the rule's cost, that a random subset of a Zipfian list is again
Zipfian, is taken as the definition of `ruleTime`. The threshold is stated with the natural
logarithm as in the book, and its relation to the exact harmonic bound is recorded by the
sufficiency theorems rather than by the book's approximate solution of `T(N, N) = T(N, M)`.
Mathlib's convention that division by zero is zero makes the threshold vanish at `N ≤ 1`.

## References

* [yang-2016]
* [yang-2005]
-/

@[expose] public section

namespace Yang2016

open Finset

/-! ### The Tolerance Principle -/

/-- The tolerance threshold for a rule applicable to `n` items. -/
noncomputable def threshold (n : ℕ) : ℝ := (n : ℝ) / Real.log n

/-- A rule with `n` items in scope and `e` exceptions is tolerated when the exceptions fit
under the threshold. -/
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

/-- A rule is productive when it costs no more than listing everything. -/
def Productive (n m : ℕ) : Prop := ruleTime n m ≤ listTime n

theorem ruleTime_self (n : ℕ) (hn : 0 < n) : ruleTime n n = listTime n := by
  unfold ruleTime
  rw [div_self (by exact_mod_cast hn.ne')]
  ring

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

theorem productive_of_le_listTime {n m : ℕ} (hmn : m ≤ n) (h : (m : ℝ) ≤ listTime n) :
    Productive n m :=
  (ruleTime_le hmn).trans h

theorem div_one_add_log_le_listTime (n : ℕ) : (n : ℝ) / (1 + Real.log n) ≤ listTime n := by
  rw [listTime_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg n)
      (by exact_mod_cast harmonic_pos hn.ne') (harmonic_le_one_add_log n)

theorem productive_of_le_div_one_add_log {n m : ℕ} (hmn : m ≤ n)
    (h : (m : ℝ) ≤ n / (1 + Real.log n)) : Productive n m :=
  productive_of_le_listTime hmn (h.trans (div_one_add_log_le_listTime n))

theorem div_one_add_log_le_threshold {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / (1 + Real.log n) ≤ threshold n :=
  div_le_div_of_nonneg_left (Nat.cast_nonneg n)
    (Real.log_pos (by exact_mod_cast hn)) (by linarith)

/-! ### The German feminine plural -/

theorem tolerates_500_80 : tolerates 500 80 := by
  unfold tolerates threshold
  push_cast
  have hlog : Real.log 500 < 25 / 4 := by
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
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  linarith

end Yang2016
