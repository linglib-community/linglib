/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.JansenPollmann2001
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Jansen and Pollmann (2001): On round numbers: Pragmatic aspects of numerical expressions

Jansen and Pollmann take a number's roundness to be its suitability for approximation, measured by
its frequency after *about* and its counterparts in four languages, and find it carried by
10-ness, 2-ness and 5-ness, with 2½-ness adding to frequency in general. They reach these
properties through two-number approximations, *about 5 or 6 books*: the pairs are consecutive
members of an arithmetic sequence whose first member and ratio are a power of ten, doubled, or
halved, and in their earlier rule also halved again. A single round number is a member of the
same sequences, among their first nine. They explain the inventory by a principle of favourite
quantities, doubling and halving, sometimes followed by halving again, being the basic means of
manipulating quantities.

Here the ratios are the powers of ten under those operations, in either rule (`Rule.IsRatio`),
a pair is two consecutive members of a sequence (`SeqPair`), and a single number is among the first
nine members of one (`FirstNine`). Among the first nine members of the revised rule's sequences
are exactly the numbers with 10-ness, 2-ness or 5-ness, and the quarter sequences of the original
rule add exactly 2½-ness.

## Implementation notes

* Quantities are rational, since halving and quartering leave the integers (`½ × 10⁰`,
  `¼ × 10¹`); pairs and single numbers are natural, so only the natural ratios `10ⁿ`, `2 × 10ⁿ`,
  `5 × 10ⁿ` and `25 × 10ⁿ` bear on them (`isRatio_natCast_iff`).
* The kinds of `k`-ness are `Numerals.Roundness.Kness` at the paper's zeroth power, 2½-ness of
  `n` being 5-ness of `2n`.
* The rules are the paper's generalizations over corpus pairs, which they fit in 90.8 to 98.2
  percent of cases (p. 197); the theorems test them on the paper's examples.

## TODO

* The regressions of roundness and frequency on these properties (pp. 198–200) belong in
  `Data/Experiments`.

## References

* [jansen-pollmann-2001]
* [sigurd-1988]
-/

@[expose] public section

open Numerals.Roundness

namespace JansenPollmann2001

/-! ### Favourite quantities (p. 200) -/

/-- The basic means of manipulating quantities, doubling and halving, sometimes followed by
halving again. -/
inductive QuantityOp
  /-- Leave the quantity as it is. -/
  | id
  /-- Double it. -/
  | double
  /-- Halve it. -/
  | half
  /-- Halve it twice. -/
  | halfAgain
  deriving DecidableEq

/-- The quantity an operation makes of `q`. -/
def QuantityOp.apply : QuantityOp → ℚ → ℚ
  | .id, q => q
  | .double, q => 2 * q
  | .half, q => q / 2
  | .halfAgain, q => q / 4

/-! ### The sequence rule (pp. 196–197) -/

/-- The two sequence rules for two-number approximations (pp. 196–197). -/
inductive Rule
  /-- The rule of the authors' earlier study, with ratios `1`, `2`, `½` and `¼` times `10ⁿ`. -/
  | original
  /-- The revised rule, without the quarters, which under half a percent of corpus pairs use. -/
  | revised
  deriving DecidableEq

/-- The quantity operations whose results a rule takes as ratios. -/
def Rule.Allows : Rule → QuantityOp → Prop
  | .original, _ => True
  | .revised, op => op ≠ .halfAgain

instance (rule : Rule) : DecidablePred rule.Allows := fun op ↦ by
  cases rule <;> unfold Rule.Allows <;> infer_instance

/-- The ratios of a rule are the powers of ten under its operations, under the original rule all
the favourite quantities. -/
def Rule.IsRatio (rule : Rule) (q : ℚ) : Prop :=
  ∃ op, rule.Allows op ∧ ∃ n : ℕ, q = op.apply (10 ^ n)

variable {r : ℕ}

theorem exists_natCast_eq_id : (∃ n : ℕ, (r : ℚ) = QuantityOp.id.apply (10 ^ n)) ↔
    ∃ n, r = 10 ^ n :=
  exists_congr fun n ↦ by simp only [QuantityOp.apply]; exact_mod_cast Iff.rfl

theorem exists_natCast_eq_double : (∃ n : ℕ, (r : ℚ) = QuantityOp.double.apply (10 ^ n)) ↔
    ∃ n, r = 2 * 10 ^ n :=
  exists_congr fun n ↦ by simp only [QuantityOp.apply]; exact_mod_cast Iff.rfl

theorem exists_natCast_eq_half : (∃ n : ℕ, (r : ℚ) = QuantityOp.half.apply (10 ^ n)) ↔
    ∃ n, r = 5 * 10 ^ n := by
  simp only [QuantityOp.apply]
  constructor
  · rintro ⟨n, h⟩
    have h2 : 2 * r = 10 ^ n := by
      have : (2 : ℚ) * r = 10 ^ n := by rw [h]; ring
      exact_mod_cast this
    rcases n with _ | n
    · omega
    · exact ⟨n, by rw [pow_succ] at h2; omega⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, by push_cast; rw [pow_succ]; ring⟩

theorem exists_natCast_eq_halfAgain :
    (∃ n : ℕ, (r : ℚ) = QuantityOp.halfAgain.apply (10 ^ n)) ↔ ∃ n, r = 25 * 10 ^ n := by
  simp only [QuantityOp.apply]
  constructor
  · rintro ⟨n, h⟩
    have h4 : 4 * r = 10 ^ n := by
      have : (4 : ℚ) * r = 10 ^ n := by rw [h]; ring
      exact_mod_cast this
    rcases n with _ | _ | n
    · omega
    · omega
    · exact ⟨n, by rw [pow_succ, pow_succ] at h4; omega⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 2, by push_cast; rw [pow_succ, pow_succ]; ring⟩

theorem isRatio_natCast_iff (rule : Rule) : rule.IsRatio r ↔
    (∃ n, r = 10 ^ n) ∨ (∃ n, r = 2 * 10 ^ n) ∨ (∃ n, r = 5 * 10 ^ n) ∨
      (rule = .original ∧ ∃ n, r = 25 * 10 ^ n) := by
  simp only [Rule.IsRatio, ← exists_natCast_eq_id, ← exists_natCast_eq_double,
    ← exists_natCast_eq_half, ← exists_natCast_eq_halfAgain]
  constructor
  · rintro ⟨op, hop, h⟩
    cases op
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · cases rule
      · exact .inr (.inr (.inr ⟨rfl, h⟩))
      · exact absurd rfl hop
  · rintro (h | h | h | ⟨rfl, h⟩)
    · exact ⟨.id, by cases rule <;> simp [Rule.Allows], h⟩
    · exact ⟨.double, by cases rule <;> simp [Rule.Allows], h⟩
    · exact ⟨.half, by cases rule <;> simp [Rule.Allows], h⟩
    · exact ⟨.halfAgain, trivial, h⟩

theorem exists_pow_iff_le_log (c : ℕ) (hc : 0 < c) :
    (∃ n, r = c * 10 ^ n) ↔ ∃ n ≤ Nat.log 10 r, r = c * 10 ^ n := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, Nat.le_log_of_pow_le (by decide) ?_, hn⟩, fun ⟨n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  rw [hn]
  exact Nat.le_mul_of_pos_left _ hc

instance (rule : Rule) (r : ℕ) : Decidable (rule.IsRatio r) :=
  decidable_of_iff ((∃ n ≤ Nat.log 10 r, r = 1 * 10 ^ n) ∨ (∃ n ≤ Nat.log 10 r, r = 2 * 10 ^ n) ∨
      (∃ n ≤ Nat.log 10 r, r = 5 * 10 ^ n) ∨
      (rule = .original ∧ ∃ n ≤ Nat.log 10 r, r = 25 * 10 ^ n)) <| by
    rw [isRatio_natCast_iff, ← exists_pow_iff_le_log 1 one_pos, ← exists_pow_iff_le_log 2 two_pos,
      ← exists_pow_iff_le_log 5 (by norm_num), ← exists_pow_iff_le_log 25 (by norm_num)]
    simp only [one_mul]

/-! ### Pairs -/

/-- `[a, b]` are consecutive members of a sequence of the rule (p. 196). -/
def SeqPair (rule : Rule) (a b : ℕ) : Prop :=
  ∃ q, rule.IsRatio q ∧ ∃ k : ℕ, 1 ≤ k ∧ (a : ℚ) = k * q ∧ (b : ℚ) = (k + 1) * q

theorem isRatio_pos {rule : Rule} {q : ℚ} (h : rule.IsRatio q) : 0 < q := by
  obtain ⟨op, -, n, rfl⟩ := h
  cases op <;> simp only [QuantityOp.apply] <;> positivity

theorem seqPair_iff {rule : Rule} {a b : ℕ} :
    SeqPair rule a b ↔ 0 < a ∧ a < b ∧ (b - a) ∣ a ∧ rule.IsRatio ((b - a : ℕ) : ℚ) := by
  constructor
  · rintro ⟨q, hq, k, hk, ha, hb⟩
    have hq0 := isRatio_pos hq
    have hlt : (a : ℚ) < b := by rw [ha, hb, add_mul, one_mul]; exact lt_add_of_pos_right _ hq0
    have hab : a < b := by exact_mod_cast hlt
    have hd : ((b - a : ℕ) : ℚ) = q := by push_cast [hab.le]; rw [ha, hb]; ring
    have hka : a = k * (b - a) := by
      have : (a : ℚ) = k * ((b - a : ℕ) : ℚ) := by rw [hd, ha]
      exact_mod_cast this
    refine ⟨?_, hab, ⟨k, by rw [mul_comm]; exact hka⟩, hd ▸ hq⟩
    calc 0 < k * (b - a) := Nat.mul_pos hk (by omega)
      _ = a := hka.symm
  · rintro ⟨ha, hab, ⟨k, hk⟩, hq⟩
    refine ⟨_, hq, k, ?_, ?_, ?_⟩
    · rcases k with _ | k
      · simp at hk; omega
      · omega
    · have : (a : ℚ) = ((b - a : ℕ) : ℚ) * k := by exact_mod_cast hk
      rw [this, mul_comm]
    · have hb : b = (b - a) * k + (b - a) := by omega
      have : (b : ℚ) = ((b - a : ℕ) : ℚ) * k + ((b - a : ℕ) : ℚ) := by exact_mod_cast hb
      rw [this]; ring

instance (rule : Rule) (a b : ℕ) : Decidable (SeqPair rule a b) :=
  decidable_of_iff _ seqPair_iff.symm

/-! ### From pairs to single numbers (pp. 197–198) -/

/-- `n` is among the first nine members of a sequence of the rule (p. 197). -/
def FirstNine (rule : Rule) (n : ℕ) : Prop :=
  ∃ q, rule.IsRatio q ∧ ∃ m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ (n : ℚ) = m * q

theorem firstNine_iff {rule : Rule} {n : ℕ} : FirstNine rule n ↔
    ∃ op, rule.Allows op ∧ ∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ (n : ℚ) = m * op.apply (10 ^ b) := by
  constructor
  · rintro ⟨_, ⟨op, hop, b, rfl⟩, m, h1, h9, h⟩
    exact ⟨op, hop, b, m, h1, h9, h⟩
  · rintro ⟨op, hop, b, m, h1, h9, h⟩
    exact ⟨_, ⟨op, hop, b, rfl⟩, m, h1, h9, h⟩

variable {n : ℕ}

theorem exists_id_iff : (∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ (n : ℚ) = m * QuantityOp.id.apply (10 ^ b)) ↔
    HasKness 1 n := by
  simp only [QuantityOp.apply, HasKness, mul_one]
  exact exists_congr fun b ↦ exists_congr fun m ↦ by
    constructor <;> rintro ⟨h1, h9, h⟩ <;> exact ⟨h1, h9, by exact_mod_cast h⟩

theorem exists_double_iff :
    (∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ (n : ℚ) = m * QuantityOp.double.apply (10 ^ b)) ↔
      HasKness 2 n := by
  simp only [QuantityOp.apply, HasKness]
  refine exists_congr fun b ↦ exists_congr fun m ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ ?_
  rw [show (m : ℚ) * (2 * 10 ^ b) = ((m * 2 * 10 ^ b : ℕ) : ℚ) by push_cast; ring]
  exact Nat.cast_inj

theorem hasKness_of_half (h : ∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧
    (n : ℚ) = m * QuantityOp.half.apply (10 ^ b)) : HasKness 5 n ∨ HasKness 1 n := by
  obtain ⟨b, m, h1, h9, h⟩ := h
  have h2 : 2 * n = m * 10 ^ b := by
    have : (2 : ℚ) * n = m * 10 ^ b := by rw [h, QuantityOp.apply]; ring
    exact_mod_cast this
  rcases b with _ | b
  · exact .inr ⟨0, n, by simp at h2; omega, by simp at h2; omega, by simp⟩
  · exact .inl ⟨b, m, h1, h9, by rw [pow_succ] at h2; linarith⟩

theorem half_of_hasKness (h : HasKness 5 n) :
    ∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ (n : ℚ) = m * QuantityOp.half.apply (10 ^ b) := by
  obtain ⟨b, m, h1, h9, rfl⟩ := h
  exact ⟨b + 1, m, h1, h9, by simp only [QuantityOp.apply]; push_cast; rw [pow_succ]; ring⟩

theorem hasKness_of_halfAgain (h : ∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧
    (n : ℚ) = m * QuantityOp.halfAgain.apply (10 ^ b)) :
    HasKness 5 (2 * n) ∨ HasKness 5 n ∨ HasKness 1 n := by
  obtain ⟨b, m, h1, h9, h⟩ := h
  have h4 : 4 * n = m * 10 ^ b := by
    have : (4 : ℚ) * n = m * 10 ^ b := by rw [h, QuantityOp.apply]; ring
    exact_mod_cast this
  rcases b with _ | _ | b
  · exact .inr (.inr ⟨0, n, by simp at h4; omega, by simp at h4; omega, by simp⟩)
  · exact .inr (.inl ⟨0, m / 2, by simp at h4; omega, by omega, by simp at h4; simp; omega⟩)
  · exact .inl ⟨b + 1, m, h1, h9, by rw [pow_succ, pow_succ] at h4; rw [pow_succ]; linarith⟩

theorem halfAgain_of_hasKness (h : HasKness 5 (2 * n)) :
    ∃ b m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ (n : ℚ) = m * QuantityOp.halfAgain.apply (10 ^ b) := by
  obtain ⟨b, m, h1, h9, h⟩ := h
  refine ⟨b + 1, m, h1, h9, ?_⟩
  have : (2 : ℚ) * n = m * 5 * 10 ^ b := by exact_mod_cast h
  simp only [QuantityOp.apply]
  rw [pow_succ]
  linarith

/-- A number is among the first nine members of a sequence of the revised rule exactly when it has
10-ness, 2-ness or 5-ness (pp. 197–198). -/
theorem firstNine_revised_iff :
    FirstNine .revised n ↔ ∃ κ ≠ Kness.twoAndAHalf, κ.Holds 0 n := by
  rw [firstNine_iff]
  constructor
  · rintro ⟨op, hop, h⟩
    cases op
    · exact ⟨.ten, by decide, by simpa [Kness.Holds] using exists_id_iff.1 h⟩
    · exact ⟨.two, by decide, by simpa [Kness.Holds] using exists_double_iff.1 h⟩
    · rcases hasKness_of_half h with h | h
      · exact ⟨.five, by decide, by simpa [Kness.Holds] using h⟩
      · exact ⟨.ten, by decide, by simpa [Kness.Holds] using h⟩
    · exact absurd rfl hop
  · rintro ⟨κ, hκ, h⟩
    cases κ <;> simp only [Kness.Holds, pow_zero, mul_one] at h
    · exact ⟨.id, by simp [Rule.Allows], exists_id_iff.2 h⟩
    · exact ⟨.double, by simp [Rule.Allows], exists_double_iff.2 h⟩
    · exact ⟨.half, by simp [Rule.Allows], half_of_hasKness h⟩
    · exact absurd rfl hκ

/-- With the original rule's quarter sequences, 2½-ness joins them, so the first nine members are
the numbers with some kind of `k`-ness (pp. 197, 199–200). -/
theorem firstNine_original_iff : FirstNine .original n ↔ ∃ κ : Kness, κ.Holds 0 n := by
  rw [firstNine_iff]
  constructor
  · rintro ⟨op, -, h⟩
    cases op
    · exact ⟨.ten, by simpa [Kness.Holds] using exists_id_iff.1 h⟩
    · exact ⟨.two, by simpa [Kness.Holds] using exists_double_iff.1 h⟩
    · rcases hasKness_of_half h with h | h
      · exact ⟨.five, by simpa [Kness.Holds] using h⟩
      · exact ⟨.ten, by simpa [Kness.Holds] using h⟩
    · rcases hasKness_of_halfAgain h with h | h | h
      · exact ⟨.twoAndAHalf, by simpa [Kness.Holds] using h⟩
      · exact ⟨.five, by simpa [Kness.Holds] using h⟩
      · exact ⟨.ten, by simpa [Kness.Holds] using h⟩
  · rintro ⟨κ, h⟩
    cases κ <;> simp only [Kness.Holds, pow_zero, mul_one] at h
    · exact ⟨.id, trivial, exists_id_iff.2 h⟩
    · exact ⟨.double, trivial, exists_double_iff.2 h⟩
    · exact ⟨.half, trivial, half_of_hasKness h⟩
    · exact ⟨.halfAgain, trivial, halfAgain_of_hasKness h⟩

/-- No favourite quantity is three times a power of ten, as no number with 3-ness alone owes it
to doubling and halving (pp. 199–200). -/
theorem not_isRatio_three_mul_pow (rule : Rule) (m : ℕ) :
    ¬ rule.IsRatio ((3 * 10 ^ m : ℕ) : ℚ) := by
  have h3 : ∀ c j : ℕ, ¬ 3 ∣ c → 3 * 10 ^ m ≠ c * 10 ^ j := fun c j hc h ↦
    hc ((Nat.Coprime.pow_right j (by decide : Nat.Coprime 3 10)).dvd_of_dvd_mul_right
      (h ▸ Dvd.intro _ rfl))
  rw [isRatio_natCast_iff]
  rintro (⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨-, n, h⟩)
  · exact h3 1 n (by norm_num) (by rw [h, one_mul])
  · exact h3 2 n (by norm_num) h
  · exact h3 5 n (by norm_num) h
  · exact h3 25 n (by norm_num) h

/-! ### The examples -/

/-- Of the paper's examples, `[3, 4]`, `[40, 50]`, `[18, 20]` and `[100, 150]` follow both sequence
rules and `[100, 125]` only the original (p. 196). -/
theorem seqPair_examples :
    (SeqPair .revised 3 4 ∧ SeqPair .revised 40 50 ∧ SeqPair .revised 18 20 ∧
      SeqPair .revised 100 150) ∧
    (SeqPair .original 100 125 ∧ ¬ SeqPair .revised 100 125) ∧
    (¬ SeqPair .original 1 3 ∧ ¬ SeqPair .original 5 7 ∧ ¬ SeqPair .original 6 9 ∧
      ¬ SeqPair .original 40 80) := by
  decide +kernel

/-- The pair of a two-number approximation with its acceptability. -/
def pairRow (r : Datum) : Option (ℕ × ℕ × Bool) := do
  let a ← r.nat? "first"
  let b ← r.nat? "second"
  pure (a, b, decide (r.judgment = .acceptable))

/-- The two-number approximations of p. 195. -/
def pairData : List (ℕ × ℕ × Bool) := Examples.all.filterMap pairRow

/-- The unstarred approximations follow the revised sequence rule and the starred ones do not
(p. 195). -/
theorem pair_rows : ∀ d ∈ pairData, d.2.2 = true ↔ SeqPair .revised d.1 d.2.1 := by
  decide +kernel

-- p. 198
theorem kness_examples :
    (HasKness 1 40 ∧ HasKness 2 40 ∧ HasKness 5 40) ∧
    (HasKness 1 8 ∧ HasKness 2 8 ∧ ¬ HasKness 5 8) ∧
    (HasKness 1 300 ∧ ¬ HasKness 2 300 ∧ HasKness 5 300) ∧
    (HasKness 1 70 ∧ ¬ HasKness 2 70 ∧ ¬ HasKness 5 70) ∧
    (¬ HasKness 1 61 ∧ ¬ HasKness 2 61 ∧ ¬ HasKness 5 61) ∧
    (HasKness 1 20 ∧ HasKness 2 20 ∧ HasKness 5 20) ∧
    (HasKness 1 80 ∧ HasKness 2 80 ∧ ¬ HasKness 5 80) ∧
    (HasKness 1 50 ∧ ¬ HasKness 2 50 ∧ HasKness 5 50) ∧
    (¬ HasKness 1 45 ∧ ¬ HasKness 2 45 ∧ HasKness 5 45) := by
  decide +kernel

end JansenPollmann2001
