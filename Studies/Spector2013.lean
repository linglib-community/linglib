module

public import Linglib.Semantics.Quantification.Numerals.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SuccPred.Nat

/-!
# Spector (2013): Bare Numerals and Scalar Implicatures

This file formalizes the comparison of accounts of bare numerals in [spector-2013]. On the
neo-Gricean account ([horn-1972]) a numeral means *at least n* and the *exactly* reading is
a scalar implicature; on the underspecification account ([carston-1988]) context selects
among *at least*, *exactly* and *at most*; on the exactly-only account ([breheny-2008]) the
numeral means *exactly n* and the other readings are contextual by-products; on the
ambiguity account, lexical in [geurts-2006] and through a covert exhaustivity operator in
[chierchia-fox-spector-2012], the numeral has both an *at least* and an *exactly* reading.
The paper's three generalizations are that *at least* readings are available in every
embedded environment, *exactly* readings in every environment, and *at most* readings only
in downward-entailing ones. The readings are the intervals `Comparison.ge.interval`,
`Comparison.eq.interval` and `Comparison.le.interval` of the degree substrate; exhaustifying a
family of readings indexed by the numeral against the stronger numerals asserts the prejacent and
denies every stronger numeral alternative, and on the numeral itself it is the exact reading
(`exh_iff_bare`, the substrate's `exhNumeral`).

The theorems are symbolic in the numeral. Under a necessity modal the neo-Gricean wide-scope
implicature is weaker than the exact reading (`necessity_implicature_of_exact`,
`necessity_implicature_ne_exact`); under negation the account predicts an indirect
implicature, *exactly n − 1*, that is not perceived (`indirect_implicature`), and cannot
reach the *at most* reading of the tax-exemption conditional, since a strengthening must
entail the literal meaning (`atMost_reading_not_entails_literal`). The lexical *at most*
entry under a possibility modal is satisfied by any small accessible value
(`poss_atMost_of_le`), while the neo-Gricean derivation gives the intended bound
(`poss_implicature_iff`). The exactly-only account reaches the *at most* and *at least*
readings of the conditionals through law-like background knowledge (`exact_extends_downward`,
`exact_extends_upward`) but cannot weaken the exact reading in upward-entailing contexts,
where the *in fact, five* continuation is consistent only with *at least*, nor in degree
uses like the voting age, where the exact reading under necessity is false and the
exhaustified *at least* reading says the minimum (`not_nec_exact_Ici`, `nec_Ici_exh_iff`).
The ambiguity account derives the third generalization: unembedded, *at most* does not
entail *exactly*, so no background can strengthen the exact reading to it
(`atMost_not_entails_exact`), while under negation it does (`not_atMost_imp_not_exact`).
The exhaustivity operator scoping below or above a possibility modal yields three readings
of which a lexical ambiguity provides two (`wide_scope_ne_narrow`, `narrow_ne_base`), and
the intermediate embedded implicature of the professor example is the parse between the
contradictory *at least* parse and the vacuous *exactly* parse (`intermediate_parse_iff`).

## Implementation notes

Modal environments are quantification over a set of accessible values, the counts or
degrees compatible with the requirement or permission. Exhaustification denies every stronger
alternative; for the antitone families of numeral readings this is the denial of the next
numeral alone (`Exhaustification.exhAgainst_lt_iff_succOrder`), which is how the paper computes
it. Prosodic marking, the
metalinguistic use of negation, and the acquisition and processing evidence the paper
reviews are not formalized.

## References

* [spector-2013]
* [horn-1972]
* [carston-1988]
* [breheny-2008]
* [geurts-2006]
* [chierchia-fox-spector-2012]
-/

@[expose] public section

namespace Spector2013

open Numerals Degree Set Exhaustification

/-! ### Environments and exhaustification -/

/-- Necessity over the accessible values `A` holds when every one of them is among `I`. -/
def nec (A I : Set ℕ) : Prop := ∀ k ∈ A, k ∈ I

/-- Possibility over the accessible values `A` holds when one of them is among `I`. -/
def poss (A I : Set ℕ) : Prop := ∃ k ∈ A, k ∈ I

theorem antitone_atLeast (k : ℕ) : Antitone (fun m ↦ k ∈ Comparison.ge.interval m) :=
  fun _ _ h hk ↦ by simp only [Comparison.interval_ge, mem_Ici] at *; omega

theorem antitone_nec (A : Set ℕ) : Antitone (fun m ↦ nec A (Comparison.ge.interval m)) :=
  fun _ _ h hb k hk ↦ antitone_atLeast k h (hb k hk)

theorem antitone_poss (A : Set ℕ) : Antitone (fun m ↦ poss A (Comparison.ge.interval m)) :=
  fun _ _ h ⟨k, hk, hkb⟩ ↦ ⟨k, hk, antitone_atLeast k h hkb⟩

theorem exhNumeral_iff_exh (m k : ℕ) :
    k ∈ exhNumeral m ↔ exhAgainst (· < ·) (fun m ↦ k ∈ Comparison.ge.interval m) m := by
  rw [exhAgainst_lt_iff_succOrder (antitone_atLeast k), Order.succ_eq_add_one]
  exact Iff.rfl

theorem exh_iff_bare (m k : ℕ) :
    exhAgainst (· < ·) (fun m ↦ k ∈ Comparison.ge.interval m) m ↔ k ∈ Comparison.eq.interval m :=
  (exhNumeral_iff_exh m k).symm.trans (by rw [exhNumeral_eq])

theorem exact_imp_atLeast {m k : ℕ} (h : k ∈ Comparison.eq.interval m) :
    k ∈ Comparison.ge.interval m :=
  (mem_singleton_iff.1 h).ge

/-! ### The neo-Gricean account -/

theorem necessity_implicature_of_exact {A : Set ℕ} (hA : A.Nonempty) {m : ℕ}
    (h : nec A (Comparison.eq.interval m)) :
    exhAgainst (· < ·) (fun m ↦ nec A (Comparison.ge.interval m)) m := by
  rw [exhAgainst_lt_iff_succOrder (antitone_nec A), Order.succ_eq_add_one]
  refine ⟨fun k hk ↦ exact_imp_atLeast (h k hk), fun hall ↦ ?_⟩
  obtain ⟨k, hk⟩ := hA
  have h1 := h k hk
  have h2 := hall k hk
  simp only [Comparison.interval_eq, mem_singleton_iff, Comparison.interval_ge, mem_Ici] at h1 h2
  omega

theorem necessity_implicature_ne_exact (m : ℕ) :
    ∃ A : Set ℕ, exhAgainst (· < ·) (fun m ↦ nec A (Comparison.ge.interval m)) m ∧
      ¬ nec A (Comparison.eq.interval m) := by
  refine ⟨{m, m + 1}, ?_, fun hall ↦ ?_⟩
  · rw [exhAgainst_lt_iff_succOrder (antitone_nec _), Order.succ_eq_add_one]
    refine ⟨fun k hk ↦ ?_, fun hall ↦ ?_⟩
    · rcases hk with rfl | rfl <;> simp
    · have := hall m (Or.inl rfl)
      simp only [Comparison.interval_ge, mem_Ici] at this
      omega
  · have := hall (m + 1) (Or.inr rfl)
    simp at this

/-- Under negation the scale reverses: the alternative with the next numeral is weaker. -/
theorem neg_reversal (m k : ℕ) :
    k ∉ Comparison.ge.interval m → k ∉ Comparison.ge.interval (m + 1) :=
  fun h h' ↦ h (antitone_atLeast k (Nat.le_succ m) h')

/-- The indirect implicature the account predicts for *Peter didn't solve n + 1 problems*:
denying the stronger alternative *didn't solve n* yields *exactly n*, which is not
perceived. -/
theorem indirect_implicature (m k : ℕ) :
    (k ∉ Comparison.ge.interval (m + 1) ∧ ¬ k ∉ Comparison.ge.interval m) ↔
      k ∈ Comparison.eq.interval m := by
  simp only [Comparison.interval_ge, mem_Ici, Comparison.interval_eq, mem_singleton_iff, not_not]
  constructor <;> intro h <;> omega

theorem atMost_reading_not_entails_literal (m : ℕ) :
    ∃ B : ℕ → Prop, (∀ k ∈ Comparison.le.interval m, ¬ B k) ∧
      ¬ ∀ k ∈ Comparison.gt.interval m, ¬ B k :=
  ⟨(m < ·), fun k hk hB ↦ by simp only [Comparison.interval_le, mem_Iic] at hk; omega,
    fun h ↦ h (m + 1) (Nat.lt_succ_self m) (Nat.lt_succ_self m)⟩

/-! ### The underspecification account -/

theorem poss_atMost_of_le {A : Set ℕ} {k m : ℕ} (hk : k ∈ A) (h : k ≤ m) :
    poss A (Comparison.le.interval m) :=
  ⟨k, hk, h⟩

theorem poss_implicature_iff (A : Set ℕ) (m : ℕ) :
    exhAgainst (· < ·) (fun m ↦ poss A (Comparison.ge.interval m)) m ↔
      poss A (Comparison.ge.interval m) ∧ nec A (Comparison.le.interval m) := by
  rw [exhAgainst_lt_iff_succOrder (antitone_poss A), Order.succ_eq_add_one]
  simp only [poss, nec, Comparison.interval_ge, mem_Ici, Comparison.interval_le, mem_Iic,
    not_exists, not_and]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun k hk ↦ by have := h2 k hk; omega⟩

/-! ### The exactly-only account -/

theorem exact_extends_downward {B : ℕ → Prop} (hB : ∀ k k', k ≤ k' → B k → B k') {m : ℕ}
    (h : ¬ B m) : ∀ k, k ∈ Comparison.le.interval m → ¬ B k :=
  fun k hk hBk ↦ h (hB k m hk hBk)

theorem exact_extends_upward {B : ℕ → Prop} (hB : ∀ k k', k ≤ k' → B k → B k') {m : ℕ}
    (h : B m) : ∀ k, k ∈ Comparison.ge.interval m → B k :=
  fun k hk ↦ hB m k hk h

theorem atLeast_of_exact_background {B : ℕ → Prop} {m k : ℕ}
    (h : k ∈ Comparison.eq.interval m) (_ : B k) :
    k ∈ Comparison.ge.interval m :=
  exact_imp_atLeast h

theorem not_nec_exact_Ici (m : ℕ) : ¬ nec (Ici m) (Comparison.eq.interval m) := fun h ↦ by
  have := h (m + 1) (Nat.le_succ m)
  simp at this

theorem nec_Ici_atLeast (m : ℕ) : nec (Ici m) (Comparison.ge.interval m) := fun _ hk ↦ hk

theorem nec_Ici_exh_iff (n m : ℕ) :
    exhAgainst (· < ·) (fun m ↦ nec (Ici n) (Comparison.ge.interval m)) m ↔ n = m := by
  rw [exhAgainst_lt_iff_succOrder (antitone_nec _), Order.succ_eq_add_one]
  simp only [nec, mem_Ici, Comparison.interval_ge]
  constructor
  · rintro ⟨h1, h2⟩
    have := h1 n le_rfl
    by_contra hne
    exact h2 fun k hk ↦ by omega
  · rintro rfl
    exact ⟨fun _ hk ↦ hk, fun h ↦ by have := h n le_rfl; omega⟩

/-! ### The ambiguity account and the third generalization -/

theorem atMost_not_entails_exact {m : ℕ} (hm : 0 < m) :
    ¬ ∀ k, k ∈ Comparison.le.interval m → k ∈ Comparison.eq.interval m := fun h ↦ by
  have := h 0 (Nat.zero_le m)
  simp only [Comparison.interval_eq, mem_singleton_iff] at this
  omega

theorem not_atMost_imp_not_exact {m k : ℕ} (h : k ∉ Comparison.le.interval m) :
    k ∉ Comparison.eq.interval m :=
  fun h' ↦ h (mem_singleton_iff.1 h').le

/-! ### Exhaustivity operators and embedded implicatures -/

theorem poss_exact_imp_poss_atLeast {A : Set ℕ} {m : ℕ} (h : poss A (Comparison.eq.interval m)) :
    poss A (Comparison.ge.interval m) :=
  let ⟨k, hk, h⟩ := h
  ⟨k, hk, exact_imp_atLeast h⟩

theorem wide_scope_ne_narrow (m : ℕ) :
    ∃ A : Set ℕ, poss A (Comparison.eq.interval m) ∧
      ¬ exhAgainst (· < ·) (fun m ↦ poss A (Comparison.ge.interval m)) m := by
  refine ⟨{m, m + 1}, ⟨m, Or.inl rfl, rfl⟩, ?_⟩
  rw [exhAgainst_lt_iff_succOrder (antitone_poss _), Order.succ_eq_add_one]
  rintro ⟨-, h⟩
  exact h ⟨m + 1, Or.inr rfl, mem_Ici.2 le_rfl⟩

theorem narrow_ne_base (m : ℕ) :
    ∃ A : Set ℕ, poss A (Comparison.ge.interval m) ∧ ¬ poss A (Comparison.eq.interval m) := by
  refine ⟨{m + 1}, ⟨m + 1, rfl, Nat.le_succ m⟩, ?_⟩
  rintro ⟨k, hk, h⟩
  rw [mem_singleton_iff] at hk
  subst hk
  simp at h

section Intermediate

variable {S : Type*} (n : S → ℕ) (managed : S → Prop) (m : ℕ)

theorem atLeast_parse_contradiction
    (h : ∀ s, nec (Ici (n s)) (Comparison.ge.interval m) → managed s) :
    ¬ ∃ s, m < n s ∧ ¬ managed s := by
  rintro ⟨s, hs, hm⟩
  exact hm (h s fun k (hk : n s ≤ k) ↦ show m ≤ k by omega)

theorem exact_parse_vacuous (s : S) : ¬ nec (Ici (n s)) (Comparison.eq.interval m) := fun h ↦ by
  have := h (n s + m + 1) (by simp only [mem_Ici]; omega)
  simp only [Comparison.interval_eq, mem_singleton_iff] at this
  omega

theorem intermediate_parse_iff :
    (∀ s, exhAgainst (· < ·) (fun m ↦ nec (Ici (n s)) (Comparison.ge.interval m)) m → managed s) ↔
      ∀ s, n s = m → managed s := by
  simp only [nec_Ici_exh_iff]

end Intermediate

end Spector2013
