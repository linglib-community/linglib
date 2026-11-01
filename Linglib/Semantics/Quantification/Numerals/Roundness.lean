module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Concept
public import Linglib.Core.Order.OfCriteria
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.DeriveFintype

/-!
# Numeral roundness

A number is round by having roundness properties: for Sigurd, divisibility by a power of ten
from ten up or by its half or quarter; for Jansen and Pollmann, 10-ness, 2-ness, 5-ness and
2½-ness, `k`-ness being a digit times `k` times a power of ten; for Woodin et al., these over
positive powers of ten together with being a multiple of five or of ten; and for Haslinger, lying
on the conventionalized scales salient in a context, Krifka's scales of multiples of a width.

Numbers and properties form a formal context. A number's profile is the intent of its object
concept, and a number is at least as round as another when its profile contains the other's,
Haslinger's ordering, so the numbers at least as round as `d` are the extent closure of `d`;
counting properties gives the roundness scores. On scales of multiples the closure is again a
scale, the multiples of the lcm of the widths through `d`, so the numbers at least as round as `d`
are closed under addition. Scales of different granularity should align, Krifka argues, their
widths forming a chain under divisibility, and on aligned scales that lcm is the coarsest width
through `d`.

## Main definitions

* `Numerals.Roundness.AtLeastAsRound`: having every roundness property of a number, the
  criteria-derived preorder with the roundness properties as criteria
  (`atLeastAsRound_iff_ofCriteria`).
* `Numerals.Roundness.profile`, `Numerals.Roundness.score`: the roundness properties a number
  has, and their number.
* `Numerals.Roundness.OnScale`: lying on a scale of multiples.
* `Numerals.Roundness.HasKness`, `Numerals.Roundness.Kness`: Jansen and Pollmann's `k`-ness and
  its four kinds, over powers of ten from a given one.

## Main statements

* `Numerals.Roundness.atLeastAsRound_iff_mem_extentClosure`: the numbers at least as round as `d`
  are its extent closure.
* `Numerals.Roundness.extentClosure_onScale`: on scales of multiples, that closure is the scale of
  multiples of `scaleLcm W d`.
* `Numerals.Roundness.AtLeastAsRound.add`: on scales of multiples, the numbers at least as round
  as `d` are closed under addition.
* `Numerals.Roundness.atLeastAsRound_onScale_iff_dvd`: roundness on scales of multiples is
  divisibility of these lcms.
* `Numerals.Roundness.isLeast_atLeastAsRound_onScale`: the least number above `d` at least as
  round as `d` is `d + scaleLcm W d`, the next point of that scale.
* `Numerals.Roundness.isGreatest_scaleLcm`: on aligned scales, `scaleLcm W d` is the coarsest
  width through `d`.

## Implementation notes

A roundness property is an attribute of the formal context `r : D → ι → Prop`, so a family of
properties and a set of salient scales are the same kind of object. Woodin et al.'s regression
weights the properties unequally; `score` counts them equally. A width is a natural number, since
the multiples of `w` and of `-w` are one scale; the numbers on it range over `ℤ`.

## References

* [sigurd-1988]
* [jansen-pollmann-2001]
* [krifka-2007]
* [woodin-etal-2024]
* [haslinger-2025-diss]
-/

@[expose] public section

namespace Numerals.Roundness

open Finset

/-! ### Roundness profiles -/

section Profile

variable {D ι : Type*} {r : D → ι → Prop} {d e f : D}

/-- `e` is at least as round as `d` when it has every roundness property that `d` has. -/
def AtLeastAsRound (r : D → ι → Prop) (d e : D) : Prop := ∀ ⦃i⦄, r d i → r e i

/-- Being at least as round is the criteria-derived preorder with every roundness property as a
criterion. -/
theorem atLeastAsRound_iff_ofCriteria :
    AtLeastAsRound r d e ↔ (Preorder.ofCriteria r Set.univ).le e d :=
  ⟨fun h _ _ hi ↦ h hi, fun h _ hi ↦ h _ trivial hi⟩

@[refl] theorem AtLeastAsRound.refl (r : D → ι → Prop) (d : D) : AtLeastAsRound r d d :=
  fun _ h ↦ h

theorem AtLeastAsRound.trans (h₁ : AtLeastAsRound r d e) (h₂ : AtLeastAsRound r e f) :
    AtLeastAsRound r d f := fun _ h ↦ h₂ (h₁ h)

theorem atLeastAsRound_iff_upperPolar_subset :
    AtLeastAsRound r d e ↔ upperPolar r {d} ⊆ upperPolar r {e} := by
  simp only [AtLeastAsRound, Set.subset_def, mem_upperPolar_singleton]

/-- The numbers at least as round as `d` are the extent closure of `d`. -/
theorem atLeastAsRound_iff_mem_extentClosure : AtLeastAsRound r d e ↔ e ∈ extentClosure r {d} := by
  simp only [extentClosure_apply, mem_lowerPolar_iff, mem_upperPolar_singleton]
  exact Iff.rfl

variable [Fintype ι] [∀ d, DecidablePred (r d)]

/-- The roundness properties a number has. -/
def profile (r : D → ι → Prop) [∀ d, DecidablePred (r d)] (d : D) : Finset ι := univ.filter (r d)

@[simp] theorem mem_profile {i : ι} : i ∈ profile r d ↔ r d i := by simp [profile]

/-- The profile of `d` is the intent of its object concept. -/
theorem coe_profile : (profile r d : Set ι) = upperPolar r {d} := by
  ext i
  simp [mem_upperPolar_singleton]

theorem profile_subset_profile : profile r d ⊆ profile r e ↔ AtLeastAsRound r d e := by
  simp only [Finset.subset_iff, mem_profile]
  exact Iff.rfl

/-- The roundness score of a number is the number of roundness properties it has. -/
def score (r : D → ι → Prop) [∀ d, DecidablePred (r d)] (d : D) : ℕ := (profile r d).card

theorem score_le_card (d : D) : score r d ≤ Fintype.card ι :=
  card_le_univ _

theorem AtLeastAsRound.score_le (h : AtLeastAsRound r d e) : score r d ≤ score r e :=
  card_le_card (profile_subset_profile.2 h)

end Profile

/-! ### Scales of multiples -/

section Scale

variable {W : Finset ℕ} {d e f : ℤ}

/-- `d` lies on the scale of width `w`, the multiples of `w`, among the widths `W`. -/
def OnScale (W : Finset ℕ) (d : ℤ) (w : W) : Prop := d ∈ AddSubgroup.zmultiples ((w : ℕ) : ℤ)

theorem atLeastAsRound_onScale_iff :
    AtLeastAsRound (OnScale W) d e ↔ ∀ w ∈ W, (w : ℤ) ∣ d → (w : ℤ) ∣ e := by
  simp [AtLeastAsRound, OnScale, Int.mem_zmultiples_iff]

instance : Decidable (AtLeastAsRound (OnScale W) d e) :=
  decidable_of_iff _ atLeastAsRound_onScale_iff.symm

/-- The lcm of the widths of the scales through `d`. -/
def scaleLcm (W : Finset ℕ) (d : ℤ) : ℕ := (W.filter fun w : ℕ ↦ (w : ℤ) ∣ d).lcm id

theorem atLeastAsRound_onScale_iff_scaleLcm_dvd :
    AtLeastAsRound (OnScale W) d e ↔ (scaleLcm W d : ℤ) ∣ e := by
  simp [atLeastAsRound_onScale_iff, scaleLcm, Int.natCast_dvd, Finset.lcm_dvd_iff]

theorem scaleLcm_dvd (W : Finset ℕ) (d : ℤ) : (scaleLcm W d : ℤ) ∣ d :=
  atLeastAsRound_onScale_iff_scaleLcm_dvd.1 (.refl _ d)

/-- On scales of multiples, the numbers at least as round as `d` are the meet of the scales
through `d`, the scale of multiples of their lcm. -/
theorem extentClosure_onScale :
    extentClosure (OnScale W) {d} = AddSubgroup.zmultiples (scaleLcm W d : ℤ) := by
  ext e
  rw [← atLeastAsRound_iff_mem_extentClosure, SetLike.mem_coe, Int.mem_zmultiples_iff,
    atLeastAsRound_onScale_iff_scaleLcm_dvd]

/-- On scales of multiples, the numbers at least as round as `d` are closed under addition. -/
theorem AtLeastAsRound.add (h₁ : AtLeastAsRound (OnScale W) d e)
    (h₂ : AtLeastAsRound (OnScale W) d f) : AtLeastAsRound (OnScale W) d (e + f) := by
  rw [atLeastAsRound_onScale_iff_scaleLcm_dvd] at *
  exact dvd_add h₁ h₂

/-- On scales of multiples, roundness is divisibility of the lcms of the widths. -/
theorem atLeastAsRound_onScale_iff_dvd :
    AtLeastAsRound (OnScale W) d e ↔ scaleLcm W d ∣ scaleLcm W e := by
  refine ⟨fun h ↦ Finset.lcm_mono fun w hw ↦ ?_, fun h ↦ ?_⟩
  · rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, atLeastAsRound_onScale_iff.1 h w hw.1 hw.2⟩
  · exact atLeastAsRound_onScale_iff_scaleLcm_dvd.2
      ((Int.natCast_dvd_natCast.2 h).trans (scaleLcm_dvd W e))

theorem scaleLcm_pos (hW : 0 ∉ W) (d : ℤ) : 0 < scaleLcm W d := by
  refine Nat.pos_of_ne_zero fun h ↦ hW ?_
  obtain ⟨w, hw, hw0⟩ := Finset.lcm_eq_zero_iff.1 h
  exact hw0 ▸ (Finset.mem_filter.1 hw).1

theorem AtLeastAsRound.scaleLcm_dvd_sub (h : AtLeastAsRound (OnScale W) d e) :
    (scaleLcm W d : ℤ) ∣ e - d :=
  dvd_sub (atLeastAsRound_onScale_iff_scaleLcm_dvd.1 h) (scaleLcm_dvd W d)

theorem AtLeastAsRound.scaleLcm_le_abs_sub (h : AtLeastAsRound (OnScale W) d e) (hne : e ≠ d) :
    (scaleLcm W d : ℤ) ≤ |e - d| :=
  Int.le_of_dvd (abs_pos.2 (sub_ne_zero.2 hne)) ((dvd_abs _ _).2 h.scaleLcm_dvd_sub)

theorem atLeastAsRound_add_scaleLcm (W : Finset ℕ) (d : ℤ) :
    AtLeastAsRound (OnScale W) d (d + scaleLcm W d) :=
  atLeastAsRound_onScale_iff_scaleLcm_dvd.2 (dvd_add (scaleLcm_dvd W d) dvd_rfl)

/-- On scales of multiples, the least number above `d` at least as round as `d` is the next point
of the scale of multiples of `scaleLcm W d`. -/
theorem isLeast_atLeastAsRound_onScale (hW : 0 ∉ W) (d : ℤ) :
    IsLeast {e | d < e ∧ AtLeastAsRound (OnScale W) d e} (d + scaleLcm W d) :=
  ⟨⟨lt_add_of_pos_right d (by exact_mod_cast scaleLcm_pos hW d), atLeastAsRound_add_scaleLcm W d⟩,
    fun _ ⟨hde, he⟩ ↦ by have := Int.le_of_dvd (sub_pos.2 hde) he.scaleLcm_dvd_sub; omega⟩

/-- On aligned scales, whose widths form a chain under divisibility, the lcm of the widths
through `d` is the coarsest width through `d`. -/
theorem isGreatest_scaleLcm (h0 : 0 ∉ W) (hW : IsChain (· ∣ ·) (W : Set ℕ))
    (hd : ∃ w ∈ W, (w : ℤ) ∣ d) : IsGreatest {w : ℕ | w ∈ W ∧ (w : ℤ) ∣ d} (scaleLcm W d) := by
  set s := W.filter fun w : ℕ ↦ (w : ℤ) ∣ d
  have hne : s.Nonempty := by simpa [s, Finset.Nonempty] using hd
  obtain ⟨hmW, hmd⟩ := Finset.mem_filter.1 (s.max'_mem hne)
  have hle : ∀ w ∈ W, (w : ℤ) ∣ d → w ≤ s.max' hne :=
    fun w hw hwd ↦ s.le_max' _ (Finset.mem_filter.2 ⟨hw, hwd⟩)
  suffices h : scaleLcm W d = s.max' hne from h ▸ ⟨⟨hmW, hmd⟩, fun w hw ↦ hle w hw.1 hw.2⟩
  refine Nat.dvd_antisymm (Finset.lcm_dvd fun w hw ↦ ?_) (Finset.dvd_lcm (s.max'_mem hne))
  obtain ⟨hwW, hwd⟩ := Finset.mem_filter.1 hw
  obtain rfl | hwm := eq_or_ne w (s.max' hne)
  · exact dvd_rfl
  refine (hW hwW hmW hwm).resolve_right fun h ↦ hwm ?_
  exact le_antisymm (hle w hwW hwd)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_of_mem_of_not_mem hwW h0)) h)

end Scale

/-! ### k-ness -/

/-- `n` has `k`-ness when `n = m × k × 10^b` for some digit `1 ≤ m ≤ 9` and exponent `b`, that
is `n ∈ k × {1, …, 9} × 10^ℕ` ([jansen-pollmann-2001]). -/
def HasKness (k n : ℕ) : Prop := ∃ b m, 1 ≤ m ∧ m ≤ 9 ∧ n = m * k * 10 ^ b

theorem hasKness_iff_exists_le_log {k n : ℕ} :
    HasKness k n ↔ ∃ b ≤ Nat.log 10 n, ∃ m < 10, 1 ≤ m ∧ n = m * k * 10 ^ b := by
  constructor
  · rintro ⟨b, m, hm, hm9, rfl⟩
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · exact ⟨0, Nat.zero_le _, m, by omega, hm, by simp⟩
    refine ⟨b, Nat.le_log_of_pow_le (by decide) ?_, m, by omega, hm, rfl⟩
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hm hk)
  · rintro ⟨b, -, m, hm, hm1, rfl⟩
    exact ⟨b, m, hm1, by omega, rfl⟩

instance (k n : ℕ) : Decidable (HasKness k n) :=
  decidable_of_iff _ hasKness_iff_exists_le_log.symm

theorem HasKness.dvd {k n : ℕ} (h : HasKness k n) : k ∣ n := by
  obtain ⟨b, m, -, -, rfl⟩ := h
  exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left k m) _

theorem hasKness_mul_pow_iff {k b₀ n : ℕ} :
    HasKness (k * 10 ^ b₀) n ↔ ∃ b ≥ b₀, ∃ m, 1 ≤ m ∧ m ≤ 9 ∧ n = m * k * 10 ^ b := by
  constructor
  · rintro ⟨b, m, h1, h9, rfl⟩
    exact ⟨b + b₀, by omega, m, h1, h9, by rw [pow_add]; ring⟩
  · rintro ⟨b, hb, m, h1, h9, rfl⟩
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
    exact ⟨c, m, h1, h9, by rw [pow_add]; ring⟩

/-- Jansen and Pollmann's four kinds of `k`-ness. -/
inductive Kness where
  | ten
  | two
  | five
  | twoAndAHalf
  deriving DecidableEq, Repr, Fintype

/-- `n` has `κ`-ness over powers of ten from `10^b₀`, where Jansen and Pollmann take `b₀ = 0` and
Woodin et al. `b₀ = 1`; 2½-ness of `n` is 5-ness of `2n`. -/
def Kness.Holds (b₀ n : ℕ) : Kness → Prop
  | .ten => HasKness (10 ^ b₀) n
  | .two => HasKness (2 * 10 ^ b₀) n
  | .five => HasKness (5 * 10 ^ b₀) n
  | .twoAndAHalf => HasKness (5 * 10 ^ b₀) (2 * n)

instance (b₀ n : ℕ) : DecidablePred (Kness.Holds b₀ n)
  | .ten | .two | .five | .twoAndAHalf => inferInstanceAs (Decidable (HasKness _ _))

end Numerals.Roundness
