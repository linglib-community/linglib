/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.WordOrder
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Boundary distance in an arrangement

When each element `c` of an arrangement is `ℓ c` words long, the distance in words between the
closest boundaries of two elements is one more than the lengths of the elements between them.
Summed over the elements after an element `x`, the distance from `x` weighs each element's length
by the number of elements farther out, so by the rearrangement inequality an order whose lengths
grow outward is shortest: short before long after `x`, and long before short before it.

## Main definitions

* `WordOrder.Arrangement.boundaryDist`: the distance in words between two elements of given
  lengths in an arrangement.

## Main results

* `WordOrder.Arrangement.sum_boundaryDist_after`: the summed distance from an element to those
  after it, by length and number of elements farther out.
* `WordOrder.Arrangement.sum_boundaryDist_after_le`: no rearrangement of the elements after an
  element is shorter than the order whose lengths grow outward.
* `WordOrder.Arrangement.sum_boundaryDist_before_le`: the mirror image, for the elements before.

## References

* [behaghel-1909]
* [gildea-temperley-2007]
* [futrell-levy-gibson-2020]
-/

@[expose] public section

namespace WordOrder.Arrangement

open Finset

variable {α : Type*} {n : ℕ}

section Monovary

variable {a : Arrangement α n} (ℓ : α → ℕ)

theorem monovaryOn_mirror_iff {s : Set α} : MonovaryOn ℓ a.mirror s ↔ AntivaryOn ℓ a s := by
  simp only [MonovaryOn, AntivaryOn, mirror, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
  exact ⟨fun h i hi j hj hij ↦ h hj hi hij, fun h i hi j hj hij ↦ h hj hi hij⟩

private theorem antivaryOn_rank_iff_monovaryOn {s : Set α} :
    AntivaryOn ℓ (fun d ↦ n - 1 - a d) s ↔ MonovaryOn ℓ a s := by
  constructor <;> intro h i hi j hj hij <;> refine h hj hi ?_ <;>
    · have := (a j).isLt
      have := (a i).isLt
      simp only [Fin.lt_def] at hij ⊢
      omega

end Monovary

section Fintype

variable [Fintype α]

section after

variable {a : Arrangement α n} {x : α}

theorem card_after (d : α) : #(a.after d) = n - 1 - a d := by
  rw [← Fin.card_Ioi, ← card_map a.toEmbedding]
  congr 1; ext j
  simp only [mem_map, mem_after, Precedes, Equiv.coe_toEmbedding, mem_Ioi]
  exact ⟨fun ⟨c, hc, hj⟩ ↦ hj ▸ hc, fun h ↦ ⟨a.symm j, by simpa using h, by simp⟩⟩

variable {σ : Equiv.Perm α} (hσ : {c | σ c ≠ c} ⊆ ↑(a.after x))
include hσ

theorem apply_eq_self_of_notMem_after {c : α} (hc : c ∉ a.after x) : σ c = c := by
  by_contra h
  exact hc (hσ h)

theorem mem_after_apply_of_mem {c : α} (hc : c ∈ a.after x) : σ c ∈ a.after x := by
  by_cases h : σ c = c
  · rwa [h]
  · exact hσ fun h' ↦ h (σ.injective h')

theorem precedes_trans_iff_of_notMem_after {c d : α} (hc : c ∉ a.after x) :
    (Precedes (σ.trans a) c d ↔ a.Precedes c d) ∧ (Precedes (σ.trans a) d c ↔ a.Precedes d c) := by
  simp only [Precedes, Equiv.trans_apply, apply_eq_self_of_notMem_after hσ hc]
  by_cases hd : d ∈ a.after x
  · have h₁ := mem_after.1 (mem_after_apply_of_mem hσ hd)
    have h₂ := mem_after.1 hd
    simp only [mem_after, Precedes, Fin.lt_def, not_lt] at h₁ h₂ hc
    simp only [Fin.lt_def]
    constructor <;> constructor <;> intro <;> omega
  · rw [apply_eq_self_of_notMem_after hσ hd]; exact ⟨Iff.rfl, Iff.rfl⟩

theorem after_trans : after (σ.trans a) x = a.after x := by
  ext c
  simp only [mem_after]
  exact (precedes_trans_iff_of_notMem_after hσ notMem_after_self).1

end after

variable [DecidableEq α] (a : Arrangement α n) (ℓ : α → ℕ) (x y : α)

/-- The distance in words between the closest boundaries of `x` and `y` when each element `c` is
`ℓ c` words long, which is one more than the words of the elements between them and zero from an
element to itself. -/
def boundaryDist : ℕ :=
  if x = y then 0 else
    1 + ∑ c with a.Precedes x c ∧ a.Precedes c y ∨ a.Precedes y c ∧ a.Precedes c x, ℓ c

@[simp] theorem boundaryDist_self : a.boundaryDist ℓ x x = 0 := by simp [boundaryDist]

theorem boundaryDist_comm : a.boundaryDist ℓ x y = a.boundaryDist ℓ y x := by
  simp only [boundaryDist, eq_comm (a := x), or_comm]

@[simp] theorem boundaryDist_mirror : a.mirror.boundaryDist ℓ x y = a.boundaryDist ℓ x y := by
  simp only [boundaryDist, precedes_mirror, and_comm, or_comm]

variable {a x y}

/-- The distance reads only the lengths of the elements strictly between its ends. -/
theorem boundaryDist_congr {ℓ' : α → ℕ} (h : ∀ c, c ≠ x → c ≠ y → ℓ c = ℓ' c) :
    a.boundaryDist ℓ x y = a.boundaryDist ℓ' x y := by
  unfold boundaryDist
  split_ifs
  · rfl
  refine congrArg (1 + ·) (sum_congr rfl fun c hc ↦ h c ?_ ?_) <;>
    · rintro rfl
      simp [Precedes] at hc

theorem boundaryDist_of_precedes (h : a.Precedes x y) :
    a.boundaryDist ℓ x y = 1 + ∑ c with a.Precedes x c ∧ a.Precedes c y, ℓ c := by
  rw [boundaryDist, ite_eq_right fun e ↦ (e ▸ h).asymm (e ▸ h)]
  exact congrArg _ (sum_congr (filter_congr fun c _ ↦ or_iff_left fun hc ↦
    h.asymm (hc.1.trans hc.2)) fun _ _ ↦ rfl)

/-- The weight before `y` is the weight before `x`, then `x`, then the weight between them. -/
theorem sum_precedes_of_precedes (w : α → ℕ) (h : a.Precedes x y) :
    ∑ d with a.Precedes d y, w d =
      ∑ d with a.Precedes d x, w d + w x + ∑ d with a.Precedes x d ∧ a.Precedes d y, w d := by
  have e : univ.filter (fun d ↦ a.Precedes d y ∧ ¬ a.Precedes d x) =
      insert x (univ.filter fun d ↦ a.Precedes x d ∧ a.Precedes d y) := by
    ext d
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hdx : d = x
    · rw [hdx]
      exact ⟨fun _ ↦ .inl rfl, fun _ ↦ ⟨h, fun h' ↦ h'.asymm h'⟩⟩
    · have := a.injective.ne hdx
      simp only [hdx, false_or, Precedes, Fin.lt_def, ne_eq, Fin.ext_iff] at this h ⊢
      omega
  rw [← sum_filter_add_sum_filter_not {d | a.Precedes d y} (a.Precedes · x), filter_filter,
    filter_filter, e,
    sum_insert (by simp [Precedes]), add_assoc]
  exact congrArg (· + _) (sum_congr (filter_congr fun d _ ↦ and_iff_right_of_imp (·.trans h))
    fun _ _ ↦ rfl)

variable (a x y)

section Behaghel

variable {a x}

theorem sum_boundaryDist_after :
    ∑ c ∈ a.after x, a.boundaryDist ℓ x c =
      #(a.after x) + ∑ d ∈ a.after x, ℓ d * (n - 1 - a d) := by
  rw [sum_congr rfl fun c hc ↦ boundaryDist_of_precedes ℓ (mem_after.1 hc)]
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, add_right_inj]
  calc ∑ c ∈ a.after x, ∑ d with a.Precedes x d ∧ a.Precedes d c, ℓ d
      = ∑ c ∈ a.after x, ∑ d ∈ a.after x with a.Precedes d c, ℓ d := by
        simp only [after, filter_filter]
    _ = ∑ d ∈ a.after x, ∑ c ∈ a.after x with a.Precedes d c, ℓ d := by
        simp only [sum_filter]
        rw [Finset.sum_comm]
    _ = ∑ d ∈ a.after x, ℓ d * (n - 1 - a d) := by
        refine sum_congr rfl fun d hd ↦ ?_
        rw [sum_const, smul_eq_mul, mul_comm, ← card_after]
        congr 2
        ext c
        simp only [mem_filter, mem_after]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨(mem_after.1 hd).trans h, h⟩⟩

section perm

variable {σ : Equiv.Perm α} (hσ : {c | σ c ≠ c} ⊆ ↑(a.after x))
include hσ

theorem boundaryDist_trans_of_notMem_after {c : α} (hc : c ∉ a.after x) :
    boundaryDist (σ.trans a) ℓ x c = a.boundaryDist ℓ x c := by
  have hx := notMem_after_self (a := a) (x := x)
  simp only [boundaryDist, (precedes_trans_iff_of_notMem_after hσ hx).1,
    (precedes_trans_iff_of_notMem_after hσ hx).2, (precedes_trans_iff_of_notMem_after hσ hc).1,
    (precedes_trans_iff_of_notMem_after hσ hc).2]

/-- When the lengths of the elements after `x` grow outward (`ℓ` monovaries with rank, short
before long), no rearrangement of them shortens the distance from `x` to them: the nesting of
dependents by length of [gildea-temperley-2007]. [futrell-levy-gibson-2020] derive from it
Behaghel's law of growing constituents in head-initial contexts; [behaghel-1909] states the law for
the conjuncts of a coordination (pp. 110, 139). -/
theorem sum_boundaryDist_after_le (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c ∈ a.after x, a.boundaryDist ℓ x c ≤
      ∑ c ∈ after (σ.trans a) x, boundaryDist (σ.trans a) ℓ x c := by
  rw [sum_boundaryDist_after, sum_boundaryDist_after, after_trans hσ]
  refine Nat.add_le_add_left ?_ _
  simpa [Equiv.trans_apply] using
    ((antivaryOn_rank_iff_monovaryOn ℓ).2 h).sum_mul_le_sum_mul_comp_perm hσ

theorem sum_boundaryDist_after_lt_iff (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c ∈ a.after x, a.boundaryDist ℓ x c <
      ∑ c ∈ after (σ.trans a) x, boundaryDist (σ.trans a) ℓ x c ↔
      ¬ MonovaryOn ℓ (σ.trans a) (after (σ.trans a) x) := by
  rw [sum_boundaryDist_after, sum_boundaryDist_after, after_trans hσ, add_lt_add_iff_left,
    ← antivaryOn_rank_iff_monovaryOn]
  simpa [Equiv.trans_apply, Function.comp_def] using
    ((antivaryOn_rank_iff_monovaryOn ℓ).2 h).sum_mul_lt_sum_mul_comp_perm_iff hσ

theorem sum_boundaryDist_le (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c, a.boundaryDist ℓ x c ≤ ∑ c, boundaryDist (σ.trans a) ℓ x c := by
  rw [← sum_filter_add_sum_filter_not univ (a.Precedes x ·),
    ← sum_filter_add_sum_filter_not univ (a.Precedes x ·)]
  refine Nat.add_le_add ?_ (le_of_eq ?_)
  · have := sum_boundaryDist_after_le (ℓ := ℓ) hσ h
    rwa [after_trans hσ] at this
  · refine sum_congr rfl fun c hc ↦ (boundaryDist_trans_of_notMem_after ℓ hσ ?_).symm
    simpa using (mem_filter.1 hc).2

theorem sum_boundaryDist_lt_iff (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c, a.boundaryDist ℓ x c < ∑ c, boundaryDist (σ.trans a) ℓ x c ↔
      ¬ MonovaryOn ℓ (σ.trans a) (after (σ.trans a) x) := by
  have e : ∑ c with ¬ a.Precedes x c, boundaryDist (σ.trans a) ℓ x c =
      ∑ c with ¬ a.Precedes x c, a.boundaryDist ℓ x c :=
    sum_congr rfl fun c hc ↦
      boundaryDist_trans_of_notMem_after ℓ hσ (by simpa using (mem_filter.1 hc).2)
  rw [← sum_filter_add_sum_filter_not univ (a.Precedes x ·),
    ← sum_filter_add_sum_filter_not univ (a.Precedes x ·), e, add_lt_add_iff_right,
    ← sum_boundaryDist_after_lt_iff ℓ hσ h, after_trans hσ]
  exact Iff.rfl

end perm

section before

variable {σ : Equiv.Perm α} (hσ : {c | σ c ≠ c} ⊆ ↑(a.before x))
include hσ

theorem sum_boundaryDist_before_le (h : AntivaryOn ℓ a (a.before x)) :
    ∑ c ∈ a.before x, a.boundaryDist ℓ x c ≤
      ∑ c ∈ before (σ.trans a) x, boundaryDist (σ.trans a) ℓ x c := by
  have h' : {c | σ c ≠ c} ⊆ ↑(a.mirror.after x) := by rwa [← before_eq_after_mirror]
  have e : ∀ b : Arrangement α n, ∑ c ∈ b.before x, b.boundaryDist ℓ x c =
      ∑ c ∈ b.mirror.after x, b.mirror.boundaryDist ℓ x c := fun b ↦ by
    rw [before_eq_after_mirror]
    exact sum_congr rfl fun c _ ↦ (boundaryDist_mirror ..).symm
  rw [e, e]
  exact sum_boundaryDist_after_le (a := a.mirror) ℓ h'
    ((monovaryOn_mirror_iff ℓ).2 ((before_eq_after_mirror (a := a) (x := x)) ▸ h))

end before

end Behaghel

end Fintype

end WordOrder.Arrangement
