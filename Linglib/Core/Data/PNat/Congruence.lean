/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.PNat.Equiv
public import Mathlib.Data.PNat.Interval
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Tactic.PNatToNat

/-!
# Additive congruences of the positive integers with interval classes

The value of a map `f` on the positive integers at a sum depends only on its values at the
summands exactly when the kernel of `f` is a congruence for addition. A congruence of `ℕ+` with
finitely many classes identifies the integers from some point on modulo a period; when its
classes are intervals the period is one. So a map with finitely many values and order-connected
fibers has this property exactly when it is injective up to some `k` and constant above it.

## Main statements

* `PNat.factorsThrough_add_iff`: a map with finitely many values and order-connected fibers has
  values at sums determined by the values at the summands iff it is injective up to some `k` and
  constant above it.
-/

@[expose] public section

namespace PNat

variable {ι : Type*} {f : ℕ+ → ι}

/-- A map with finitely many values and order-connected fibers has values at sums determined by
the values at the summands iff it is injective up to some `k` and constant above it. -/
theorem factorsThrough_add_iff [Finite ι] (hf : ∀ i, (f ⁻¹' {i}).OrdConnected) :
    (fun p : ℕ+ × ℕ+ ↦ f (p.1 + p.2)).FactorsThrough (Prod.map f f) ↔
      ∃ k : ℕ, ∀ m n : ℕ+, f m = f n ↔ m = n ∨ k < m ∧ k < n := by
  classical
  constructor
  · intro H
    have shift {m n : ℕ+} (t : ℕ+) (h : f m = f n) : f (m + t) = f (n + t) :=
      H (a := (m, t)) (b := (n, t)) (by simp [h])
    -- Some fiber is infinite, and an infinite order-connected fiber contains a final segment.
    have hev : ∃ k : ℕ, ∀ m n : ℕ+, k < m → k < n → f m = f n := by
      have : Infinite ℕ+ := Infinite.of_injective _ Equiv.pnatEquivNat.symm.injective
      obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber f
      have hinf : (f ⁻¹' {i}).Infinite := Set.infinite_coe_iff.1 hi
      obtain ⟨a, ha⟩ := hinf.nonempty
      have key (x : ℕ+) (hx : a ≤ x) : f x = i := by
        obtain ⟨b, hb, hxb⟩ := hinf.exists_gt x
        exact (hf i).out ha hb ⟨hx, hxb.le⟩
      exact ⟨a, fun m n hm hn ↦ by
        rw [key m (by pnat_to_nat; omega), key n (by pnat_to_nat; omega)]⟩
    set k := Nat.find hev
    let K : ℕ+ := ⟨k + 1, k.succ_pos⟩
    have hK : (K : ℕ) = k + 1 := rfl
    have top (x : ℕ+) (hx : k < x) : f x = f K := Nat.find_spec hev x K hx k.lt_succ_self
    -- No point at or below `k` takes the value above `k`.
    have below (x : ℕ+) (hx : (x : ℕ) ≤ k) (h : f x = f K) : False := by
      have hx0 := x.pos
      refine Nat.find_min hev (m := x - 1) (by omega) fun m n hm hn ↦ ?_
      have mem (y : ℕ+) (hy : (x : ℕ) - 1 < y) : f y = f K := by
        by_cases hyk : k < (y : ℕ)
        · exact top y hyk
        · exact (hf (f K)).out h rfl
            ⟨(PNat.coe_le_coe _ _).1 (by omega), (PNat.coe_le_coe _ _).1 (by omega)⟩
      rw [mem m hm, mem n hn]
    have key (m n : ℕ+) (hmn : m < n) (h : f m = f n) (hk : ¬ (k < (m : ℕ) ∧ k < (n : ℕ))) :
        False := by
      have hmn' := (PNat.coe_lt_coe _ _).2 hmn
      have hmk : (m : ℕ) ≤ k := by
        by_contra hmk
        exact hk ⟨by omega, by omega⟩
      by_cases hnk : k < (n : ℕ)
      · exact below m hmk (h.trans (top n hnk))
      · -- Shift `m` up to `k`, carrying `n` past it.
        have hm0 := m.pos
        obtain ⟨t, ht⟩ : ∃ t : ℕ+, (t : ℕ) = k - m := ⟨⟨k - m, by omega⟩, rfl⟩
        have e := shift t h
        rw [show m + t = ⟨k, by omega⟩ from PNat.eq (show (m : ℕ) + t = k by omega),
          top (n + t) (by rw [PNat.add_coe]; omega)] at e
        exact below ⟨k, by omega⟩ le_rfl e
    refine ⟨k, fun m n ↦ ⟨fun h ↦ ?_, ?_⟩⟩
    · by_contra hne
      rw [not_or] at hne
      rcases lt_or_gt_of_ne hne.1 with hmn | hmn
      · exact key m n hmn h hne.2
      · exact key n m hmn h.symm fun h' ↦ hne.2 ⟨h'.2, h'.1⟩
    · rintro (rfl | ⟨hm, hn⟩)
      · rfl
      · exact (top m hm).trans (top n hn).symm
  · rintro ⟨k, hk⟩ ⟨m, m'⟩ ⟨n, n'⟩ h
    simp only [Prod.map, Prod.mk.injEq] at h
    refine (hk _ _).2 ?_
    simp only [PNat.add_coe]
    rcases (hk _ _).1 h.1 with rfl | ⟨h1, h1'⟩ <;> rcases (hk _ _).1 h.2 with rfl | ⟨h2, h2'⟩
    · exact Or.inl rfl
    all_goals exact Or.inr ⟨by omega, by omega⟩

end PNat
