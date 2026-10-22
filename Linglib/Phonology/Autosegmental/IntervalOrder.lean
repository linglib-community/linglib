/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.IntervalOrder
public import Linglib.Phonology.Autosegmental.Basic

/-!
# Representations in time

Read in time, the order of each tier is precedence and an association line is overlap. A
representation has an interval order when some interval order on its positions extends the
order of each tier and leaves associated positions incomparable. On two tiers the `2 + 2`
condition of an interval order is the No-Crossing Constraint, and every non-crossing
representation has an interval order; on three tiers, lines that cross none pairwise can chain
around a cycle of tiers that no interval order admits.

## Main definitions

* `AR.HasIntervalOrder`: the representation has an interval order.

## Main results

* `IsNonCrossing.of_intervals`, `IsNonCrossing.exists_intervals`: a relation between two tiers
  is non-crossing iff its pairs are overlaps of intervals placed in tier order.
* `AR.HasIntervalOrder.noCrossing`: a representation with an interval order obeys the NCC.
* `AR.noCrossing_iff_hasIntervalOrder`: on two tiers the converse holds.
* `AR.exists_noCrossing_not_hasIntervalOrder`: on three tiers it fails.

## Implementation notes

A representation fixes precedence only within tiers, so a floating tone and a toneless timing
slot can be ordered either way: a representation has interval orders, generally many, and is
not one. The least precedence it forces is not an interval order in general, since two tiers
without lines form a `2 + 2`.

## References

* [sagey-1988]
* [bird-klein-1990]
* [fishburn-1970]
-/

@[expose] public section

namespace Autosegmental

open NonemptyInterval

/-! ### Relations between two tiers -/

section Intervals

variable {ι κ T : Type*} [Preorder ι] [LinearOrder κ] [LinearOrder T] {R : SetRel ι κ}

/-- A relation whose pairs are overlaps of intervals placed in tier order is non-crossing
([sagey-1988]'s derivation of the No-Crossing Constraint). -/
theorem IsNonCrossing.of_intervals {I : ι → NonemptyInterval T} {J : κ → NonemptyInterval T}
    (hI : ∀ ⦃a b⦄, a < b → (I a).Precedes (I b)) (hJ : ∀ ⦃a b⦄, a < b → (J a).Precedes (J b))
    (hR : ∀ x ∈ R, (I x.1).Overlaps (J x.2)) : IsNonCrossing R := by
  intro x hx y hy hlt
  by_contra! hgt
  rcases IsIntervalOrder.two_plus_two (hI hlt) (hJ hgt) with h | h
  exacts [precedes_not_overlaps h (hR x hx), precedes_not_overlaps h (overlaps_symm (hR y hy))]

end Intervals

/-- A non-crossing relation between two finite tiers is realized by intervals in `ℕ`: with
`B k` the last lower position linked to an upper position before `k`, upper position `p` spans
`p + B p` to `p + B (p + 1)`, and dually below. -/
theorem IsNonCrossing.exists_intervals {n m : ℕ} {R : SetRel (Fin n) (Fin m)}
    (h : IsNonCrossing R) :
    ∃ (I : Fin n → NonemptyInterval ℕ) (J : Fin m → NonemptyInterval ℕ),
      (∀ ⦃a b⦄, a < b → (I a).Precedes (I b)) ∧ (∀ ⦃a b⦄, a < b → (J a).Precedes (J b)) ∧
        ∀ x ∈ R, (I x.1).Overlaps (J x.2) := by
  classical
  let B (k : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n × Fin m ↦ x ∈ R ∧ (x.1 : ℕ) < k).sup
    fun x ↦ (x.2 : ℕ)
  let C (k : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n × Fin m ↦ x ∈ R ∧ (x.2 : ℕ) < k).sup
    fun x ↦ (x.1 : ℕ)
  have le_B {x : Fin n × Fin m} {k : ℕ} (hx : x ∈ R) (hk : (x.1 : ℕ) < k) : (x.2 : ℕ) ≤ B k :=
    Finset.le_sup (f := fun x : Fin n × Fin m ↦ (x.2 : ℕ)) (by simp [hx, hk])
  have le_C {x : Fin n × Fin m} {k : ℕ} (hx : x ∈ R) (hk : (x.2 : ℕ) < k) : (x.1 : ℕ) ≤ C k :=
    Finset.le_sup (f := fun x : Fin n × Fin m ↦ (x.1 : ℕ)) (by simp [hx, hk])
  have B_mono {k k' : ℕ} (hk : k ≤ k') : B k ≤ B k' :=
    Finset.sup_le fun x hx ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact le_B hx.1 (hx.2.trans_le hk)
  have C_mono {k k' : ℕ} (hk : k ≤ k') : C k ≤ C k' :=
    Finset.sup_le fun x hx ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact le_C hx.1 (hx.2.trans_le hk)
  refine ⟨fun p ↦ ⟨(p + B p, p + B (p + 1)), by simpa using B_mono (Nat.le_succ p)⟩,
    fun q ↦ ⟨(q + C q, q + C (q + 1)), by simpa using C_mono (Nat.le_succ q)⟩,
    fun a b hab ↦ ?_, fun a b hab ↦ ?_, fun x hx ↦ ⟨?_, ?_⟩⟩
  · have hab : (a : ℕ) < b := hab
    have := B_mono (show (a : ℕ) + 1 ≤ b from hab)
    show (a : ℕ) + B (a + 1) < b + B b
    omega
  · have hab : (a : ℕ) < b := hab
    have := C_mono (show (a : ℕ) + 1 ≤ b from hab)
    show (a : ℕ) + C (a + 1) < b + C b
    omega
  · have hB : B x.1 ≤ x.2 := Finset.sup_le fun y hy ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact h hy.1 hx hy.2
    show (x.1 : ℕ) + B x.1 ≤ x.2 + C (x.2 + 1)
    rw [Nat.add_comm (x.2 : ℕ)]
    exact Nat.add_le_add (le_C hx (Nat.lt_succ_self x.2)) hB
  · have hC : C x.2 ≤ x.1 := Finset.sup_le fun y hy ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      by_contra! hlt
      exact absurd (h hx hy.1 hlt) (not_le.2 hy.2)
    show (x.2 : ℕ) + C x.2 ≤ x.1 + B (x.1 + 1)
    rw [Nat.add_comm (x.1 : ℕ)]
    exact Nat.add_le_add (le_B hx (Nat.lt_succ_self x.1)) hC

/-! ### Representations -/

namespace AR

variable {ι : Type*} {τ : ι → Type*}

variable (X : AR τ) in
/-- `X` has an interval order: an interval order on its positions that extends the order of
each tier and leaves associated positions incomparable. -/
def HasIntervalOrder : Prop :=
  ∃ r : X.Pos → X.Pos → Prop, IsIntervalOrder X.Pos r ∧
    (∀ i ⦃p q : Fin (X.word i).length⦄, p < q → r ⟨i, p⟩ ⟨i, q⟩) ∧
      ∀ ⦃v w⦄, X.assoc.Adj v w → ¬ r v w

variable {X : AR τ}

/-- Intervals placing each tier in order, with associated positions overlapping, give a
representation an interval order: the precedence of the intervals. -/
theorem hasIntervalOrder_of_intervals {T : Type*} [LinearOrder T] (I : X.Pos → NonemptyInterval T)
    (hI : ∀ i ⦃p q : Fin (X.word i).length⦄, p < q → (I ⟨i, p⟩).Precedes (I ⟨i, q⟩))
    (hA : ∀ ⦃v w⦄, X.assoc.Adj v w → (I v).Overlaps (I w)) : X.HasIntervalOrder :=
  ⟨InvImage Precedes I, isIntervalOrder_precedes.invImage I, hI,
    fun _ _ h hp ↦ precedes_not_overlaps hp (hA h)⟩

/-- A representation with an interval order obeys the No-Crossing Constraint: two crossing
lines would make the order of their tiers a `2 + 2`. -/
theorem HasIntervalOrder.noCrossing (h : X.HasIntervalOrder) : X.NoCrossing := by
  obtain ⟨r, hr, htier, hadj⟩ := h
  refine fun i j ↦ isNonCrossing_lines_iff.2 fun p q p' q' ⟨hp, hq, h₁⟩ ⟨hp', hq', h₂⟩ hlt ↦ ?_
  by_contra! hgt
  rcases hr.two_plus_two (htier i (show (⟨p, hp⟩ : Fin _) < ⟨p', hp'⟩ from hlt))
    (htier j (show (⟨q', hq'⟩ : Fin _) < ⟨q, hq⟩ from hgt)) with h | h
  exacts [hadj h₁ h, hadj h₂.symm h]

/-- On two tiers, a representation obeys the No-Crossing Constraint iff it has an interval
order. -/
theorem noCrossing_iff_hasIntervalOrder {τ : Bool → Type*} {X : AR τ} :
    X.NoCrossing ↔ X.HasIntervalOrder := by
  refine ⟨fun h ↦ ?_, HasIntervalOrder.noCrossing⟩
  obtain ⟨I, J, hI, hJ, hR⟩ := (h true false).exists_intervals
  refine hasIntervalOrder_of_intervals (fun | ⟨true, p⟩ => I p | ⟨false, q⟩ => J q) ?_ ?_
  · rintro (_ | _) p q hpq
    exacts [hJ hpq, hI hpq]
  · rintro ⟨_ | _, p⟩ ⟨_ | _, q⟩ hadj
    · exact (fst_ne_of_adj hadj rfl).elim
    · exact overlaps_symm (hR (q, p) hadj.symm)
    · exact hR (p, q) hadj
    · exact (fst_ne_of_adj hadj rfl).elim

/-- On three tiers the converse fails: with each tier's first position linked to the next
tier's second, around the cycle of tiers, no two lines cross, yet the precedences chain from
the last tier's first position to the first tier's second, to which it is linked. -/
theorem exists_noCrossing_not_hasIntervalOrder :
    ∃ X : AR fun _ : Fin 3 ↦ Unit, X.NoCrossing ∧ ¬ X.HasIntervalOrder := by
  refine ⟨fromRel (fun _ ↦ [(), ()]) fun i j p q ↦ p = 0 ∧ q = 1 ∧ j = i + 1, by decide, ?_⟩
  rintro ⟨r, hr, htier, hadj⟩
  have h₀ := htier 0 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₁ := htier 1 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₂ := htier 2 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  rcases hr.two_plus_two h₂ h₁ with h | h
  · rcases hr.two_plus_two h h₀ with h' | h'
    · exact hadj (by decide) h'
    · exact hadj (by decide) h'
  · exact hadj (by decide) h

end AR

end Autosegmental
