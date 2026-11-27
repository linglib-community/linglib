/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Sonority.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Sonority sequencing

For a scale `σ : α → β` and a string `l : List α`, sonority peaks at position `n` when `σ` is
strictly increasing on the positions up to `n` and strictly decreasing on the positions from `n`
on (`Phonology.Sonority.PeaksAt`). A string is sequenced when sonority peaks at one of its
positions (`Phonology.Sonority.Sequenced`). This is the sonority sequencing principle for the
segments of a syllable: one peak of sonority, with a slope that rises to it on one side and falls
from it on the other.

A string has at most one position at which sonority peaks (`PeaksAt.unique`), and no value of the
string exceeds the value there (`PeaksAt.le_peak`). On a string of two segments, sonority peaks at
the second when it rises and at the first when it falls.

## Implementation notes

The slopes are strict, so a string with two adjacent segments of equal sonority is not sequenced.
The definition takes a string and not a syllable, and says nothing of which position is the
nucleus.

## References

* [parker-2002]
* [clements-1990]
* [selkirk-1984]
-/

@[expose] public section

namespace Phonology.Sonority

variable {α β : Type*} [Preorder β] {σ : α → β} {l : List α} {m n : ℕ}

/-- Sonority peaks at position `n` of a string when the scale is strictly increasing on the
positions up to `n` and strictly decreasing on the positions from `n` on. -/
def PeaksAt (σ : α → β) (l : List α) (n : ℕ) : Prop :=
  StrictMonoOn (fun i : Fin l.length ↦ σ l[i]) {i | i ≤ n} ∧
    StrictAntiOn (fun i : Fin l.length ↦ σ l[i]) {i | n ≤ i}

/-- A string is sequenced when sonority peaks at one of its positions. -/
def Sequenced (σ : α → β) (l : List α) : Prop := ∃ n : Fin l.length, PeaksAt σ l n

instance [DecidableLT β] : Decidable (PeaksAt σ l n) := by
  unfold PeaksAt StrictMonoOn StrictAntiOn
  infer_instance

instance [DecidableLT β] : Decidable (Sequenced σ l) := by
  unfold Sequenced
  infer_instance

theorem PeaksAt.lt_of_lt_of_le (h : PeaksAt σ l n) {i j : Fin l.length} (hij : i < j)
    (hjn : j ≤ n) : σ l[i] < σ l[j] :=
  h.1 (show i.val ≤ n from (Nat.le_of_lt hij).trans hjn) hjn hij

theorem PeaksAt.lt_of_le_of_lt (h : PeaksAt σ l n) {i j : Fin l.length} (hni : n ≤ i)
    (hij : i < j) : σ l[j] < σ l[i] :=
  h.2 hni (show n ≤ j.val from hni.trans (Nat.le_of_lt hij)) hij

/-- Sonority peaks at no more than one position of a string. -/
theorem PeaksAt.unique (hm : PeaksAt σ l m) (hn : PeaksAt σ l n) (hml : m < l.length)
    (hnl : n < l.length) : m = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact lt_asymm (hn.lt_of_lt_of_le (i := ⟨m, hml⟩) (j := ⟨n, hnl⟩) h le_rfl)
      (hm.lt_of_le_of_lt (i := ⟨m, hml⟩) (j := ⟨n, hnl⟩) le_rfl h)
  · exact lt_asymm (hm.lt_of_lt_of_le (i := ⟨n, hnl⟩) (j := ⟨m, hml⟩) h le_rfl)
      (hn.lt_of_le_of_lt (i := ⟨n, hnl⟩) (j := ⟨m, hml⟩) le_rfl h)

/-- No segment of a string is more sonorous than the one at which sonority peaks. -/
theorem PeaksAt.le_peak (h : PeaksAt σ l n) (hnl : n < l.length) (i : Fin l.length) :
    σ l[i] ≤ σ l[n] := by
  rcases lt_trichotomy i.val n with hi | hi | hi
  · exact (h.lt_of_lt_of_le (j := ⟨n, hnl⟩) hi le_rfl).le
  · subst hi; exact le_rfl
  · exact (h.lt_of_le_of_lt (i := ⟨n, hnl⟩) le_rfl hi).le

theorem peaksAt_pair_one {a b : α} : PeaksAt σ [a, b] 1 ↔ σ a < σ b := by
  simp [PeaksAt, StrictMonoOn, StrictAntiOn, Fin.forall_fin_two]

theorem peaksAt_pair_zero {a b : α} : PeaksAt σ [a, b] 0 ↔ σ b < σ a := by
  simp [PeaksAt, StrictMonoOn, StrictAntiOn, Fin.forall_fin_two]

end Phonology.Sonority
