/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Finite.List
public import Linglib.Core.Computability.ShuffleIdeal
public import Linglib.Core.Computability.StarFree

/-!
# Piecewise testable languages

A language is *piecewise `k`-testable* when membership of a word depends only on the set of its
subsequences of length at most `k`. These are the piecewise testable events of Simon.

## Main definitions

* `subseqSet k w`: the subsequences of `w` of length at most `k`.
* `Language.IsPiecewiseTestable`: membership in the language factors through `subseqSet k`.

## Main results

* `subseqSet_append_congr`: words with the same subsequences of length at most `k` still have the
  same ones after concatenation.
* `subseqSet_flatten_replicate_succ`: `k + 1` copies of a word have the same subsequences of
  length at most `k` as `k` copies.
* `Language.isPiecewiseTestable_shuffleIdeal`: the shuffle ideal of a word of length at most `k`
  is piecewise `k`-testable.
* `Language.IsPiecewiseTestable.isStarFree`: over a finite alphabet, piecewise testable languages
  are star-free.

## References

* [simon-1975]
-/

@[expose] public section

open List

variable {α : Type*}

/-- The subsequences of `w` of length at most `k`. The bound is at most `k`, not exactly `k`, so
that words shorter than `k` stay distinguishable. -/
def subseqSet (k : ℕ) (w : List α) : Set (List α) :=
  { s | s <+ w ∧ s.length ≤ k }

@[simp] lemma mem_subseqSet {k : ℕ} {s w : List α} :
    s ∈ subseqSet k w ↔ s <+ w ∧ s.length ≤ k :=
  Iff.rfl

/-- Words with the same `subseqSet k` have the same subsequences of length at most `k`. -/
lemma subseqSet_eq_iff {k : ℕ} {w₁ w₂ : List α}
    (heq : subseqSet k w₁ = subseqSet k w₂) {s : List α} (hlen : s.length ≤ k) :
    s <+ w₁ ↔ s <+ w₂ := by
  simpa [hlen] using Set.ext_iff.mp heq s

/-- Sharing `subseqSet k` is preserved by concatenation, since a subsequence of `u ++ v` splits
as a subsequence of `u` followed by one of `v`. -/
theorem subseqSet_append_congr {k : ℕ} {u₁ u₂ v₁ v₂ : List α}
    (hu : subseqSet k u₁ = subseqSet k u₂) (hv : subseqSet k v₁ = subseqSet k v₂) :
    subseqSet k (u₁ ++ v₁) = subseqSet k (u₂ ++ v₂) := by
  have aux : ∀ {u₁ u₂ v₁ v₂ : List α}, subseqSet k u₁ = subseqSet k u₂ →
      subseqSet k v₁ = subseqSet k v₂ →
      subseqSet k (u₁ ++ v₁) ⊆ subseqSet k (u₂ ++ v₂) := by
    rintro u₁ u₂ v₁ v₂ hu hv s ⟨hsub, hlen⟩
    obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := sublist_append_iff.mp hsub
    rw [length_append] at hlen
    exact ⟨((subseqSet_eq_iff hu (by omega)).mp h₁).append
      ((subseqSet_eq_iff hv (by omega)).mp h₂), by simp [length_append]; omega⟩
  exact Set.Subset.antisymm (aux hu hv) (aux hu.symm hv.symm)

/-- A subsequence of `m + 1` copies of `w` that is no longer than `m` misses one of the copies, so
it is a subsequence of `m` copies. -/
theorem List.sublist_flatten_replicate_of_length_le {w : List α} :
    ∀ {m : ℕ} {s : List α}, s.length ≤ m → s <+ (replicate (m + 1) w).flatten →
      s <+ (replicate m w).flatten
  | 0, s, hs, _ => by simp [length_eq_zero_iff.mp (Nat.le_zero.mp hs)]
  | m + 1, s, hs, h => by
    rw [replicate_succ, flatten_cons] at h ⊢
    obtain ⟨s₁, s₂, rfl, h₁, h₂⟩ := sublist_append_iff.mp h
    rcases s₁ with _ | ⟨a, s₁⟩
    · exact h₂
    · exact h₁.append (sublist_flatten_replicate_of_length_le
        (by simp only [length_append, length_cons] at hs; omega) h₂)

/-- `k + 1` copies of a word have the same subsequences of length at most `k` as `k` copies. -/
theorem subseqSet_flatten_replicate_succ (k : ℕ) (w : List α) :
    subseqSet k (replicate (k + 1) w).flatten = subseqSet k (replicate k w).flatten :=
  Set.ext fun _ ↦ ⟨fun h ↦ ⟨sublist_flatten_replicate_of_length_le h.2 h.1, h.2⟩,
    fun h ↦ ⟨h.1.trans (by simp [replicate_succ]), h.2⟩⟩

/-- Over a finite alphabet `subseqSet k` takes finitely many values. -/
theorem finite_range_subseqSet [Finite α] (k : ℕ) :
    (Set.range (subseqSet (α := α) k)).Finite :=
  ((List.finite_length_le α k).finite_subsets).subset
    (by rintro _ ⟨w, rfl⟩; exact fun s hs ↦ hs.2)

namespace Language

/-- A language is *piecewise `k`-testable* when membership factors through the set `subseqSet k`
of subsequences of length at most `k`. -/
def IsPiecewiseTestable (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (subseqSet k)

variable {L M : Language α} {k : ℕ}

theorem IsPiecewiseTestable.compl (h : L.IsPiecewiseTestable k) : Lᶜ.IsPiecewiseTestable k :=
  fun _ _ e ↦ congrArg Not (h e)

theorem IsPiecewiseTestable.inter (hL : L.IsPiecewiseTestable k)
    (hM : M.IsPiecewiseTestable k) : (L ⊓ M).IsPiecewiseTestable k :=
  fun _ _ e ↦ congrArg₂ And (hL e) (hM e)

theorem IsPiecewiseTestable.union (hL : L.IsPiecewiseTestable k)
    (hM : M.IsPiecewiseTestable k) : (L ⊔ M).IsPiecewiseTestable k :=
  fun _ _ e ↦ congrArg₂ Or (hL e) (hM e)

/-- Containing a pattern that fits in the window is piecewise testable. -/
theorem isPiecewiseTestable_shuffleIdeal {p : List α} (hp : p.length ≤ k) :
    (shuffleIdeal p).IsPiecewiseTestable k :=
  fun _ _ e ↦ propext (subseqSet_eq_iff e hp)

/-- Avoiding a pattern that fits in the window is piecewise testable. -/
theorem isPiecewiseTestable_compl_shuffleIdeal {p : List α} (hp : p.length ≤ k) :
    (shuffleIdeal p)ᶜ.IsPiecewiseTestable k :=
  (isPiecewiseTestable_shuffleIdeal hp).compl

/-- Over a finite alphabet piecewise testable languages are star-free. -/
theorem IsPiecewiseTestable.isStarFree [Finite α] (h : L.IsPiecewiseTestable k) : L.IsStarFree :=
  .of_factorsThrough h (fun _ _ _ _ ↦ subseqSet_append_congr) (finite_range_subseqSet k)
    (subseqSet_flatten_replicate_succ k)

theorem IsPiecewiseTestable.isRegular [Finite α] (h : L.IsPiecewiseTestable k) : L.IsRegular :=
  h.isStarFree.isRegular

end Language
