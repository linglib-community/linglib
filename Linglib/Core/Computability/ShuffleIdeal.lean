/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Nat.Find
public import Linglib.Core.Order.WellQuasiOrder

/-!
# Shuffle ideals and sublist-closed languages

The **shuffle ideal** of a word `w` is the language `{v | w <+ v}` of words containing `w` as a
subsequence, and a language is **sublist-closed** when it is downward closed under the sublist
order. This file proves that shuffle ideals are regular, and that over a finite alphabet a
sublist-closed language is the complement of finitely many shuffle ideals (by Higman's lemma)
and hence regular (Haines' theorem).

## Main definitions

* `Language.shuffleIdeal w`: the words containing `w` as a subsequence.
* `Language.IsSublistClosed L`: `L` is downward closed under `<+`.
* `List.maxMatch w x`: the length of the longest prefix of `w` occurring as a subsequence of `x`.

## Main results

* `Language.isRegular_shuffleIdeal`: shuffle ideals are regular.
* `Language.IsSublistClosed.exists_finset_compl_eq_biSup_shuffleIdeal`: the finite forbidden
  basis.
* `Language.IsSublistClosed.isRegular`: Haines' theorem.

## References

* [higman-1952]
* [haines-1969]
-/

@[expose] public section

open List

variable {α : Type*}

namespace Language

variable {L : Language α} {w : List α}

/-! ### Shuffle ideals and sublist-closed languages -/

/-- The **shuffle ideal** of `w`: the words admitting `w` as a subsequence, the language
`Σ*a₁Σ* ⋯ aₙΣ*` over `w = a₁ ⋯ aₙ`. -/
def shuffleIdeal (w : List α) : Language α := {v | w <+ v}

@[simp] theorem mem_shuffleIdeal {v : List α} : v ∈ shuffleIdeal w ↔ w <+ v := Iff.rfl

@[simp] theorem shuffleIdeal_nil : shuffleIdeal ([] : List α) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ nil_sublist x

/-- A language is **sublist-closed** when deleting symbols never leaves it. -/
def IsSublistClosed (L : Language α) : Prop := ∀ ⦃v w : List α⦄, v <+ w → w ∈ L → v ∈ L

theorem IsSublistClosed.mem_compl_of_sublist (hL : L.IsSublistClosed) {v w : List α}
    (hvw : v <+ w) (hv : v ∈ Lᶜ) : w ∈ Lᶜ := fun hw ↦ hv (hL hvw hw)

theorem isSublistClosed_compl_shuffleIdeal (w : List α) : (shuffleIdeal w)ᶜ.IsSublistClosed :=
  fun _ _ hvw hw hm ↦ hw (hm.trans hvw)

end Language

/-! ### Greedy matching -/

namespace List

variable [DecidableEq α]

/-- The length of the longest prefix of `w` occurring as a subsequence of `x`. -/
def maxMatch (w x : List α) : ℕ := Nat.findGreatest (fun m ↦ w.take m <+ x) w.length

theorem maxMatch_le (w x : List α) : maxMatch w x ≤ w.length := Nat.findGreatest_le _

theorem take_maxMatch_sublist (w x : List α) : w.take (maxMatch w x) <+ x :=
  Nat.findGreatest_spec (P := fun m ↦ w.take m <+ x) (Nat.zero_le _) (by simp)

theorem le_maxMatch {w x : List α} {j : ℕ} (hj : j ≤ w.length) (h : w.take j <+ x) :
    j ≤ maxMatch w x := Nat.le_findGreatest hj h

/-- **Greedy matching is optimal**: `w` scatters into `x ++ v` exactly when the part of `w` left
over after its longest `x`-matchable prefix scatters into `v`. -/
theorem sublist_append_iff_drop_maxMatch (w x v : List α) :
    w <+ x ++ v ↔ w.drop (maxMatch w x) <+ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := sublist_append_iff.mp h
    have hj : l₁.length ≤ maxMatch (l₁ ++ l₂) x :=
      le_maxMatch (by simp) (by rw [take_left]; exact h₁)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, ← drop_drop, drop_left]
    exact (drop_sublist _ _).trans h₂
  · have := (take_maxMatch_sublist w x).append h
    rwa [take_append_drop] at this

end List

namespace Language

variable {L : Language α}

/-! ### Regularity of shuffle ideals -/

theorem leftQuotient_shuffleIdeal [DecidableEq α] (w x : List α) :
    (shuffleIdeal w).leftQuotient x = shuffleIdeal (w.drop (w.maxMatch x)) :=
  Set.ext (sublist_append_iff_drop_maxMatch w x)

/-- A shuffle ideal is **regular**: its left quotients are the shuffle ideals of the suffixes of
`w`, of which there are at most `|w| + 1`, so Myhill–Nerode applies. -/
theorem isRegular_shuffleIdeal (w : List α) : (shuffleIdeal w).IsRegular := by
  classical
  refine isRegular_iff_finite_range_leftQuotient.mpr (Set.Finite.subset
    (Set.finite_range fun j : Fin (w.length + 1) ↦ shuffleIdeal (w.drop j)) ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨w.maxMatch x, Nat.lt_succ_of_le (w.maxMatch_le x)⟩, (leftQuotient_shuffleIdeal w x).symm⟩

/-! ### Haines' theorem -/

/-- **Finite forbidden basis**: over a finite alphabet a sublist-closed language is avoidance of
finitely many forbidden subsequences, the finite-basis property of well-quasi-orders
(`WellQuasiOrdered.exists_finset_eq_biUnion`) at Higman's lemma. -/
theorem IsSublistClosed.exists_finset_compl_eq_biSup_shuffleIdeal [Finite α]
    (hL : L.IsSublistClosed) : ∃ F : Finset (List α), Lᶜ = ⨆ m ∈ F, shuffleIdeal m :=
  List.wellQuasiOrdered_sublist.exists_finset_eq_biUnion fun _ _ ↦ hL.mem_compl_of_sublist

theorem isRegular_bot : (⊥ : Language α).IsRegular :=
  ⟨Unit, inferInstance, ⟨fun _ _ ↦ (), (), ∅⟩, rfl⟩

theorem isRegular_biSup_finset {ι : Type*} {F : Finset ι} {f : ι → Language α}
    (hf : ∀ i ∈ F, (f i).IsRegular) : (⨆ i ∈ F, f i).IsRegular := by
  classical
  induction F using Finset.induction with
  | empty => simpa using isRegular_bot
  | insert i _ _ ih =>
    rw [Finset.iSup_insert]
    exact (hf i (by simp)).add (ih fun j hj ↦ hf j (by simp [hj]))

/-- **Haines' theorem**: over a finite alphabet every sublist-closed language is regular, being
the complement of the union of the shuffle ideals of finitely many forbidden subsequences. -/
theorem IsSublistClosed.isRegular [Finite α] (hL : L.IsSublistClosed) : L.IsRegular :=
  have ⟨_, hF⟩ := hL.exists_finset_compl_eq_biSup_shuffleIdeal
  (hF ▸ isRegular_biSup_finset fun m _ ↦ isRegular_shuffleIdeal m).of_compl

end Language
