/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.List.Infix
public import Linglib.Core.Computability.PiecewiseTestable
public import Linglib.Core.Order.WellQuasiOrder

/-!
# Shuffle ideals and sublist-closed languages

The **shuffle ideal** of a word `w` is the language `{v | w <+ v}` of words containing `w` as a
subsequence, and a language is **sublist-closed** when it is downward closed under the sublist
order. Shuffle ideals are regular, and those of short words are piecewise testable. Over a
finite alphabet a sublist-closed language is the complement of finitely many shuffle ideals (by
Higman's lemma), hence piecewise testable, hence regular (Haines' theorem).

## Main definitions

* `Language.shuffleIdeal w`: the words containing `w` as a subsequence.
* `Language.IsSublistClosed L`: `L` is downward closed under `<+`.

## Main results

* `Language.isRegular_shuffleIdeal`: shuffle ideals are regular, over any alphabet.
* `Language.isPiecewiseTestable_shuffleIdeal`: the shuffle ideal of a word of length at most `k`
  is piecewise `k`-testable.
* `Language.IsSublistClosed.exists_finset_compl_eq_biSup_shuffleIdeal`: the finite forbidden
  basis.
* `Language.IsSublistClosed.exists_isPiecewiseTestable`: sublist-closed languages are piecewise
  testable.
* `Language.IsSublistClosed.isRegular`: Haines' theorem.

## References

* [higman-1952]
* [haines-1969]
-/

@[expose] public section

open List

namespace Language

variable {α : Type*} {L : Language α} {w : List α} {k : ℕ}

/-! ### Shuffle ideals -/

/-- The **shuffle ideal** of `w`: the words admitting `w` as a subsequence, the language
`Σ*a₁Σ* ⋯ aₙΣ*` over `w = a₁ ⋯ aₙ`. -/
def shuffleIdeal (w : List α) : Language α := {v | w <+ v}

@[simp] theorem mem_shuffleIdeal {v : List α} : v ∈ shuffleIdeal w ↔ w <+ v := Iff.rfl

@[simp] theorem shuffleIdeal_nil : shuffleIdeal ([] : List α) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ nil_sublist x

/-- Containing a pattern that fits in the window is piecewise testable. -/
theorem isPiecewiseTestable_shuffleIdeal (hw : w.length ≤ k) :
    (shuffleIdeal w).IsPiecewiseTestable k :=
  fun _ _ e ↦ propext (subseqSet_eq_iff e hw)

theorem isPiecewiseTestable_compl_shuffleIdeal (hw : w.length ≤ k) :
    (shuffleIdeal w)ᶜ.IsPiecewiseTestable k :=
  (isPiecewiseTestable_shuffleIdeal hw).compl

/-! ### Regularity of shuffle ideals -/

theorem leftQuotient_singleton_shuffleIdeal [DecidableEq α] (a : α) (w : List α) :
    (shuffleIdeal w).leftQuotient [a] =
      shuffleIdeal (if w.head? = some a then w.tail else w) := by
  ext v
  change w <+ a :: v ↔ _
  rcases w with _ | ⟨b, u⟩
  · exact iff_of_true (nil_sublist _) (nil_sublist _)
  · by_cases hb : b = a
    · subst hb; simp [cons_sublist_cons]
    · simp [hb, sublist_cons_iff]

theorem exists_suffix_leftQuotient_shuffleIdeal (w x : List α) :
    ∃ s, s <:+ w ∧ (shuffleIdeal w).leftQuotient x = shuffleIdeal s := by
  classical
  induction x generalizing w with
  | nil => exact ⟨w, suffix_refl w, leftQuotient_nil _⟩
  | cons a x ih =>
    obtain ⟨s, hs, e⟩ := ih (if w.head? = some a then w.tail else w)
    refine ⟨s, hs.trans ?_, ?_⟩
    · split <;> simp [tail_suffix]
    · rw [← singleton_append, leftQuotient_append, leftQuotient_singleton_shuffleIdeal, e]

/-- A shuffle ideal is **regular**: its left quotients are shuffle ideals of the finitely many
suffixes of `w`, so Myhill–Nerode applies. -/
theorem isRegular_shuffleIdeal (w : List α) : (shuffleIdeal w).IsRegular := by
  refine isRegular_iff_finite_range_leftQuotient.mpr
    ((w.tails.finite_toSet.image shuffleIdeal).subset ?_)
  rintro _ ⟨x, rfl⟩
  obtain ⟨s, hs, e⟩ := exists_suffix_leftQuotient_shuffleIdeal w x
  exact ⟨s, (mem_tails s w).mpr hs, e.symm⟩

/-! ### Sublist-closed languages -/

/-- A language is **sublist-closed** when deleting symbols never leaves it. -/
def IsSublistClosed (L : Language α) : Prop := ∀ ⦃v w : List α⦄, v <+ w → w ∈ L → v ∈ L

theorem IsSublistClosed.mem_compl_of_sublist (hL : L.IsSublistClosed) {v w : List α}
    (hvw : v <+ w) (hv : v ∈ Lᶜ) : w ∈ Lᶜ := fun hw ↦ hv (hL hvw hw)

theorem isSublistClosed_compl_shuffleIdeal (w : List α) : (shuffleIdeal w)ᶜ.IsSublistClosed :=
  fun _ _ hvw hw hm ↦ hw (hm.trans hvw)

/-- **Finite forbidden basis**: over a finite alphabet a sublist-closed language is avoidance of
finitely many forbidden subsequences, the finite-basis property of well-quasi-orders
(`WellQuasiOrdered.exists_finset_eq_biUnion`) at Higman's lemma. -/
theorem IsSublistClosed.exists_finset_compl_eq_biSup_shuffleIdeal [Finite α]
    (hL : L.IsSublistClosed) : ∃ F : Finset (List α), Lᶜ = ⨆ m ∈ F, shuffleIdeal m :=
  List.wellQuasiOrdered_sublist.exists_finset_eq_biUnion fun _ _ ↦ hL.mem_compl_of_sublist

/-- Over a finite alphabet a sublist-closed language is piecewise testable, at the length of its
longest forbidden basis word. -/
theorem IsSublistClosed.exists_isPiecewiseTestable [Finite α] (hL : L.IsSublistClosed) :
    ∃ k, L.IsPiecewiseTestable k := by
  obtain ⟨F, hF⟩ := hL.exists_finset_compl_eq_biSup_shuffleIdeal
  refine ⟨F.sup length, ?_⟩
  rw [← compl_compl L, hF]
  refine (IsPiecewiseTestable.iSup fun m ↦ IsPiecewiseTestable.iSup fun hm ↦ ?_).compl
  exact isPiecewiseTestable_shuffleIdeal (F.le_sup (f := length) hm)

/-- **Haines' theorem**: over a finite alphabet every sublist-closed language is regular. -/
theorem IsSublistClosed.isRegular [Finite α] (hL : L.IsSublistClosed) : L.IsRegular :=
  have ⟨_, h⟩ := hL.exists_isPiecewiseTestable
  h.isRegular

end Language
