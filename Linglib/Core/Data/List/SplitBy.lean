/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.SplitBy

/-!
# Refining `List.splitBy`

`Mathlib/Data/List/SplitBy.lean` characterizes `List.splitBy` (`List.splitBy_eq_iff`) but has no
lemma comparing the splittings by two relations. When `r` implies `s`, every run of `r` lies in a
run of `s`, so splitting by `s` and then splitting each run by `r` splits by `r`. [UPSTREAM]
candidate for that file.

## Main results

* `List.flatMap_splitBy_splitBy`: splitting by a coarser relation and then by a finer one
  splits by the finer one.
-/

@[expose] public section

namespace List

variable {α : Type*} {r s : α → α → Bool}

/-- Splitting by a coarser relation and then by a finer one splits by the finer one. -/
theorem flatMap_splitBy_splitBy (h : ∀ x y, r x y → s x y) (l : List α) :
    (l.splitBy s).flatMap (splitBy r) = l.splitBy r := by
  symm
  rw [splitBy_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [flatMap, flatten_flatten, map_map]
    simp [Function.comp_def, flatten_splitBy]
  · simp only [mem_flatMap, not_exists, not_and]
    exact fun g _ ↦ nil_notMem_splitBy r g
  · simp only [mem_flatMap, forall_exists_index, and_imp]
    exact fun m g _ hm ↦ isChain_of_mem_splitBy hm
  · rw [flatMap, isChain_flatten (by simp [nil_notMem_splitBy])]
    refine ⟨by simpa using fun g _ ↦ isChain_getLast_head_splitBy r g, ?_⟩
    rw [isChain_map]
    refine (isChain_getLast_head_splitBy s l).imp fun g₁ g₂ ⟨h₁, h₂, hs⟩ ↦ ?_
    intro a ha b hb
    refine ⟨ne_nil_of_mem_splitBy (mem_of_mem_getLast? ha),
      ne_nil_of_mem_splitBy (mem_of_mem_head? hb), ?_⟩
    simp_rw [← getLast_of_mem_getLast? ha, getLast_getLast_splitBy _ h₁, ← head_of_mem_head? hb,
      head_head_splitBy _ h₂]
    exact Bool.eq_false_iff.2 fun hr ↦ by simp [h _ _ hr] at hs

end List
