/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Cover
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.UpperLower.Basic

/-!
# Covers

`[UPSTREAM]` In a linear order the greatest element strictly below `b` is the one `b` covers, and a
lower set has greatest element `a` exactly when it contains `a` and not the element covering it. A
list in which each element is weakly covered by the next moves up a linear order one step at a
time, so it cannot pass over a value. An element is branching when two elements cover it, and a
finite order whose non-maximal elements all branch [has a cherry](##exists_cherry).
-/

public section

variable {α : Type*}

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

/-- The greatest element strictly below `b` is the one that `b` covers. -/
theorem isGreatest_Iio_iff_covBy : IsGreatest (Set.Iio b) a ↔ a ⋖ b :=
  ⟨fun h ↦ ⟨h.1, fun _ hac hcb ↦ hac.not_ge (h.2 hcb)⟩, fun h ↦ ⟨h.lt, fun _ hc ↦ h.le_of_lt hc⟩⟩

/-- The least element strictly above `a` is the one that covers `a`. -/
theorem isLeast_Ioi_iff_covBy : IsLeast (Set.Ioi a) b ↔ a ⋖ b :=
  ⟨fun h ↦ ⟨h.1, fun _ hac hcb ↦ hcb.not_ge (h.2 hac)⟩, fun h ↦ ⟨h.lt, fun _ hc ↦ h.ge_of_gt hc⟩⟩

/-- A lower set has greatest element `a` exactly when it contains `a` and not the element
covering `a`. -/
theorem IsLowerSet.isGreatest_iff_of_covBy (hs : IsLowerSet s) (h : a ⋖ b) :
    IsGreatest s a ↔ a ∈ s ∧ b ∉ s :=
  ⟨fun hg ↦ ⟨hg.1, fun hb ↦ h.lt.not_ge (hg.2 hb)⟩,
    fun ⟨ha, hb⟩ ↦ ⟨ha, fun _ hc ↦ not_lt.1 fun hac ↦ hb (hs (h.ge_of_gt hac) hc)⟩⟩

end LinearOrder

/-- A chain of weak covers that starts at or below `x` and reaches an element at or above `x`
contains `x`. -/
theorem List.IsChain.mem_of_le_of_le [LinearOrder α] {x m : α} :
    ∀ {a : α} {l : List α}, (a :: l).IsChain (· ⩿ ·) → a ≤ x → m ∈ a :: l → x ≤ m → x ∈ a :: l
  | a, [], _, hax, hm, hxm => by
    obtain rfl := List.mem_singleton.1 hm
    exact List.mem_singleton.2 (le_antisymm hxm hax)
  | a, b :: l, hc, hax, hm, hxm => by
    rw [List.isChain_cons_cons] at hc
    rcases hax.eq_or_lt with rfl | hlt
    · exact List.mem_cons_self
    · rcases List.mem_cons.1 hm with rfl | hm'
      · exact absurd (hlt.trans_le hxm) (lt_irrefl _)
      · exact List.mem_cons_of_mem _
          (mem_of_le_of_le hc.2 (not_lt.1 fun hxb ↦ hc.1.2 hlt hxb) hm' hxm)

/-! ### Branching

A node branches when it has two daughters. In a finite order in which every node with a daughter
branches, a topmost node with daughters has only maximal daughters, so some node has two maximal
daughters, a cherry in the language of phylogenetic trees. -/

section Branching

variable {M : Type*} [PartialOrder M]

/-- A node is branching when it has at least two covers. -/
@[expose] def IsBranching (x : M) : Prop := {a | x ⋖ a}.Nontrivial

/-- In a finite order in which every non-maximal node branches, a non-maximal node yields a node
covered by two distinct maximal ones. -/
theorem exists_cherry [Finite M] (hb : ∀ x : M, ¬ IsMax x → IsBranching x) {x : M}
    (hx : ¬ IsMax x) : ∃ m a b : M, m ⋖ a ∧ m ⋖ b ∧ a ≠ b ∧ IsMax a ∧ IsMax b := by
  obtain ⟨m, hm, hmax⟩ := (Set.toFinite {y : M | ¬ IsMax y}).exists_maximal ⟨x, hx⟩
  obtain ⟨a, ha, b, hb', hab⟩ := hb m hm
  have key : ∀ c, m ⋖ c → IsMax c := fun c hc ↦ of_not_not fun h ↦ hc.lt.not_ge (hmax h hc.le)
  exact ⟨m, a, b, ha, hb', hab, key a ha, key b hb'⟩

end Branching
