/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Order.Comparable

/-!
# Strictly monotone maps into ordered groups detect `≤`

`[UPSTREAM]` candidate for `Mathlib/Algebra/Order/Group/Indicator.lean`.

The indicator of an upper set is monotone wherever the function is monotone and nonnegative. Adding
a large constant on `Set.Ici a` to a strictly monotone map into a nontrivial linearly ordered
additive group therefore keeps it strictly monotone, so for a partial order `α`, `a ≤ b` [fails
exactly when some strictly monotone map puts `a` above
`b`](##StrictMono.not_le_iff_exists_strictMono_lt), and two elements are [incomparable exactly
when strictly monotone maps order them both ways](##StrictMono.incompRel_iff_exists_strictMono).
-/

public section

open Set

section Indicator

variable {α M : Type*} [Preorder α] [Preorder M] [One M] {s : Set α} {f : α → M}

/-- The indicator of an upper set is monotone where the function is monotone and at least `1`. -/
@[to_additive /-- The indicator of an upper set is monotone where the function is monotone and
nonnegative. -/]
theorem IsUpperSet.monotone_mulIndicator (hs : IsUpperSet s) (hf : Monotone f)
    (h1 : ∀ x ∈ s, 1 ≤ f x) : Monotone (s.mulIndicator f) := fun _ y hxy ↦
  mulIndicator_apply_le' (fun hx ↦ (hf hxy).trans_eq (mulIndicator_of_mem (hs hxy hx) f).symm)
    fun _ ↦ one_le_mulIndicator h1 y

end Indicator

variable {α β : Type*} [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Nontrivial β]
  {f : α → β} {a b : α}

/-- Given one strictly monotone map into a nontrivial linearly ordered additive group, some
strictly monotone map puts `a` above any `b` with `¬ a ≤ b`. -/
theorem StrictMono.exists_strictMono_lt_of_not_ge [Preorder α] (hf : StrictMono f)
    (hab : ¬ a ≤ b) : ∃ g : α → β, StrictMono g ∧ g b < g a := by
  obtain ⟨c, hc⟩ := exists_gt (max 0 (f b - f a))
  rw [max_lt_iff, sub_lt_iff_lt_add'] at hc
  refine ⟨f + (Ici a).indicator fun _ ↦ c, hf.add_monotone <|
    IsUpperSet.monotone_indicator (fun _ _ h hx ↦ le_trans hx h) monotone_const
      fun _ _ ↦ hc.1.le, ?_⟩
  simpa [indicator_apply, hab] using hc.2

/-- For a partial order `α` with a strictly monotone map into a nontrivial linearly ordered
additive group, `a ≤ b` fails iff some strictly monotone map puts `a` above `b`. -/
theorem StrictMono.not_le_iff_exists_strictMono_lt [PartialOrder α] (hf : StrictMono f) :
    ¬ a ≤ b ↔ ∃ g : α → β, StrictMono g ∧ g b < g a :=
  ⟨hf.exists_strictMono_lt_of_not_ge, fun ⟨_, hg, hlt⟩ hab ↦ (hg.monotone hab).not_gt hlt⟩

/-- For a partial order `α` with a strictly monotone map into a nontrivial linearly ordered
additive group, `a` and `b` are incomparable iff strictly monotone maps order them both ways. -/
theorem StrictMono.incompRel_iff_exists_strictMono [PartialOrder α] (hf : StrictMono f) :
    IncompRel (· ≤ ·) a b ↔
      (∃ g : α → β, StrictMono g ∧ g a < g b) ∧ ∃ g : α → β, StrictMono g ∧ g b < g a :=
  and_comm.trans <| and_congr hf.not_le_iff_exists_strictMono_lt hf.not_le_iff_exists_strictMono_lt
