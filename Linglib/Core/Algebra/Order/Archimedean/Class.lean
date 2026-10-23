/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class

/-!
# Order-connected subgroups and archimedean classes

`[UPSTREAM]` candidate for `Mathlib/Algebra/Order/Archimedean/Class.lean`. A subgroup of a
linearly ordered abelian group is order-connected, a convex subgroup, as soon as it contains
every element between zero and one of its elements. The subgroups that upper sets of archimedean
classes cut out, among them `ballAddSubgroup` and `closedBallAddSubgroup`, are order-connected.
-/

@[expose] public section

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

namespace AddSubgroup

theorem ordConnected_of_Icc_zero_subset {H : AddSubgroup G} (h : ∀ b ∈ H, Set.Icc 0 b ⊆ H) :
    (H : Set G).OrdConnected := by
  refine Set.ordConnected_of_uIcc_subset_left (x := 0) fun y hy z hz ↦ ?_
  rcases le_total 0 y with hy₀ | hy₀
  · exact h y hy (by simpa [Set.uIcc_of_le hy₀] using hz)
  · rw [Set.uIcc_of_ge hy₀] at hz
    simpa using H.neg_mem (h (-y) (H.neg_mem hy) ⟨neg_nonneg.2 hz.2, neg_le_neg hz.1⟩)

theorem exists_pos_mem_of_ne_bot {H : AddSubgroup G} (h : H ≠ ⊥) : ∃ a ∈ H, 0 < a := by
  obtain ⟨⟨a, ha⟩, hne⟩ := ne_bot_iff_exists_ne_zero.1 h
  rcases lt_or_gt_of_ne (show a ≠ 0 from fun e ↦ hne (Subtype.ext e)) with h | h
  · exact ⟨-a, H.neg_mem ha, neg_pos.2 h⟩
  · exact ⟨a, ha, h⟩

end AddSubgroup

namespace ArchimedeanClass

theorem ordConnected_addSubgroup (s : UpperSet (ArchimedeanClass G)) :
    (addSubgroup s : Set G).OrdConnected := by
  rcases eq_or_ne s ⊤ with rfl | hs
  · simp [Set.ordConnected_singleton]
  refine AddSubgroup.ordConnected_of_Icc_zero_subset fun b hb a ⟨ha, hab⟩ ↦ ?_
  rw [SetLike.mem_coe, mem_addSubgroup_iff hs] at *
  exact s.upper (mk_antitoneOn ha (ha.trans hab) hab) hb

theorem ordConnected_ballAddSubgroup (c : ArchimedeanClass G) :
    (ballAddSubgroup c : Set G).OrdConnected :=
  ordConnected_addSubgroup _

theorem ordConnected_closedBallAddSubgroup (c : ArchimedeanClass G) :
    (closedBallAddSubgroup c : Set G).OrdConnected :=
  ordConnected_addSubgroup _

end ArchimedeanClass
