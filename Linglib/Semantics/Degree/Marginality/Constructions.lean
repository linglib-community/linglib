/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Setoid.Basic
public import Linglib.Core.Algebra.Order.Archimedean.Class
public import Linglib.Semantics.Degree.Marginality.Basic

/-!
# Constructions of marginal scales

Lexicographic pairs of a block and a location within it form a marginal scale, in which two pairs
differ at most marginally when they share a block. The differences lying in an order-connected
subgroup of a linearly ordered group are the at most marginal differences of a marginal scale on
the group.

## Main definitions

* `MarginalScale.lex`: the marginal scale of lexicographic pairs.
* `MarginalScale.ofAddSubgroup`: the marginal scale of an order-connected subgroup.
* `MarginalScale.ofArchimedeanClass`: the marginal scale of an archimedean class, whose at most
  marginal differences are those of that class or a higher one.

## Main results

* `MarginalScale.isML_lex`: lexicographic pairs satisfy ML theory when there are at least two
  blocks and the locations have no least and no greatest element, as in the representative model
  `ℚ ×ₗ ℤ`.
* `MarginalScale.isML_ofAddSubgroup`: the scale of a subgroup satisfies ML theory when the
  subgroup is neither trivial nor everything.
* `MarginalScale.not_ofArchimedeanClass_largelyLT`: in an archimedean group the scale of a class
  has no large difference.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
-/

@[expose] public section

namespace MarginalScale

variable {α : Type*} [LinearOrder α] {ml : MarginalScale α} {x y z : α}

section Lex

variable (β γ : Type*) [LinearOrder β] [LinearOrder γ]

/-- Lexicographic pairs of a block and a location form a marginal scale in which two pairs differ
at most marginally when they share a block. -/
def lex : MarginalScale (β ×ₗ γ) where
  toSetoid := Setoid.ker fun p ↦ (ofLex p).1
  ordConnected' x := by
    convert (Set.ordConnected_singleton (a := (ofLex x).1)).preimage_mono
      Prod.Lex.monotone_fst_ofLex using 1
    ext
    simp [Setoid.ker_def, eq_comm]

variable {β γ}

@[simp]
theorem lex_atMostMarginal_iff {x y : β ×ₗ γ} :
    (lex β γ).AtMostMarginal x y ↔ (ofLex x).1 = (ofLex y).1 :=
  Iff.rfl

@[simp]
theorem lex_marginallyLT_iff {x y : β ×ₗ γ} :
    (lex β γ).MarginallyLT x y ↔ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2 := by
  rw [MarginallyLT, lex_atMostMarginal_iff]
  grind [Prod.Lex.lt_iff]

@[simp]
theorem lex_largelyLT_iff {x y : β ×ₗ γ} : (lex β γ).LargelyLT x y ↔ (ofLex x).1 < (ofLex y).1 := by
  rw [largelyLT_iff_lt_and_not_atMostMarginal, lex_atMostMarginal_iff]
  grind [Prod.Lex.lt_iff]

/-- Lexicographic pairs satisfy ML theory when there are at least two blocks and the locations
have no least and no greatest element. -/
theorem isML_lex [Nontrivial β] [Nonempty γ] [NoMaxOrder γ] [NoMinOrder γ] : (lex β γ).IsML :=
  isML_iff.2
    ⟨let ⟨a, b, hab⟩ := exists_pair_ne β
      let ⟨c⟩ := ‹Nonempty γ›
      ⟨toLex (a, c), toLex (b, c), hab⟩,
    fun x _ _ _ ↦
      let ⟨c, hc⟩ := exists_gt (ofLex x).2
      ⟨toLex ((ofLex x).1, c), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hc⟩), rfl⟩,
    fun _ y _ _ ↦
      let ⟨d, hd⟩ := exists_lt (ofLex y).2
      ⟨toLex ((ofLex y).1, d), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hd⟩), rfl⟩⟩

end Lex

section AddSubgroup

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  {H : AddSubgroup G} {hconv : (H : Set G).OrdConnected} {x y : G}

/-- The differences lying in an order-connected subgroup are the at most marginal differences of
a marginal scale. -/
def ofAddSubgroup (H : AddSubgroup G) (hconv : (H : Set G).OrdConnected) : MarginalScale G where
  toSetoid := QuotientAddGroup.leftRel H
  ordConnected' x := by
    simp only [QuotientAddGroup.leftRel_apply]
    exact hconv.preimage_mono (f := fun y ↦ -x + y) fun _ _ h ↦ by simpa using h

theorem ofAddSubgroup_atMostMarginal_iff :
    (ofAddSubgroup H hconv).AtMostMarginal x y ↔ y - x ∈ H := by
  rw [← neg_add_eq_sub, ← QuotientAddGroup.leftRel_apply]
  rfl

theorem ofAddSubgroup_marginallyLT_iff :
    (ofAddSubgroup H hconv).MarginallyLT x y ↔ x < y ∧ y - x ∈ H := by
  rw [MarginallyLT, ofAddSubgroup_atMostMarginal_iff]

/-- The scale of an order-connected subgroup satisfies ML theory when the subgroup is neither
trivial nor everything. -/
theorem isML_ofAddSubgroup (hbot : H ≠ ⊥) (htop : H ≠ ⊤) : (ofAddSubgroup H hconv).IsML := by
  obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
  refine isML_iff.2 ⟨?_, fun x _ _ _ ↦ ⟨x + h, by simpa using hpos, ?_⟩,
    fun _ y _ _ ↦ ⟨y - h, by simpa using hpos, ?_⟩⟩
  · obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
      by_contra! h
      exact htop (eq_top_iff.2 fun g _ ↦ h g)
    exact ⟨0, g, by simpa [ofAddSubgroup_atMostMarginal_iff] using hg⟩
  · simpa [ofAddSubgroup_atMostMarginal_iff] using hH
  · simpa [ofAddSubgroup_atMostMarginal_iff] using hH

/-- The scale of an archimedean class `A` of a linearly ordered group: two elements differ at most
marginally when the class of their difference is at least `A`. -/
noncomputable def ofArchimedeanClass (A : ArchimedeanClass G) : MarginalScale G :=
  ofAddSubgroup (ArchimedeanClass.closedBallAddSubgroup A)
    (ArchimedeanClass.ordConnected_closedBallAddSubgroup A)

theorem ofArchimedeanClass_atMostMarginal_iff {A : ArchimedeanClass G} :
    (ofArchimedeanClass A).AtMostMarginal x y ↔ A ≤ ArchimedeanClass.mk (y - x) :=
  ofAddSubgroup_atMostMarginal_iff.trans ArchimedeanClass.mem_closedBallAddSubgroup_iff

theorem ofArchimedeanClass_largelyLT_iff {A : ArchimedeanClass G} :
    (ofArchimedeanClass A).LargelyLT x y ↔ x < y ∧ ArchimedeanClass.mk (y - x) < A := by
  rw [largelyLT_iff_lt_and_not_atMostMarginal, ofArchimedeanClass_atMostMarginal_iff, not_le]

/-- In an archimedean group no difference is large in the scale of the class of a nonzero
element. -/
theorem not_ofArchimedeanClass_largelyLT [Archimedean G] {d : G} (hd : d ≠ 0) :
    ¬ (ofArchimedeanClass (ArchimedeanClass.mk d)).LargelyLT x y := fun h ↦
  have ⟨hxy, hlt⟩ := ofArchimedeanClass_largelyLT_iff.1 h
  hlt.ne (ArchimedeanClass.mk_eq_mk_of_archimedean (sub_pos.2 hxy).ne' hd)

end AddSubgroup

end MarginalScale
