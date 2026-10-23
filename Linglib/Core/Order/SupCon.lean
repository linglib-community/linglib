/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Order.Hom.Lattice

/-!
# Join-semilattice congruences

`SupCon α` is an equivalence relation compatible with `⊔`, the join-only sibling of mathlib's
`LatticeCon`. The kernel of a sup-homomorphism is one. Conversely, a congruence of a
join-semilattice is cut out by the sup-homomorphisms to `Prop` whose kernels contain it: for each
`y`, the elements whose join with `y` stays in the class of `y` form an ideal, and its complement
is such a homomorphism separating `y` from everything outside that ideal. In a finite
join-semilattice the ideal is principal, so a congruence is cut out by the down-sets `Iic a` that
are unions of its classes.

## Main definitions

* `SupCon`: a congruence for `⊔`.
* `SupCon.ker`: the kernel of a sup-homomorphism.
* `SupCon.sepHom`: the sup-homomorphism to `Prop` separating `y` from the elements whose join
  with `y` leaves its class.

## Main statements

* `SupCon.r_iff_forall_le`: in a finite join-semilattice, two elements are congruent iff they lie
  in the same down-sets `Iic a` among those that are unions of classes.

`[UPSTREAM]` candidate beside `Mathlib/Order/Lattice/Congruence.lean`.
-/

@[expose] public section

variable {F α β : Type*}

variable (α) in
/-- An equivalence relation is a congruence for `⊔` if it is compatible with it. -/
structure SupCon [Max α] extends Setoid α where
  sup : ∀ {w x y z}, r w x → r y z → r (w ⊔ y) (x ⊔ z)

namespace SupCon

section Max

variable [Max α] [Max β] [FunLike F α β] [SupHomClass F α β]

open Function in
/-- The kernel of a sup-homomorphism as a congruence. -/
@[simps!]
def ker (f : F) : SupCon α where
  toSetoid := Setoid.ker f
  sup _ _ := by simp_all +instances only [Setoid.ker, onFun, map_sup]

end Max

section SemilatticeSup

variable [SemilatticeSup α] (c : SupCon α) {x y z w : α}

theorem r_sup_sup_iff : c.r (z ⊔ w ⊔ y) y ↔ c.r (z ⊔ y) y ∧ c.r (w ⊔ y) y := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hz, hw⟩ ↦ ?_⟩
  · have := c.sup h (c.iseqv.refl (z ⊔ y))
    rw [sup_eq_left.mpr (sup_le_sup_right le_sup_left y), sup_eq_right.mpr le_sup_right] at this
    exact c.iseqv.trans (c.iseqv.symm this) h
  · have := c.sup h (c.iseqv.refl (w ⊔ y))
    rw [sup_eq_left.mpr (sup_le_sup_right le_sup_right y), sup_eq_right.mpr le_sup_right] at this
    exact c.iseqv.trans (c.iseqv.symm this) h
  · simpa [← sup_sup_distrib_right] using c.sup hz hw

/-- The elements whose join with `y` leaves the class of `y`: the complement of an ideal, so a
sup-homomorphism to `Prop`. -/
def sepHom (y : α) : SupHom α Prop where
  toFun z := ¬ c.r (z ⊔ y) y
  map_sup' z w := by
    simp only [sup_Prop_eq, c.r_sup_sup_iff, not_and_or]

@[simp] theorem sepHom_apply (y z : α) : c.sepHom y z ↔ ¬ c.r (z ⊔ y) y := Iff.rfl

theorem le_ker_sepHom (y : α) : c.toSetoid ≤ Setoid.ker (c.sepHom y) := fun a b h ↦ by
  have hab := c.sup h (c.iseqv.refl y)
  refine Setoid.ker_def.mpr (propext ?_)
  exact not_congr ⟨fun h' ↦ c.iseqv.trans (c.iseqv.symm hab) h', fun h' ↦ c.iseqv.trans hab h'⟩

theorem exists_iff_le [Finite α] (y : α) : ∃ a, ∀ z, z ≤ a ↔ c.r (z ⊔ y) y := by
  classical
  have := Fintype.ofFinite α
  let s := Finset.univ.filter fun z ↦ c.r (z ⊔ y) y
  have hy : y ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, sup_idem]
    exact c.iseqv.refl y
  refine ⟨s.sup' ⟨y, hy⟩ id, fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩⟩
  · have ha : c.r (s.sup' ⟨y, hy⟩ id ⊔ y) y :=
      Finset.sup'_mem {z | c.r (z ⊔ y) y} (fun z hz w hw ↦ c.r_sup_sup_iff.mpr ⟨hz, hw⟩) s _ id
        fun z hz ↦ by simpa [s] using hz
    have := c.sup ha (c.iseqv.refl (z ⊔ y))
    rw [sup_eq_left.mpr (sup_le_sup_right hz y), sup_eq_right.mpr le_sup_right] at this
    exact c.iseqv.trans (c.iseqv.symm this) ha
  · exact Finset.le_sup' id (by simpa [s] using hz)

/-- In a finite join-semilattice, two elements are congruent iff they lie in the same down-sets
`Iic a` among those that are unions of classes. -/
theorem r_iff_forall_le [Finite α] :
    c.r x y ↔ ∀ a, (∀ z w, c.r z w → (z ≤ a ↔ w ≤ a)) → (x ≤ a ↔ y ≤ a) := by
  refine ⟨fun h a ha ↦ ha x y h, fun h ↦ ?_⟩
  have sat (y : α) :
      ∃ a, (∀ z, z ≤ a ↔ c.r (z ⊔ y) y) ∧ ∀ z w, c.r z w → (z ≤ a ↔ w ≤ a) := by
    obtain ⟨a, ha⟩ := c.exists_iff_le y
    refine ⟨a, ha, fun z w hzw ↦ ?_⟩
    rw [ha, ha, ← not_iff_not]
    exact eq_iff_iff.mp (c.le_ker_sepHom y hzw)
  obtain ⟨a, ha, hsa⟩ := sat y
  obtain ⟨b, hb, hsb⟩ := sat x
  have hy : c.r (x ⊔ y) y := (ha x).mp ((h a hsa).mpr ((ha y).mpr (by rw [sup_idem])))
  have hx : c.r (y ⊔ x) x := (hb y).mp ((h b hsb).mp ((hb x).mpr (by rw [sup_idem])))
  rw [sup_comm] at hx
  exact c.iseqv.trans (c.iseqv.symm hx) hy

end SemilatticeSup

end SupCon
