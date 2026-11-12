module

public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# The unit-interval involution

`[UPSTREAM]` additions to `Mathlib.Algebra.Order.Interval.Set.Instances`: the
involution `1 - t` of `Set.Icc (0 : β) 1` and its lemmas, stated at that file's
generality — generalizing `unitInterval.symm` beyond `ℝ` is its stated TODO. The involution is
[an order isomorphism onto the dual](##Set.Icc.symmOrderIso), from which its order lemmas follow.

Linglib uses `Set.Icc (0 : ℚ) 1` as the home of gradient linguistic degrees
(at-issueness, projectivity, prior credence): mathlib's `unitInterval` is
real-valued and topological, while linguistic degrees are exact rationals.
-/

@[expose] public section

namespace Set.Icc

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

/-- The involution `1 - t` of the unit interval — `unitInterval.symm` at the
    generality of this file's instances. -/
def symm (t : Icc (0 : β) 1) : Icc (0 : β) 1 :=
  ⟨1 - t, mem_iff_one_sub_mem.mp t.prop⟩

@[simp, grind =] theorem coe_symm_eq (t : Icc (0 : β) 1) : (symm t : β) = 1 - t := rfl

@[simp, grind =] theorem symm_symm (t : Icc (0 : β) 1) : symm (symm t) = t :=
  Subtype.ext (by simp)

@[simp, grind =] theorem symm_zero : symm (0 : Icc (0 : β) 1) = 1 := Subtype.ext (by simp)

@[simp, grind =] theorem symm_one : symm (1 : Icc (0 : β) 1) = 0 := Subtype.ext (by simp)

theorem symm_involutive : Function.Involutive (symm : Icc (0 : β) 1 → Icc (0 : β) 1) :=
  symm_symm

theorem symm_bijective : Function.Bijective (symm : Icc (0 : β) 1 → Icc (0 : β) 1) :=
  symm_involutive.bijective

theorem symm_inj {s t : Icc (0 : β) 1} : symm s = symm t ↔ s = t :=
  symm_bijective.injective.eq_iff

theorem symm_eq_one {t : Icc (0 : β) 1} : symm t = 1 ↔ t = 0 := by
  rw [← symm_zero, symm_inj]

theorem symm_eq_zero {t : Icc (0 : β) 1} : symm t = 0 ↔ t = 1 := by
  rw [← symm_one, symm_inj]

theorem symm_le_symm {s t : Icc (0 : β) 1} : symm s ≤ symm t ↔ t ≤ s := by
  simp only [symm, Subtype.mk_le_mk, sub_le_sub_iff_left, Subtype.coe_le_coe]

/-- The involution `1 - t` of the unit interval as an order isomorphism onto the order dual. -/
def symmOrderIso : Icc (0 : β) 1 ≃o (Icc (0 : β) 1)ᵒᵈ where
  toEquiv := (symm_involutive.toPerm _).trans OrderDual.toDual
  map_rel_iff' := symm_le_symm

@[simp] theorem symmOrderIso_apply (t : Icc (0 : β) 1) :
    symmOrderIso t = OrderDual.toDual (symm t) := rfl

@[simp] theorem symmOrderIso_symm_apply (t : (Icc (0 : β) 1)ᵒᵈ) :
    symmOrderIso.symm t = symm (OrderDual.ofDual t) := rfl

theorem le_symm_comm {s t : Icc (0 : β) 1} : s ≤ symm t ↔ t ≤ symm s := by
  rw [← symm_le_symm, symm_symm]

theorem symm_le_comm {s t : Icc (0 : β) 1} : symm s ≤ t ↔ symm t ≤ s := by
  rw [← symm_le_symm, symm_symm]

theorem symm_lt_symm {s t : Icc (0 : β) 1} : symm s < symm t ↔ t < s :=
  OrderIso.lt_iff_lt (symmOrderIso (β := β)) (x := t) (y := s)

theorem lt_symm_comm {s t : Icc (0 : β) 1} : s < symm t ↔ t < symm s := by
  rw [← symm_lt_symm, symm_symm]

theorem symm_lt_comm {s t : Icc (0 : β) 1} : symm s < t ↔ symm t < s := by
  rw [← symm_lt_symm, symm_symm]

theorem strictAnti_symm : StrictAnti (symm : Icc (0 : β) 1 → Icc (0 : β) 1) :=
  fun _ _ h ↦ symmOrderIso.strictMono h

theorem antitone_symm : Antitone (symm : Icc (0 : β) 1 → Icc (0 : β) 1) :=
  fun _ _ h ↦ symmOrderIso.monotone h

end Set.Icc
