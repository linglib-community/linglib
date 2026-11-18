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
* `SupCon.Quotient`, `SupCon.mk'`, `SupCon.lift`, `SupCon.kerLift`: the quotient
  join-semilattice, the map to it, and the descent of a sup-homomorphism, following mathlib's
  `Con`.

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

/-! ### The quotient -/

section Quotient

section Max

variable [Max α] (c : SupCon α)

/-- The quotient of a type with a join by a congruence for it. -/
protected def Quotient := Quotient c.toSetoid

variable {c}

/-- The class of an element in the quotient by a congruence. -/
@[coe] def toQuotient : α → c.Quotient := Quotient.mk''

variable (c)

/-- Coercion from a type with a join to its quotient by a congruence. -/
instance (priority := 10) : CoeTC α c.Quotient := ⟨toQuotient⟩

/-- The quotient by a decidable congruence has decidable equality. -/
instance (priority := 500) [∀ a b, Decidable (c.r a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

/-- The quotient of a finite type by a decidable congruence is finite. -/
instance [Fintype α] [∀ a b, Decidable (c.r a b)] : Fintype c.Quotient :=
  inferInstanceAs (Fintype (Quotient c.toSetoid))

variable {c}

@[elab_as_elim]
protected theorem induction_on {C : c.Quotient → Prop} (q : c.Quotient) (H : ∀ x : α, C x) : C q :=
  Quotient.inductionOn' q H

@[elab_as_elim]
protected theorem induction_on₂ {C : c.Quotient → c.Quotient → Prop} (p q : c.Quotient)
    (H : ∀ x y : α, C x y) : C p q :=
  Quotient.inductionOn₂' p q H

/-- Two elements have the same class iff they are congruent. -/
protected theorem eq {a b : α} : (a : c.Quotient) = (b : c.Quotient) ↔ c.r a b :=
  Quotient.eq''

variable (c)

/-- The join of two classes is the class of the join. -/
instance : Max c.Quotient := ⟨Quotient.map₂ (· ⊔ ·) fun _ _ h _ _ h' ↦ c.sup h h'⟩

@[simp, norm_cast] theorem coe_sup (x y : α) :
    ((x ⊔ y : α) : c.Quotient) = (x : c.Quotient) ⊔ (y : c.Quotient) :=
  rfl

end Max

variable [SemilatticeSup α] (c : SupCon α)

/-- The quotient of a join-semilattice by a congruence is a join-semilattice. -/
instance : SemilatticeSup c.Quotient :=
  SemilatticeSup.mk'
    (fun p q ↦ SupCon.induction_on₂ p q fun x y ↦ congrArg toQuotient (sup_comm x y))
    (fun p q r ↦ SupCon.induction_on₂ p q fun x y ↦ SupCon.induction_on r fun z ↦
      congrArg toQuotient (sup_assoc x y z))
    (fun p ↦ SupCon.induction_on p fun x ↦ congrArg toQuotient (sup_idem x))

/-- The map from a join-semilattice to its quotient by a congruence. -/
def mk' : SupHom α c.Quotient where
  toFun := (↑)
  map_sup' _ _ := rfl

@[simp] theorem mk'_apply (x : α) : c.mk' x = x := rfl

theorem mk'_surjective : Function.Surjective c.mk' := Quotient.mk''_surjective

variable {c} [SemilatticeSup β]

/-- A sup-homomorphism constant on the classes of a congruence descends to the quotient. -/
def lift (f : SupHom α β) (h : c.toSetoid ≤ Setoid.ker f) : SupHom c.Quotient β where
  toFun q := Quotient.liftOn' q f fun _ _ hab ↦ h hab
  map_sup' p q := SupCon.induction_on₂ p q fun x y ↦ map_sup f x y

@[simp] theorem lift_coe (f : SupHom α β) (h : c.toSetoid ≤ Setoid.ker f) (x : α) :
    lift f h (x : c.Quotient) = f x :=
  rfl

/-- A sup-homomorphism descends to the quotient by its kernel. -/
def kerLift (f : SupHom α β) : SupHom (ker f).Quotient β := lift f le_rfl

@[simp] theorem kerLift_coe (f : SupHom α β) (x : α) : kerLift f (x : (ker f).Quotient) = f x :=
  rfl

/-- A sup-homomorphism is injective on the quotient by its kernel. -/
theorem kerLift_injective (f : SupHom α β) : Function.Injective (kerLift f) := fun p q ↦
  SupCon.induction_on₂ p q fun _ _ h ↦ SupCon.eq.2 h

end Quotient

end SupCon
