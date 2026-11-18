/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Preorder.Finite
public import Linglib.Semantics.Degree.CresswellDegree

/-!
# Marginal and large differences

Dinis and Jacinto's ML theory orders degrees by smaller than together with a relation of being
marginally smaller, and a degree is largely smaller than another when it is smaller but not
marginally so. A `MarginalScale` is a linear order with such a relation obeying the five axioms of
their 2026 paper, which simplify the original theory of 2025. Largely smaller than is a strict weak
order [whose incomparability is at most marginal
difference](##MarginalScale.atMostMarginal_iff_incompRel), so the degrees fall into
[blocks](##MarginalScale.Block), the degrees that Cresswell builds from the comparison largely
smaller than, and [taking a degree to its block](##MarginalScale.toBlock_lt_toBlock) is monotone.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
* [cresswell-1976]
-/

@[expose] public section

/-- A marginal scale is a linear order with a relation of being marginally smaller, subject to the
five axioms of ML theory. A degree is largely smaller than another when it is smaller but not
marginally smaller. -/
structure MarginalScale (α : Type*) [LinearOrder α] where
  /-- `x` is marginally smaller than `y`. -/
  MarginallyLT : α → α → Prop
  /-- Axiom 1 says that some element is largely smaller than another. -/
  exists_large : ∃ x y, x < y ∧ ¬ MarginallyLT x y
  /-- Axiom 2 says that marginally smaller than implies smaller than. -/
  lt_of_marginallyLT : ∀ ⦃x y⦄, MarginallyLT x y → x < y
  /-- Axiom 3, M-irrelevance, says that when `x` is marginally smaller than `y`, whatever is
  largely smaller than `y` is largely smaller than `x`, and `y` is largely smaller than whatever
  `x` is largely smaller than. -/
  irrelevance : ∀ ⦃x y⦄ z, MarginallyLT x y →
    (z < y ∧ ¬ MarginallyLT z y → z < x ∧ ¬ MarginallyLT z x) ∧
      (x < z ∧ ¬ MarginallyLT x z → y < z ∧ ¬ MarginallyLT y z)
  /-- Axiom 4 says that whatever is smaller than something largely smaller than `z` is largely
  smaller than `z`, and whatever is largely smaller than something smaller than `z` is largely
  smaller than `z`. -/
  extends_lt : ∀ ⦃x y⦄ z, x < y →
    (y < z ∧ ¬ MarginallyLT y z → x < z ∧ ¬ MarginallyLT x z) ∧
      (z < x ∧ ¬ MarginallyLT z x → z < y ∧ ¬ MarginallyLT z y)
  /-- Axiom 5, Decomposition, says that a large difference is a marginal step followed by a
  large one, and a large one followed by a marginal step. -/
  decomposition : ∀ ⦃x y⦄, x < y ∧ ¬ MarginallyLT x y →
    (∃ z, MarginallyLT x z ∧ z < y ∧ ¬ MarginallyLT z y) ∧
      ∃ w, MarginallyLT w y ∧ x < w ∧ ¬ MarginallyLT x w

namespace MarginalScale

variable {α : Type*} [LinearOrder α] (ml : MarginalScale α)

@[ext]
theorem ext {ml ml' : MarginalScale α} (h : ∀ x y, ml.MarginallyLT x y ↔ ml'.MarginallyLT x y) :
    ml = ml' := by
  cases ml; cases ml'
  congr
  exact funext₂ fun x y ↦ propext (h x y)

/-- `x` is largely smaller than `y` when it is smaller but not marginally smaller. -/
def LargelyLT (x y : α) : Prop := x < y ∧ ¬ ml.MarginallyLT x y

/-- Two degrees differ at most marginally when they are equal or one is marginally smaller than
the other. -/
def AtMostMarginal : α → α → Prop := Relation.ReflGen (Relation.SymmGen ml.MarginallyLT)

variable {ml} {x y z : α}

@[grind =]
theorem atMostMarginal_iff :
    ml.AtMostMarginal x y ↔ x = y ∨ ml.MarginallyLT x y ∨ ml.MarginallyLT y x :=
  (Relation.reflGen_iff _ _ _).trans (or_congr_left eq_comm)

variable (ml) in
theorem exists_largelyLT : ∃ x y, ml.LargelyLT x y := ml.exists_large

@[grind →]
theorem MarginallyLT.lt (h : ml.MarginallyLT x y) : x < y := ml.lt_of_marginallyLT h

@[grind →]
theorem LargelyLT.lt (h : ml.LargelyLT x y) : x < y := h.1

theorem MarginallyLT.not_largelyLT (h : ml.MarginallyLT x y) : ¬ ml.LargelyLT x y := fun h' ↦ h'.2 h

theorem MarginallyLT.atMostMarginal (h : ml.MarginallyLT x y) : ml.AtMostMarginal x y :=
  .single (.inl h)

theorem LargelyLT.exists_marginallyLT_largelyLT (h : ml.LargelyLT x y) :
    ∃ z, ml.MarginallyLT x z ∧ ml.LargelyLT z y :=
  (ml.decomposition h).1

theorem LargelyLT.exists_largelyLT_marginallyLT (h : ml.LargelyLT x y) :
    ∃ w, ml.LargelyLT x w ∧ ml.MarginallyLT w y :=
  let ⟨w, hw⟩ := (ml.decomposition h).2
  ⟨w, hw.symm⟩

theorem marginallyLT_or_largelyLT_of_lt (h : x < y) : ml.MarginallyLT x y ∨ ml.LargelyLT x y :=
  (em _).imp_right (⟨h, ·⟩)

theorem LargelyLT.of_lt_of_largelyLT (hxy : x < y) (h : ml.LargelyLT y z) : ml.LargelyLT x z :=
  (ml.extends_lt z hxy).1 h

theorem LargelyLT.trans_lt (h : ml.LargelyLT x y) (hyz : y < z) : ml.LargelyLT x z :=
  (ml.extends_lt x hyz).2 h

theorem LargelyLT.trans (hxy : ml.LargelyLT x y) (hyz : ml.LargelyLT y z) : ml.LargelyLT x z :=
  hxy.trans_lt hyz.lt

/-- Marginal steps do not accrue to a large difference. -/
theorem MarginallyLT.trans (hxy : ml.MarginallyLT x y) (hyz : ml.MarginallyLT y z) :
    ml.MarginallyLT x z := by
  grind [ml.irrelevance, MarginallyLT.lt]

theorem MarginallyLT.bounded (hxz : ml.MarginallyLT x z) (hxy : x < y) (hyz : y < z) :
    ml.MarginallyLT x y ∧ ml.MarginallyLT y z := by
  grind [ml.extends_lt]

instance : IsStrictOrder α ml.MarginallyLT where
  irrefl _ h := h.lt.false
  trans _ _ _ := MarginallyLT.trans

instance : Std.Asymm ml.LargelyLT := ⟨fun _ _ h h' ↦ h.lt.asymm h'.lt⟩

/-- Largely smaller than is negatively transitive. When one degree is largely smaller than
another, any third degree is largely greater than the first or largely smaller than the
second. -/
instance : IsOrderConnected α ml.LargelyLT where
  conn a b c h := by
    rcases le_or_gt b a with hba | hab
    · exact .inr (hba.eq_or_lt.elim (· ▸ h) (LargelyLT.of_lt_of_largelyLT · h))
    rcases le_or_gt c b with hcb | hbc
    · exact .inl (hcb.eq_or_lt.elim (· ▸ h) h.trans_lt)
    exact (marginallyLT_or_largelyLT_of_lt hab).elim
      (fun hm ↦ (marginallyLT_or_largelyLT_of_lt hbc).imp
        (fun hm' ↦ absurd (hm.trans hm') h.2) id) .inl

instance instIsStrictWeakOrderLargelyLT : IsStrictWeakOrder α ml.LargelyLT :=
  isStrictWeakOrder_of_isOrderConnected

/-- At most marginal difference is incomparability under largely smaller than. -/
theorem atMostMarginal_iff_incompRel : ml.AtMostMarginal x y ↔ IncompRel ml.LargelyLT x y := by
  simp only [AtMostMarginal, Relation.reflGen_iff, Relation.SymmGen, IncompRel]
  grind [marginallyLT_or_largelyLT_of_lt, MarginallyLT.not_largelyLT]

theorem AtMostMarginal.refl (x : α) : ml.AtMostMarginal x x := Relation.ReflGen.refl

theorem AtMostMarginal.symm (h : ml.AtMostMarginal x y) : ml.AtMostMarginal y x :=
  atMostMarginal_iff_incompRel.2 (atMostMarginal_iff_incompRel.1 h).symm

theorem AtMostMarginal.trans (hxy : ml.AtMostMarginal x y) (hyz : ml.AtMostMarginal y z) :
    ml.AtMostMarginal x z :=
  atMostMarginal_iff_incompRel.2 <| IsStrictWeakOrder.incomp_trans _ _ _
    (atMostMarginal_iff_incompRel.1 hxy) (atMostMarginal_iff_incompRel.1 hyz)

variable (ml) in
/-- At most marginal difference is an equivalence relation, sameness for present purposes. -/
def atMostMarginalSetoid : Setoid α :=
  ⟨ml.AtMostMarginal, ⟨AtMostMarginal.refl, AtMostMarginal.symm, AtMostMarginal.trans⟩⟩

theorem AtMostMarginal.largelyLT_congr_left (h : ml.AtMostMarginal x y) :
    ml.LargelyLT x z ↔ ml.LargelyLT y z :=
  have h := atMostMarginal_iff_incompRel.1 h
  ⟨fun h' ↦ (IsOrderConnected.conn _ y _ h').resolve_left h.1,
    fun h' ↦ (IsOrderConnected.conn _ x _ h').resolve_left h.2⟩

theorem AtMostMarginal.largelyLT_congr_right (h : ml.AtMostMarginal y z) :
    ml.LargelyLT x y ↔ ml.LargelyLT x z :=
  have h := atMostMarginal_iff_incompRel.1 h
  ⟨fun h' ↦ (IsOrderConnected.conn _ _ _ h').resolve_right h.2,
    fun h' ↦ (IsOrderConnected.conn _ _ _ h').resolve_right h.1⟩

theorem marginallyLT_iff_lt_and_atMostMarginal :
    ml.MarginallyLT x y ↔ x < y ∧ ml.AtMostMarginal x y := by
  grind [atMostMarginal_iff_incompRel, IncompRel, LargelyLT]

theorem LargelyLT.not_atMostMarginal (h : ml.LargelyLT x y) : ¬ ml.AtMostMarginal x y :=
  fun h' ↦ (atMostMarginal_iff_incompRel.1 h').1 h

/-! ### Blocks -/

variable (ml) in
/-- The blocks of a marginal scale are its classes of at most marginally different degrees,
ordered by largely smaller than. They are the degrees that [cresswell-1976] builds from the
comparison largely smaller than. -/
def Block : Type _ := CresswellDegree (Function.swap ml.LargelyLT)

variable (ml) in
/-- The block of a degree. -/
def toBlock (x : α) : ml.Block := Quotient.mk _ x

noncomputable instance : LinearOrder ml.Block := by
  classical exact inferInstanceAs (LinearOrder (CresswellDegree (Function.swap ml.LargelyLT)))

@[elab_as_elim]
protected theorem Block.ind {p : ml.Block → Prop} (h : ∀ x, p (ml.toBlock x)) (b : ml.Block) :
    p b :=
  Quotient.ind h b

variable (ml) in
theorem toBlock_surjective : Function.Surjective ml.toBlock := Block.ind fun x ↦ ⟨x, rfl⟩

/-- One block comes before another exactly when its degrees are largely smaller. -/
@[simp]
theorem toBlock_lt_toBlock : ml.toBlock x < ml.toBlock y ↔ ml.LargelyLT x y := Iff.rfl

@[simp]
theorem toBlock_eq_toBlock : ml.toBlock x = ml.toBlock y ↔ ml.AtMostMarginal x y := by
  rw [atMostMarginal_iff_incompRel, ← incompRel_swap, ← cresswellSetoid_iff_incompRel]
  exact Quotient.eq

theorem toBlock_le_toBlock : ml.toBlock x ≤ ml.toBlock y ↔ ¬ ml.LargelyLT y x :=
  not_lt.symm.trans (not_congr toBlock_lt_toBlock)

variable (ml) in
theorem toBlock_mono : Monotone ml.toBlock :=
  fun _ _ h ↦ toBlock_le_toBlock.2 fun h' ↦ h'.lt.not_ge h

variable (ml) in
/-- Taking a degree to its block, as an order homomorphism. -/
@[simps]
def toBlockHom : α →o ml.Block := ⟨ml.toBlock, ml.toBlock_mono⟩

instance : Nontrivial ml.Block :=
  let ⟨_, _, h⟩ := ml.exists_largelyLT
  ⟨_, _, (toBlock_lt_toBlock.2 h).ne⟩

instance [Countable α] : Countable ml.Block := ml.toBlock_surjective.countable

/-- Two degrees differ at most marginally or one is largely smaller than the other. -/
theorem largelyLT_or_atMostMarginal_or_largelyLT (x y : α) :
    ml.LargelyLT x y ∨ ml.AtMostMarginal x y ∨ ml.LargelyLT y x := by
  simpa using lt_trichotomy (ml.toBlock x) (ml.toBlock y)

theorem ordConnected_setOf_atMostMarginal (x : α) :
    {y | ml.AtMostMarginal x y}.OrdConnected := by
  convert (Set.ordConnected_singleton (a := ml.toBlock x)).preimage_mono ml.toBlock_mono using 1
  ext y
  exact toBlock_eq_toBlock.symm.trans eq_comm

theorem LargelyLT.infinite_setOf (h : ml.LargelyLT x y) :
    {z | ml.MarginallyLT x z ∧ ml.LargelyLT z y}.Infinite := fun hfin ↦ by
  obtain ⟨z₀, hz₀⟩ := (ml.decomposition h).1
  obtain ⟨z, ⟨hxz, hzy⟩, hmax⟩ := hfin.exists_maximal ⟨z₀, hz₀⟩
  obtain ⟨w, hzw, hwy⟩ := (ml.decomposition hzy).1
  exact (hmax ⟨hxz.trans hzw, hwy⟩ hzw.lt.le).not_gt hzw.lt

theorem LargelyLT.infinite_Ioo (h : ml.LargelyLT x y) : (Set.Ioo x y).Infinite :=
  h.infinite_setOf.mono (s := {z | ml.MarginallyLT x z ∧ ml.LargelyLT z y}) fun _ hz ↦
    ⟨hz.1.lt, hz.2.lt⟩

theorem isUpperSet_setOf_largelyLT (x : α) : IsUpperSet {y | ml.LargelyLT x y} :=
  fun _ _ hle h ↦ hle.eq_or_lt.elim (· ▸ h) h.trans_lt

end MarginalScale
