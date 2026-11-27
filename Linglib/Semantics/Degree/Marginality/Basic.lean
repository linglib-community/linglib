/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.Order.Comparable
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Quotient

/-!
# Marginal and large differences

A marginal scale on a linear order is an equivalence relation with order-connected classes: two
degrees are equivalent when they differ at most marginally. A degree `x` is marginally smaller
than `y` when `x < y` and the two differ at most marginally, and largely smaller when `x < y` and
they do not. The classes are the blocks of the scale. They are linearly ordered, as the quotient of
a linear order by an equivalence with order-connected classes is, and one block precedes another
exactly when its degrees are largely smaller.

The ML theory of Dinis and Jacinto takes marginally smaller than as primitive. Its axioms that
marginally smaller implies smaller, that marginal differences are irrelevant to large ones, and
that large differences extend along the order hold on every marginal scale. Its two remaining
axioms, that some difference is large and that a large difference decomposes into a marginal step
and a large one on either side, are the predicate `MarginalScale.IsML`.

## Main definitions

* `MarginalScale`: an equivalence relation with order-connected classes on a linear order.
* `MarginalScale.AtMostMarginal`, `MarginalScale.MarginallyLT`, `MarginalScale.LargelyLT`: the
  three comparisons of a marginal scale.
* `MarginalScale.Block`, `MarginalScale.toBlock`, `MarginalScale.toBlockHom`: the blocks, and the
  monotone map taking a degree to its block.
* `MarginalScale.IsML`: the scales that satisfy ML theory.
* `MarginalScale.ofMarginallyLT`: the scale of a relation of being marginally smaller that
  satisfies Axioms 2 and 3 of ML theory.

## Main results

* `MarginalScale.toBlock_lt_toBlock`: one block precedes another exactly when its degrees are
  largely smaller.
* `MarginalScale.instIsStrictWeakOrderLargelyLT`,
  `MarginalScale.atMostMarginal_iff_incompRel`: largely smaller than is a strict weak order whose
  incomparability is at most marginal difference.
* `MarginalScale.isML_iff`: a scale satisfies ML theory exactly when it has at least two blocks
  and none has an endpoint facing another.
* `MarginalScale.IsML.infinite_Ioo`: in a scale satisfying ML theory, infinitely many degrees lie
  between two that differ largely.

## Implementation notes

The scale is the equivalence and not the relation of being marginally smaller with the axioms of
ML theory as fields. The two presentations determine each other, by `MarginalScale.ofMarginallyLT`
and `MarginalScale.ofMarginallyLT_eq_self`, and the equivalence is the one
under which the scale of an order-connected subgroup of an ordered group exists whatever the
subgroup: when the subgroup is everything, as in an archimedean group, no difference is large and
the scale does not satisfy ML theory.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
-/

@[expose] public section

/-- A marginal scale on a linear order is an equivalence relation, at most marginal difference,
whose classes are order-connected. -/
structure MarginalScale (α : Type*) [LinearOrder α] extends Setoid α where
  /-- The degrees that differ at most marginally from a given one are order-connected. -/
  ordConnected' : ∀ x, {y | r x y}.OrdConnected

namespace MarginalScale

variable {α : Type*} [LinearOrder α] (ml : MarginalScale α)

/-- Two degrees differ at most marginally when they are equivalent in the scale. -/
def AtMostMarginal (x y : α) : Prop := ml.toSetoid x y

/-- `x` is marginally smaller than `y` when it is smaller and differs at most marginally. -/
def MarginallyLT (x y : α) : Prop := x < y ∧ ml.AtMostMarginal x y

/-- `x` is largely smaller than `y` when it is smaller but not marginally smaller. -/
def LargelyLT (x y : α) : Prop := x < y ∧ ¬ ml.MarginallyLT x y

variable {ml} {x y z : α}

@[ext]
theorem ext {ml ml' : MarginalScale α} (h : ∀ x y, ml.AtMostMarginal x y ↔ ml'.AtMostMarginal x y) :
    ml = ml' := by
  obtain ⟨s, _⟩ := ml
  obtain ⟨s', _⟩ := ml'
  obtain rfl : s = s' := Setoid.ext h
  rfl

theorem AtMostMarginal.refl (x : α) : ml.AtMostMarginal x x := ml.toSetoid.refl x

theorem AtMostMarginal.symm (h : ml.AtMostMarginal x y) : ml.AtMostMarginal y x :=
  ml.toSetoid.symm h

theorem AtMostMarginal.trans (hxy : ml.AtMostMarginal x y) (hyz : ml.AtMostMarginal y z) :
    ml.AtMostMarginal x z :=
  ml.toSetoid.trans hxy hyz

theorem atMostMarginal_comm : ml.AtMostMarginal x y ↔ ml.AtMostMarginal y x :=
  ⟨.symm, .symm⟩

variable (ml) in
theorem ordConnected_setOf_atMostMarginal (x : α) : {y | ml.AtMostMarginal x y}.OrdConnected :=
  ml.ordConnected' x

theorem marginallyLT_iff_lt_and_atMostMarginal :
    ml.MarginallyLT x y ↔ x < y ∧ ml.AtMostMarginal x y :=
  Iff.rfl

theorem largelyLT_iff_lt_and_not_atMostMarginal :
    ml.LargelyLT x y ↔ x < y ∧ ¬ ml.AtMostMarginal x y :=
  and_congr_right fun h ↦ not_congr (and_iff_right h)

@[grind =]
theorem atMostMarginal_iff :
    ml.AtMostMarginal x y ↔ x = y ∨ ml.MarginallyLT x y ∨ ml.MarginallyLT y x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases lt_trichotomy x y with hxy | rfl | hxy
    exacts [.inr (.inl ⟨hxy, h⟩), .inl rfl, .inr (.inr ⟨hxy, h.symm⟩)]
  · rintro (rfl | h | h)
    exacts [.refl _, h.2, h.2.symm]

/-- Axiom 2 of ML theory: marginally smaller than implies smaller than. -/
@[grind →]
theorem MarginallyLT.lt (h : ml.MarginallyLT x y) : x < y := h.1

@[grind →]
theorem LargelyLT.lt (h : ml.LargelyLT x y) : x < y := h.1

theorem MarginallyLT.not_largelyLT (h : ml.MarginallyLT x y) : ¬ ml.LargelyLT x y := fun h' ↦ h'.2 h

theorem MarginallyLT.atMostMarginal (h : ml.MarginallyLT x y) : ml.AtMostMarginal x y := h.2

theorem LargelyLT.not_atMostMarginal (h : ml.LargelyLT x y) : ¬ ml.AtMostMarginal x y :=
  (largelyLT_iff_lt_and_not_atMostMarginal.1 h).2

theorem marginallyLT_or_largelyLT_of_lt (h : x < y) : ml.MarginallyLT x y ∨ ml.LargelyLT x y :=
  (em _).imp_right (⟨h, ·⟩)

/-- Marginal steps do not accrue to a large difference. -/
theorem MarginallyLT.trans (hxy : ml.MarginallyLT x y) (hyz : ml.MarginallyLT y z) :
    ml.MarginallyLT x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

theorem MarginallyLT.bounded (hxz : ml.MarginallyLT x z) (hxy : x < y) (hyz : y < z) :
    ml.MarginallyLT x y ∧ ml.MarginallyLT y z :=
  have h : ml.AtMostMarginal x y :=
    (ml.ordConnected_setOf_atMostMarginal x).out (.refl x) hxz.2 ⟨hxy.le, hyz.le⟩
  ⟨⟨hxy, h⟩, hyz, h.symm.trans hxz.2⟩

instance : IsStrictOrder α ml.MarginallyLT where
  irrefl _ h := h.lt.false
  trans _ _ _ := MarginallyLT.trans

/-! ### Blocks -/

variable (ml) in
/-- The blocks of a marginal scale are its classes of at most marginally different degrees. -/
def Block : Type _ := Quotient ml.toSetoid

variable (ml) in
/-- The block of a degree. -/
def toBlock (x : α) : ml.Block := Quotient.mk _ x

instance (q : Quotient ml.toSetoid) : (Quotient.mk ml.toSetoid ⁻¹' {q}).OrdConnected := by
  induction q using Quotient.inductionOn with | h x
  convert ml.ordConnected_setOf_atMostMarginal x using 1
  ext y
  exact Quotient.eq.trans atMostMarginal_comm

noncomputable instance : LinearOrder ml.Block := by
  classical exact inferInstanceAs (LinearOrder (Quotient ml.toSetoid))

@[elab_as_elim]
protected theorem Block.ind {p : ml.Block → Prop} (h : ∀ x, p (ml.toBlock x)) (b : ml.Block) :
    p b :=
  Quotient.ind h b

variable (ml) in
theorem toBlock_surjective : Function.Surjective ml.toBlock := Block.ind fun x ↦ ⟨x, rfl⟩

/-- One block comes before another exactly when its degrees are largely smaller. -/
@[simp]
theorem toBlock_lt_toBlock : ml.toBlock x < ml.toBlock y ↔ ml.LargelyLT x y :=
  Quotient.mk_lt_mk.trans largelyLT_iff_lt_and_not_atMostMarginal.symm

@[simp]
theorem toBlock_eq_toBlock : ml.toBlock x = ml.toBlock y ↔ ml.AtMostMarginal x y := Quotient.eq

theorem toBlock_le_toBlock : ml.toBlock x ≤ ml.toBlock y ↔ ¬ ml.LargelyLT y x :=
  not_lt.symm.trans (not_congr toBlock_lt_toBlock)

variable (ml) in
theorem toBlock_mono : Monotone ml.toBlock := Quotient.mk_monotone

variable (ml) in
/-- Taking a degree to its block, as an order homomorphism. -/
@[simps]
def toBlockHom : α →o ml.Block := ⟨ml.toBlock, ml.toBlock_mono⟩

instance [Countable α] : Countable ml.Block := ml.toBlock_surjective.countable

/-! ### Largely smaller than -/

/-- The first half of Axiom 4 of ML theory: whatever is smaller than something largely smaller
than `z` is largely smaller than `z`. -/
theorem LargelyLT.of_lt_of_largelyLT (hxy : x < y) (h : ml.LargelyLT y z) : ml.LargelyLT x z :=
  toBlock_lt_toBlock.1 ((ml.toBlock_mono hxy.le).trans_lt (toBlock_lt_toBlock.2 h))

/-- The second half of Axiom 4 of ML theory: whatever is largely smaller than something smaller
than `z` is largely smaller than `z`. -/
theorem LargelyLT.trans_lt (h : ml.LargelyLT x y) (hyz : y < z) : ml.LargelyLT x z :=
  toBlock_lt_toBlock.1 ((toBlock_lt_toBlock.2 h).trans_le (ml.toBlock_mono hyz.le))

theorem AtMostMarginal.largelyLT_congr_left (h : ml.AtMostMarginal x y) :
    ml.LargelyLT x z ↔ ml.LargelyLT y z := by
  rw [← toBlock_lt_toBlock, ← toBlock_lt_toBlock, toBlock_eq_toBlock.2 h]

theorem AtMostMarginal.largelyLT_congr_right (h : ml.AtMostMarginal y z) :
    ml.LargelyLT x y ↔ ml.LargelyLT x z := by
  rw [← toBlock_lt_toBlock, ← toBlock_lt_toBlock, toBlock_eq_toBlock.2 h]

/-- Axiom 3 of ML theory, M-irrelevance: when `x` is marginally smaller than `y`, whatever is
largely smaller than `y` is largely smaller than `x`, and `y` is largely smaller than whatever `x`
is largely smaller than. -/
theorem MarginallyLT.irrelevance (h : ml.MarginallyLT x y) (z : α) :
    (ml.LargelyLT z y → ml.LargelyLT z x) ∧ (ml.LargelyLT x z → ml.LargelyLT y z) :=
  ⟨h.atMostMarginal.largelyLT_congr_right.2, h.atMostMarginal.largelyLT_congr_left.1⟩

instance : Std.Asymm ml.LargelyLT := ⟨fun _ _ h h' ↦ h.lt.asymm h'.lt⟩

/-- Largely smaller than is negatively transitive. When one degree is largely smaller than
another, any third degree is largely greater than the first or largely smaller than the
second. -/
instance : IsOrderConnected α ml.LargelyLT where
  conn a b c h := by
    simp only [← toBlock_lt_toBlock] at h ⊢
    exact (lt_or_ge (ml.toBlock a) (ml.toBlock b)).imp_right fun h' ↦ h'.trans_lt h

instance : IsOrderConnected α (Function.swap ml.LargelyLT) :=
  ⟨fun a b c h ↦ (IsOrderConnected.conn c b a h).symm⟩

instance instIsStrictWeakOrderLargelyLT : IsStrictWeakOrder α ml.LargelyLT :=
  isStrictWeakOrder_of_isOrderConnected

/-- At most marginal difference is incomparability under largely smaller than. -/
theorem atMostMarginal_iff_incompRel : ml.AtMostMarginal x y ↔ IncompRel ml.LargelyLT x y := by
  rw [← toBlock_eq_toBlock, le_antisymm_iff, toBlock_le_toBlock, toBlock_le_toBlock, and_comm]
  rfl

/-! ### Scales satisfying ML theory -/

variable (ml) in
/-- A marginal scale satisfies ML theory when some difference is large and every large difference
decomposes into a marginal step followed by a large one, and into a large one followed by a
marginal step. -/
structure IsML : Prop where
  /-- Some degree is largely smaller than another. -/
  exists_largelyLT : ∃ x y, ml.LargelyLT x y
  /-- A large difference is a marginal step followed by a large difference. -/
  exists_marginallyLT_largelyLT : ∀ ⦃x y⦄, ml.LargelyLT x y →
    ∃ z, ml.MarginallyLT x z ∧ ml.LargelyLT z y
  /-- A large difference is a large difference followed by a marginal step. -/
  exists_largelyLT_marginallyLT : ∀ ⦃x y⦄, ml.LargelyLT x y →
    ∃ w, ml.LargelyLT x w ∧ ml.MarginallyLT w y

/-- A marginal scale satisfies ML theory exactly when it has at least two blocks, a block below
another has no greatest degree, and a block above another has no least degree. -/
theorem isML_iff : ml.IsML ↔ (∃ x y, ¬ ml.AtMostMarginal x y) ∧
    (∀ ⦃x y⦄, x < y → ¬ ml.AtMostMarginal x y → ∃ z, x < z ∧ ml.AtMostMarginal x z) ∧
      ∀ ⦃x y⦄, x < y → ¬ ml.AtMostMarginal x y → ∃ w, w < y ∧ ml.AtMostMarginal w y := by
  refine ⟨fun h ↦ ⟨?_, fun x y hxy hn ↦ ?_, fun x y hxy hn ↦ ?_⟩, fun ⟨⟨x, y, hn⟩, hgt, hlt⟩ ↦
    ⟨?_, fun x y h ↦ ?_, fun x y h ↦ ?_⟩⟩
  · obtain ⟨x, y, h⟩ := h.exists_largelyLT
    exact ⟨x, y, h.not_atMostMarginal⟩
  · obtain ⟨z, hz, -⟩ := h.exists_marginallyLT_largelyLT
      (largelyLT_iff_lt_and_not_atMostMarginal.2 ⟨hxy, hn⟩)
    exact ⟨z, hz⟩
  · obtain ⟨w, -, hw⟩ := h.exists_largelyLT_marginallyLT
      (largelyLT_iff_lt_and_not_atMostMarginal.2 ⟨hxy, hn⟩)
    exact ⟨w, hw⟩
  · rcases lt_trichotomy x y with hxy | rfl | hxy
    · exact ⟨x, y, largelyLT_iff_lt_and_not_atMostMarginal.2 ⟨hxy, hn⟩⟩
    · exact absurd (.refl x) hn
    · exact ⟨y, x, largelyLT_iff_lt_and_not_atMostMarginal.2 ⟨hxy, fun h ↦ hn h.symm⟩⟩
  · obtain ⟨hxy, hn⟩ := largelyLT_iff_lt_and_not_atMostMarginal.1 h
    obtain ⟨z, hxz, hz⟩ := hgt hxy hn
    exact ⟨z, ⟨hxz, hz⟩, (hz.largelyLT_congr_left).1 h⟩
  · obtain ⟨hxy, hn⟩ := largelyLT_iff_lt_and_not_atMostMarginal.1 h
    obtain ⟨w, hwy, hw⟩ := hlt hxy hn
    exact ⟨w, (hw.largelyLT_congr_right).2 h, hwy, hw⟩

namespace IsML

variable (h : ml.IsML)
include h

theorem infinite_setOf (hxy : ml.LargelyLT x y) :
    {z | ml.MarginallyLT x z ∧ ml.LargelyLT z y}.Infinite := fun hfin ↦ by
  obtain ⟨z₀, hz₀⟩ := h.exists_marginallyLT_largelyLT hxy
  obtain ⟨z, ⟨hxz, hzy⟩, hmax⟩ := hfin.exists_maximal ⟨z₀, hz₀⟩
  obtain ⟨w, hzw, hwy⟩ := h.exists_marginallyLT_largelyLT hzy
  exact (hmax ⟨hxz.trans hzw, hwy⟩ hzw.lt.le).not_gt hzw.lt

/-- In a scale satisfying ML theory, infinitely many degrees lie between two that differ
largely. -/
theorem infinite_Ioo (hxy : ml.LargelyLT x y) : (Set.Ioo x y).Infinite :=
  (h.infinite_setOf hxy).mono (s := {z | ml.MarginallyLT x z ∧ ml.LargelyLT z y}) fun _ hz ↦
    ⟨hz.1.lt, hz.2.lt⟩

end IsML

/-! ### Marginally smaller than as the primitive -/

section OfMarginallyLT

variable {M : α → α → Prop} (lt_of : ∀ ⦃x y⦄, M x y → x < y)
  (irrelevance : ∀ ⦃x y⦄ z, M x y →
    (z < y ∧ ¬ M z y → z < x ∧ ¬ M z x) ∧ (x < z ∧ ¬ M x z → y < z ∧ ¬ M y z))

include lt_of irrelevance in
theorem trans_of_irrelevance (hxy : M x y) (hyz : M y z) : M x z := by grind

include irrelevance in
theorem bounded_of_irrelevance (hxz : M x z) (hxy : x < y) (hyz : y < z) :
    M x y ∧ M y z := by
  grind

variable (M) in
/-- A relation that satisfies Axioms 2 and 3 of ML theory, with largely smaller than defined from
it, is marginally smaller than in a marginal scale. -/
def ofMarginallyLT : MarginalScale α where
  r x y := x = y ∨ M x y ∨ M y x
  iseqv :=
    have t {x y z : α} : M x y → M y z → M x z := trans_of_irrelevance lt_of irrelevance
    have b {x y z : α} : M x z → x < y → y < z → M x y ∧ M y z :=
      bounded_of_irrelevance irrelevance
    ⟨fun _ ↦ .inl rfl, fun h ↦ by grind, fun {x y z} hxy hyz ↦ by
      rcases lt_trichotomy x z with hxz | rfl | hzx
      · grind
      · exact .inl rfl
      · grind⟩
  ordConnected' x :=
    have t {x y z : α} : M x y → M y z → M x z := trans_of_irrelevance lt_of irrelevance
    have b {x y z : α} : M x z → x < y → y < z → M x y ∧ M y z :=
      bounded_of_irrelevance irrelevance
    ⟨fun a ha c hc w hw ↦ by
      change _ ∨ _ ∨ _ at ha hc ⊢
      obtain ⟨haw, hwc⟩ := hw
      rcases lt_trichotomy x w with hxw | rfl | hwx
      · grind
      · exact .inl rfl
      · grind⟩

theorem ofMarginallyLT_atMostMarginal_iff :
    (ofMarginallyLT M lt_of irrelevance).AtMostMarginal x y ↔ x = y ∨ M x y ∨ M y x :=
  Iff.rfl

@[simp]
theorem ofMarginallyLT_marginallyLT_iff :
    (ofMarginallyLT M lt_of irrelevance).MarginallyLT x y ↔ M x y := by
  rw [MarginallyLT, ofMarginallyLT_atMostMarginal_iff]
  exact ⟨fun ⟨hxy, h⟩ ↦ h.elim (fun e ↦ absurd e hxy.ne) fun h ↦
    h.elim id fun h ↦ absurd (lt_of h) hxy.not_gt, fun h ↦ ⟨lt_of h, .inr (.inl h)⟩⟩

/-- A marginal scale is the scale of its relation of being marginally smaller. -/
theorem ofMarginallyLT_eq_self (ml : MarginalScale α) :
    ofMarginallyLT ml.MarginallyLT (fun _ _ h ↦ h.lt)
      (fun _ _ z h ↦ h.irrelevance z) = ml :=
  ext fun _ _ ↦ (ofMarginallyLT_atMostMarginal_iff ..).trans atMostMarginal_iff.symm

end OfMarginallyLT

end MarginalScale
