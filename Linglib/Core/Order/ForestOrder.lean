/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Comparable
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Forest orders

An order is a **forest** when the elements below any element are pairwise comparable,
`a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a`, which is to say that
[every principal down-set is a chain](##isForestOrder_iff_forall_isChain_Iic): the order may
branch upward but never downward. A forest in which any two elements have a common upper bound
[is totally ordered](##IsForestOrder.le_total). Linear orders are forests, as is every `PredOrder`
with archimedean predecessor, such as the rooted trees of `Mathlib/Order/SuccPred/Tree.lean`, and
the property [pulls back along an order embedding](##OrderEmbedding.isForestOrder).

The flags of a forest are its branches. A flag [contains everything below](##Flag.Iic_subset)
each of its elements, the down-set of a maximal element [is a flag](##Flag.ofIsMax), and when `>`
is well-founded [every flag arises this way](##Flag.exists_isMax_eq_ofIsMax), so that quantifying
over flags [is quantifying over maximal elements](##Flag.forall_mem_iff).

`[UPSTREAM]` candidate for `Mathlib/Order/Forest.lean`. The class states what mathlib proves
separately as `le_total_of_directed` and `Part.le_total_of_le_of_le`, and
`IsForestOrder.le_total` is the totality behind `IsPredArchimedean.linearOrder`.
-/

@[expose] public section

variable {α β : Type*}

/-- An order is a **forest** when the elements below any element are pairwise comparable, so
that it never branches downward. -/
class IsForestOrder (α : Type*) [LE α] : Prop where
  /-- The elements below any element are pairwise comparable. -/
  le_total_of_le_of_le : ∀ ⦃a b c : α⦄, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

instance (priority := 100) LinearOrder.toIsForestOrder [LinearOrder α] : IsForestOrder α :=
  ⟨fun a b _ _ _ ↦ le_total a b⟩

instance (priority := 100) IsPredArchimedean.toIsForestOrder [Preorder α] [PredOrder α]
    [IsPredArchimedean α] : IsForestOrder α :=
  ⟨fun _ _ _ ha hb ↦ (le_total_of_directed ha hb).symm⟩

theorem OrderEmbedding.isForestOrder [LE α] [LE β] [IsForestOrder β] (f : α ↪o β) :
    IsForestOrder α :=
  ⟨fun _ _ _ ha hb ↦ (IsForestOrder.le_total_of_le_of_le (f.map_rel_iff.2 ha)
    (f.map_rel_iff.2 hb)).imp f.map_rel_iff.1 f.map_rel_iff.1⟩

instance Subtype.instIsForestOrder [LE α] [IsForestOrder α] (p : α → Prop) :
    IsForestOrder (Subtype p) :=
  ⟨fun a b c ha hb ↦ IsForestOrder.le_total_of_le_of_le (a := a.1) (b := b.1) (c := c.1) ha hb⟩

/-- The order dual of an order is a forest exactly when the elements above any element are
pairwise comparable, so that the order never branches upward. -/
theorem isForestOrder_orderDual_iff [LE α] :
    IsForestOrder αᵒᵈ ↔ ∀ ⦃a b c : α⦄, c ≤ a → c ≤ b → a ≤ b ∨ b ≤ a :=
  ⟨fun h a b c ha hb ↦ (h.le_total_of_le_of_le (a := OrderDual.toDual a)
      (b := OrderDual.toDual b) (c := OrderDual.toDual c) ha hb).symm,
    fun h ↦ ⟨fun a b c ha hb ↦ (h (a := OrderDual.ofDual a) (b := OrderDual.ofDual b)
      (c := OrderDual.ofDual c) ha hb).symm⟩⟩

namespace IsForestOrder

section Preorder

variable [Preorder α] [IsForestOrder α] {a b c : α}

/-- A forest in which any two elements have a common upper bound is totally ordered. -/
protected theorem le_total [IsDirectedOrder α] (a b : α) : a ≤ b ∨ b ≤ a :=
  let ⟨_, ha, hb⟩ := exists_ge_ge a b
  le_total_of_le_of_le ha hb

theorem isChain_Iic (a : α) : IsChain (· ≤ ·) (Set.Iic a) :=
  fun _ hb _ hc _ ↦ le_total_of_le_of_le (Set.mem_Iic.1 hb) (Set.mem_Iic.1 hc)

/-- In a forest two principal up-sets are disjoint exactly when their generators are
incomparable. -/
theorem disjoint_Ici_iff : Disjoint (Set.Ici a) (Set.Ici b) ↔ IncompRel (· ≤ ·) a b :=
  ⟨fun h ↦ ⟨fun hab ↦ Set.disjoint_left.1 h hab le_rfl,
      fun hba ↦ Set.disjoint_right.1 h hba le_rfl⟩,
    fun h ↦ Set.disjoint_left.2 fun _ ha hb ↦ (le_total_of_le_of_le ha hb).elim h.1 h.2⟩

/-- `CovBy.le_of_lt` in a forest. -/
theorem le_of_lt_of_covBy (hab : a ⋖ b) (hcb : c < b) : c ≤ a :=
  (le_total_of_le_of_le hcb.le hab.le).elim id fun h ↦
    by_contra fun hca ↦ hab.2 (lt_of_le_not_ge h hca) hcb

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c d x : α}

/-- `CovBy.unique_left` in a forest: an element covers at most one element. -/
theorem covBy_unique_left [IsForestOrder α] (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
  (le_of_lt_of_covBy hb ha.lt).antisymm (le_of_lt_of_covBy ha hb.lt)

/-- `CovBy.unique_right` when the order dual is a forest: an element is covered by at most one
element. -/
theorem covBy_unique_right [IsForestOrder αᵒᵈ] (hb : a ⋖ b) (hc : a ⋖ c) : b = c :=
  covBy_unique_left (α := αᵒᵈ) hb.toDual hc.toDual

/-- In a forest, two elements covering the same element and lying below a common element are
equal. -/
theorem eq_of_covBy_of_le [IsForestOrder α] (hc : a ⋖ c) (hd : a ⋖ d) (hcx : c ≤ x)
    (hdx : d ≤ x) : c = d :=
  (le_total_of_le_of_le hcx hdx).elim (fun h ↦ (hd.eq_or_eq hc.le h).resolve_left hc.ne')
    fun h ↦ ((hc.eq_or_eq hd.le h).resolve_left hd.ne').symm

end PartialOrder

end IsForestOrder

theorem isForestOrder_iff_forall_isChain_Iic [Preorder α] :
    IsForestOrder α ↔ ∀ a : α, IsChain (· ≤ ·) (Set.Iic a) :=
  ⟨fun _ ↦ IsForestOrder.isChain_Iic, fun h ↦
    ⟨fun _ _ c ha hb ↦ (h c).total (Set.mem_Iic.2 ha) (Set.mem_Iic.2 hb)⟩⟩

/-! ### Flags -/

namespace Flag

variable [PartialOrder α] {m x y : α} {h : Flag α}

/-- A flag through a non-maximal element contains a strictly larger one; otherwise inserting
the successor would extend the chain. -/
theorem exists_mem_gt_of_lt (hm : m ∈ h) (hx : m < x) : ∃ y ∈ h, m < y := by
  by_contra! hcon
  have hxh : x ∈ h := mem_iff_forall_le_or_ge.2 fun b hb ↦ .inr <|
    (h.le_or_le hb hm).elim (fun hbm ↦ hbm.trans hx.le) fun hmb ↦
      (hmb.lt_or_eq.resolve_left (hcon b hb)) ▸ hx.le
  exact hcon x hxh hx

variable [IsForestOrder α]

theorem Iic_subset (hm : m ∈ h) : Set.Iic m ⊆ (h : Set α) := fun _ hx ↦
  mem_iff_forall_le_or_ge.2 fun _ hb ↦ (h.le_or_le hb hm).elim
    (fun hbm ↦ IsForestOrder.le_total_of_le_of_le hx hbm) fun hmb ↦ .inl (hx.trans hmb)

/-- The down-set of a maximal element of a forest, as a flag. -/
def ofIsMax (hx : IsMax x) : Flag α where
  carrier := Set.Iic x
  Chain' := IsForestOrder.isChain_Iic x
  max_chain' := fun _ hc hsub ↦ hsub.antisymm fun _ hy ↦
    (hc.total (hsub (Set.mem_Iic.2 le_rfl)) hy).elim (fun h ↦ hx h) id

@[simp, norm_cast] theorem coe_ofIsMax (hx : IsMax x) : (ofIsMax hx : Set α) = Set.Iic x := rfl

@[simp] theorem mem_ofIsMax {hx : IsMax x} : y ∈ ofIsMax hx ↔ y ≤ x := Iff.rfl

theorem eq_ofIsMax_of_mem (hx : IsMax x) (hxh : x ∈ h) : h = ofIsMax hx :=
  Flag.ext (Set.ext fun _ ↦ ⟨fun hy ↦ (h.le_or_le hy hxh).elim id fun hxy ↦ hx hxy,
    fun hy ↦ Iic_subset hxh hy⟩)

variable [WellFoundedGT α]

/-- When `>` is well-founded, as on a finite order, every flag of a forest is the down-set of
a maximal element: the flag has a greatest element, which a strict successor would contradict. -/
theorem exists_isMax_eq_ofIsMax [Nonempty α] (h : Flag α) :
    ∃ x, ∃ hx : IsMax x, h = ofIsMax hx := by
  obtain ⟨x, hx, hmax⟩ :=
    WellFounded.has_min (wellFounded_gt (α := α)) (h : Set α) (h.maxChain.nonempty_iff.1 ‹_›)
  refine ⟨x, fun y hxy ↦ ?_, eq_ofIsMax_of_mem _ hx⟩
  by_contra hyx
  obtain ⟨z, hz, hxz⟩ := exists_mem_gt_of_lt hx (lt_of_le_not_ge hxy hyx)
  exact hmax z hz hxz

/-- When `>` is well-founded, quantifying over the flags through an element of a left-linear
order is quantifying over the maximal elements above it. -/
theorem forall_mem_iff {P : Flag α → Prop} :
    (∀ h : Flag α, m ∈ h → P h) ↔ ∀ x, ∀ hx : IsMax x, m ≤ x → P (ofIsMax hx) :=
  ⟨fun H x hx hmx ↦ H _ hmx, fun H h hm ↦ by
    obtain ⟨x, hx, rfl⟩ := have : Nonempty α := ⟨m⟩; exists_isMax_eq_ofIsMax h
    exact H x hx hm⟩

end Flag
