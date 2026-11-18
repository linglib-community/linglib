module

public import Mathlib.Order.Comparable
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.Preorder.Finite

/-!
# Left-linear orders

An order is **left-linear** when the predecessors of every element are pairwise comparable,
`a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a`, which is to say that
[every principal down-set is a chain](##isLeftLinear_iff_forall_isChain_Iic). This is the
order-theoretic notion of a tree: the order may branch upward but never downward. Linear orders
are left-linear, as is every `PredOrder` with archimedean predecessor, such as the rooted trees of
`Mathlib/Order/SuccPred/Tree.lean`, and left-linearity
[pulls back along an order embedding](##OrderEmbedding.isLeftLinear).

The flags of a left-linear order behave like the branches of a tree. A flag
[contains the past](##Flag.Iic_subset) of each of its elements, the down-set of a maximal element
[is a flag](##Flag.ofIsMax), and when `>` is well-founded
[every flag arises this way](##Flag.exists_isMax_eq_ofIsMax), so that quantifying over flags
[is quantifying over maximal elements](##Flag.forall_mem_iff).
-/

@[expose] public section

/-- An order is **left-linear** when the predecessors of every element are pairwise comparable,
so that it never branches backward. -/
class IsLeftLinear (M : Type*) [LE M] : Prop where
  /-- The predecessors of any element are pairwise comparable. -/
  le_total_of_le_of_le : ∀ ⦃a b c : M⦄, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

/-- A linear order is left-linear. -/
instance (priority := 100) {M : Type*} [LinearOrder M] : IsLeftLinear M :=
  ⟨fun a b _ _ _ ↦ le_total a b⟩

/-- A `PredOrder` with archimedean predecessor, such as a rooted tree, is left-linear. -/
instance (priority := 100) {M : Type*} [Preorder M] [PredOrder M] [IsPredArchimedean M] :
    IsLeftLinear M :=
  ⟨fun _ _ _ ha hb ↦ (le_total_of_directed ha hb).symm⟩

theorem OrderEmbedding.isLeftLinear {M N : Type*} [LE M] [LE N] [IsLeftLinear N] (f : M ↪o N) :
    IsLeftLinear M :=
  ⟨fun _ _ _ ha hb ↦ (IsLeftLinear.le_total_of_le_of_le (f.map_rel_iff.2 ha)
    (f.map_rel_iff.2 hb)).imp f.map_rel_iff.1 f.map_rel_iff.1⟩

/-- The order dual of an order is left-linear exactly when the successors of every element are
pairwise comparable, so that it never branches forward. -/
theorem isLeftLinear_orderDual_iff {M : Type*} [LE M] :
    IsLeftLinear Mᵒᵈ ↔ ∀ ⦃a b c : M⦄, c ≤ a → c ≤ b → a ≤ b ∨ b ≤ a :=
  ⟨fun h a b c ha hb ↦ (h.le_total_of_le_of_le (a := OrderDual.toDual a)
      (b := OrderDual.toDual b) (c := OrderDual.toDual c) ha hb).symm,
    fun h ↦ ⟨fun a b c ha hb ↦ (h (a := OrderDual.ofDual a) (b := OrderDual.ofDual b)
      (c := OrderDual.ofDual c) ha hb).symm⟩⟩

namespace IsLeftLinear

section Preorder

variable {M : Type*} [Preorder M] [IsLeftLinear M] {a b c : M}

/-- In a left-linear order the principal down-set `Iic m` is a chain. -/
theorem isChain_Iic (m : M) : IsChain (· ≤ ·) (Set.Iic m) :=
  fun _ ha _ hb _ ↦ le_total_of_le_of_le (Set.mem_Iic.1 ha) (Set.mem_Iic.1 hb)

/-- In a left-linear order two principal up-sets are disjoint exactly when their generators are
incomparable: the subtrees under two nodes of a tree share a node only when one node lies under
the other. -/
theorem disjoint_Ici_iff : Disjoint (Set.Ici a) (Set.Ici b) ↔ IncompRel (· ≤ ·) a b :=
  ⟨fun h ↦ ⟨fun hab ↦ Set.disjoint_left.1 h hab le_rfl,
      fun hba ↦ Set.disjoint_right.1 h hba le_rfl⟩,
    fun h ↦ Set.disjoint_left.2 fun _ ha hb ↦ (le_total_of_le_of_le ha hb).elim h.1 h.2⟩

/-- The left-linear form of `CovBy.le_of_lt`. -/
theorem le_of_lt_of_covBy (hab : a ⋖ b) (hcb : c < b) : c ≤ a :=
  (le_total_of_le_of_le hcb.le hab.le).elim id fun h ↦
    by_contra fun hca ↦ hab.2 (lt_of_le_not_ge h hca) hcb

end Preorder

section PartialOrder

variable {M : Type*} [PartialOrder M] [IsLeftLinear M] {a b c d x : M}

/-- The left-linear form of `CovBy.unique_left`: a node of a tree has at most one mother. -/
theorem covBy_unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
  (le_of_lt_of_covBy hb ha.lt).antisymm (le_of_lt_of_covBy ha hb.lt)

theorem eq_of_covBy_of_le (hc : a ⋖ c) (hd : a ⋖ d) (hcx : c ≤ x) (hdx : d ≤ x) : c = d :=
  (le_total_of_le_of_le hcx hdx).elim (fun h ↦ (hd.eq_or_eq hc.le h).resolve_left hc.ne')
    fun h ↦ ((hc.eq_or_eq hd.le h).resolve_left hd.ne').symm

end PartialOrder

end IsLeftLinear

theorem isLeftLinear_iff_forall_isChain_Iic {M : Type*} [Preorder M] :
    IsLeftLinear M ↔ ∀ m : M, IsChain (· ≤ ·) (Set.Iic m) :=
  ⟨fun _ ↦ IsLeftLinear.isChain_Iic, fun h ↦
    ⟨fun _ _ c ha hb ↦ (h c).total (Set.mem_Iic.2 ha) (Set.mem_Iic.2 hb)⟩⟩

/-! ### Branching

A node branches when it has two daughters. In a finite order in which every node with a daughter
branches, a topmost node with daughters has only maximal daughters, so some node has two maximal
daughters, a cherry in the language of phylogenetic trees. -/

section Branching

variable {M : Type*} [PartialOrder M]

/-- A node is branching when it has at least two covers. -/
def IsBranching (x : M) : Prop := {a | x ⋖ a}.Nontrivial

/-- An order with a branching element is not left-linear in its order dual. -/
theorem IsBranching.not_isLeftLinear_orderDual {x : M} (hx : IsBranching x) : ¬ IsLeftLinear Mᵒᵈ :=
  fun h ↦ by
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    rcases isLeftLinear_orderDual_iff.1 h ha.le hb.le with hle | hle
    · exact hab ((hb.eq_or_eq ha.le hle).resolve_left ha.ne')
    · exact hab ((ha.eq_or_eq hb.le hle).resolve_left hb.ne').symm

/-- In a finite order in which every non-maximal node branches, a non-maximal node yields a node
covered by two distinct maximal ones. -/
theorem exists_cherry [Finite M] (hb : ∀ x : M, ¬ IsMax x → IsBranching x) {x : M}
    (hx : ¬ IsMax x) : ∃ m a b : M, m ⋖ a ∧ m ⋖ b ∧ a ≠ b ∧ IsMax a ∧ IsMax b := by
  obtain ⟨m, hm, hmax⟩ := (Set.toFinite {y : M | ¬ IsMax y}).exists_maximal ⟨x, hx⟩
  obtain ⟨a, ha, b, hb', hab⟩ := hb m hm
  have key : ∀ c, m ⋖ c → IsMax c := fun c hc ↦ of_not_not fun h ↦ hc.lt.not_ge (hmax h hc.le)
  exact ⟨m, a, b, ha, hb', hab, key a ha, key b hb'⟩

end Branching

/-! ### Flags

In a left-linear order a flag, mathlib's maximal chain, is a branch: it contains the whole
past of each of its elements, and when `>` is well-founded it is the down-set of a maximal
element. -/

/-- Maximality is decidable on a finite type. -/
instance {M : Type*} [PartialOrder M] [Fintype M] [DecidableLE M] (x : M) :
    Decidable (IsMax x) :=
  decidable_of_iff (∀ b, x ≤ b → b ≤ x) Iff.rfl

namespace Flag

variable {M : Type*} [PartialOrder M] {m x y : M} {h : Flag M}

/-- A flag through a non-maximal element contains a strictly larger one; otherwise inserting
the successor would extend the chain. -/
theorem exists_mem_gt_of_lt (hm : m ∈ h) (hx : m < x) : ∃ y ∈ h, m < y := by
  by_contra! hcon
  have hxh : x ∈ h := mem_iff_forall_le_or_ge.2 fun b hb ↦ .inr <|
    (h.le_or_le hb hm).elim (fun hbm ↦ hbm.trans hx.le) fun hmb ↦
      (hmb.lt_or_eq.resolve_left (hcon b hb)) ▸ hx.le
  exact hcon x hxh hx

variable [IsLeftLinear M]

theorem Iic_subset (hm : m ∈ h) : Set.Iic m ⊆ (h : Set M) := fun _ hx ↦
  mem_iff_forall_le_or_ge.2 fun _ hb ↦ (h.le_or_le hb hm).elim
    (fun hbm ↦ IsLeftLinear.le_total_of_le_of_le hx hbm) fun hmb ↦ .inl (hx.trans hmb)

/-- The down-set of a maximal element of a left-linear order, as a flag. -/
def ofIsMax (hx : IsMax x) : Flag M where
  carrier := Set.Iic x
  Chain' := IsLeftLinear.isChain_Iic x
  max_chain' := fun _ hc hsub ↦ hsub.antisymm fun _ hy ↦
    (hc.total (hsub (Set.mem_Iic.2 le_rfl)) hy).elim (fun h ↦ hx h) id

@[simp, norm_cast] theorem coe_ofIsMax (hx : IsMax x) : (ofIsMax hx : Set M) = Set.Iic x := rfl

@[simp] theorem mem_ofIsMax {hx : IsMax x} : y ∈ ofIsMax hx ↔ y ≤ x := Iff.rfl

theorem eq_ofIsMax_of_mem (hx : IsMax x) (hxh : x ∈ h) : h = ofIsMax hx :=
  Flag.ext (Set.ext fun _ ↦ ⟨fun hy ↦ (h.le_or_le hy hxh).elim id fun hxy ↦ hx hxy,
    fun hy ↦ Iic_subset hxh hy⟩)

variable [WellFoundedGT M]

/-- When `>` is well-founded, as on a finite order, every flag of a left-linear order is the
down-set of a maximal element: the flag has a greatest element, which a strict successor would
contradict. -/
theorem exists_isMax_eq_ofIsMax [Nonempty M] (h : Flag M) :
    ∃ x, ∃ hx : IsMax x, h = ofIsMax hx := by
  obtain ⟨x, hx, hmax⟩ :=
    WellFounded.has_min (wellFounded_gt (α := M)) (h : Set M) (h.maxChain.nonempty_iff.1 ‹_›)
  refine ⟨x, fun y hxy ↦ ?_, eq_ofIsMax_of_mem _ hx⟩
  by_contra hyx
  obtain ⟨z, hz, hxz⟩ := exists_mem_gt_of_lt hx (lt_of_le_not_ge hxy hyx)
  exact hmax z hz hxz

/-- When `>` is well-founded, quantifying over the flags through an element of a left-linear
order is quantifying over the maximal elements above it. -/
theorem forall_mem_iff {P : Flag M → Prop} :
    (∀ h : Flag M, m ∈ h → P h) ↔ ∀ x, ∀ hx : IsMax x, m ≤ x → P (ofIsMax hx) :=
  ⟨fun H x hx hmx ↦ H _ hmx, fun H h hm ↦ by
    obtain ⟨x, hx, rfl⟩ := have : Nonempty M := ⟨m⟩; exists_isMax_eq_ofIsMax h
    exact H x hx hm⟩

end Flag
