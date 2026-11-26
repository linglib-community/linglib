module

public import Linglib.Core.Order.Compare
public import Linglib.Logic.Temporal.PartitionScheme
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Powerset

/-!
# The point algebra

An element of the point algebra of [vilain-kautz-1986] is a set of the orderings in which one
point of a linear order may stand to another, read as the disjunction of the relations `<`, `=`
and `>` that it contains. Elements form a Boolean algebra with a converse and a composition whose
unit is `{eq}`; composition distributes over joins, which the `IdemSemiring` instance records.
Each element is a [relation](##PointAlgebra.toSetRel) on any ordered type. On a linear order with
two points the relations [order as the elements do](##PointAlgebra.toSetRel_subset_toSetRel_iff),
and passing to the relation preserves joins, complements and converses. The relation of a product
contains the composite of the relations, and is the composite for all elements [exactly when the
order is dense and has no least or greatest point](##PointAlgebra.toSetRel_mul_iff), where the
algebra is that of the relations definable from `<`. In the terms of [ligozat-renz-2004] the
orderings are the basic relations of the partition scheme of a linear order
(`PointAlgebra.scheme`), reading an element as a relation is a weak representation, and the
product is weak composition on dense time without endpoints (`PointAlgebra.weakComp_eq_mul`).

## References

* [vilain-kautz-1986]
* [ligozat-renz-2004]
-/

@[expose] public section

/-- An element of the point algebra is a set of orderings, the positions in which one point may
stand to another. -/
def PointAlgebra : Type := Finset Ordering
deriving DecidableEq, Fintype, BooleanAlgebra, Membership, Singleton, Insert

namespace PointAlgebra

open SetRel

variable {C D : PointAlgebra} {o a : Ordering}

instance : DecidablePred (· ∈ C) := fun o ↦ Finset.decidableMem o C

instance : DecidableLE PointAlgebra := fun (C D : Finset Ordering) ↦
  inferInstanceAs (Decidable (C ⊆ D))

@[simp] theorem mem_singleton : o ∈ ({a} : PointAlgebra) ↔ o = a := Finset.mem_singleton

@[simp] theorem mem_insert : o ∈ (insert a C : PointAlgebra) ↔ o = a ∨ o ∈ C := Finset.mem_insert

@[simp] theorem mem_sup : o ∈ C ⊔ D ↔ o ∈ C ∨ o ∈ D := Finset.mem_union

@[simp] theorem mem_compl : o ∈ Cᶜ ↔ o ∉ C := Finset.mem_compl

@[simp] theorem mem_top : o ∈ (⊤ : PointAlgebra) := Finset.mem_univ o

@[simp] theorem notMem_bot : o ∉ (⊥ : PointAlgebra) := Finset.notMem_empty o

/-! ### Composition -/

/-- The unit is equality. -/
instance : One PointAlgebra := ⟨({.eq} : Finset Ordering)⟩

/-- `C * D` holds of a point and a third when the third stands to some second in `D` and the
second to the point in `C`. -/
instance : Mul PointAlgebra := ⟨fun C D ↦ Finset.biUnion D fun d ↦ Finset.biUnion C d.comp⟩

@[simp] theorem mem_one : o ∈ (1 : PointAlgebra) ↔ o = .eq := Finset.mem_singleton

theorem mem_mul : o ∈ C * D ↔ ∃ d ∈ D, ∃ c ∈ C, o ∈ d.comp c := by
  change o ∈ Finset.biUnion D _ ↔ _
  simp only [Finset.mem_biUnion]

instance : Add PointAlgebra := ⟨(· ⊔ ·)⟩

instance : Zero PointAlgebra := ⟨⊥⟩

instance : IdemSemiring PointAlgebra where
  __ := (inferInstance : SemilatticeSup PointAlgebra)
  __ := (inferInstance : OrderBot PointAlgebra)
  nsmul := nsmulRec
  nsmul_zero := fun _ ↦ rfl
  nsmul_succ := fun _ _ ↦ rfl
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide

theorem add_eq_sup (C D : PointAlgebra) : C + D = C ⊔ D := rfl

theorem zero_eq_bot : (0 : PointAlgebra) = ⊥ := rfl

/-! ### Converse -/

/-- The converse exchanges `<` with `>`. -/
instance : InvolutiveInv PointAlgebra where
  inv C := Finset.image Ordering.swap C
  inv_inv := by decide

@[simp] theorem mem_inv : o ∈ C⁻¹ ↔ o.swap ∈ C := by
  change o ∈ Finset.image Ordering.swap C ↔ _
  rw [Finset.mem_image]
  exact ⟨fun ⟨a, ha, h⟩ ↦ by rwa [← h, Ordering.swap_swap], fun h ↦ ⟨_, h, o.swap_swap⟩⟩

theorem mul_inv_rev (C D : PointAlgebra) : (C * D)⁻¹ = D⁻¹ * C⁻¹ := by
  revert C D
  decide

/-! ### The relation of an element -/

variable {T : Type*} {x y : T}

section LT

variable [LT T]

/-- The relation of an element relates a point to the points that stand to it in one of the
element's orderings. -/
def toSetRel (C : PointAlgebra) : SetRel T T := {p | ∃ o ∈ C, o.Compares p.2 p.1}

theorem mem_toSetRel : x ~[toSetRel C] y ↔ ∃ o ∈ C, o.Compares y x := .rfl

@[simp] theorem mem_toSetRel_lt : x ~[toSetRel {.lt}] y ↔ y < x := by
  simp [mem_toSetRel]

@[simp] theorem mem_toSetRel_gt : x ~[toSetRel {.gt}] y ↔ x < y := by
  simp [mem_toSetRel]

@[simp] theorem mem_toSetRel_one : x ~[toSetRel 1] y ↔ y = x := by
  simp [mem_toSetRel]

@[simp] theorem toSetRel_one : (toSetRel 1 : SetRel T T) = SetRel.id := by
  ext ⟨x, y⟩
  exact mem_toSetRel_one.trans eq_comm

theorem mem_toSetRel_top : x ~[toSetRel ⊤] y ↔ y < x ∨ y = x ∨ x < y :=
  ⟨fun ⟨o, _, h⟩ ↦ by cases o; exacts [.inl h, .inr (.inl h), .inr (.inr h)],
    fun h ↦ h.elim (⟨.lt, mem_top, ·⟩) fun h ↦ h.elim (⟨.eq, mem_top, ·⟩) (⟨.gt, mem_top, ·⟩)⟩

@[simp] theorem toSetRel_bot : (toSetRel ⊥ : SetRel T T) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, ho, _⟩ ↦ notMem_bot ho

theorem toSetRel_sup (C D : PointAlgebra) :
    (toSetRel (C ⊔ D) : SetRel T T) = toSetRel C ∪ toSetRel D := by
  ext ⟨x, y⟩
  simp only [mem_toSetRel, mem_sup, or_and_right, exists_or, Set.mem_union]

@[gcongr] theorem toSetRel_mono (h : C ≤ D) : (toSetRel C : SetRel T T) ⊆ toSetRel D :=
  fun _ ⟨o, ho, hc⟩ ↦ ⟨o, h ho, hc⟩

theorem toSetRel_inv (C : PointAlgebra) : (toSetRel C⁻¹ : SetRel T T) = (toSetRel C).inv := by
  ext ⟨x, y⟩
  simp only [SetRel.mem_inv, mem_toSetRel, mem_inv]
  exact ⟨fun ⟨o, ho, h⟩ ↦ ⟨o.swap, ho, Ordering.compares_swap.2 h⟩,
    fun ⟨o, ho, h⟩ ↦ ⟨o.swap, by rwa [Ordering.swap_swap], Ordering.compares_swap.2 h⟩⟩

/-- The relation `<` relates a point to a smaller one through a third exactly when the order is
dense. -/
theorem toSetRel_lt_subset_comp_self_iff :
    (toSetRel {.lt} : SetRel T T) ⊆ toSetRel {.lt} ○ toSetRel {.lt} ↔ DenselyOrdered T where
  mp h := ⟨fun _ _ hab ↦ let ⟨c, h₁, h₂⟩ := h (mem_toSetRel_lt.2 hab)
    ⟨c, mem_toSetRel_lt.1 h₂, mem_toSetRel_lt.1 h₁⟩⟩
  mpr _ := fun _ h ↦ let ⟨c, h₁, h₂⟩ := exists_between (mem_toSetRel_lt.1 h)
    ⟨c, mem_toSetRel_lt.2 h₂, mem_toSetRel_lt.2 h₁⟩

/-- The relation `>` relates a point to a greater one through a third exactly when the order is
dense. -/
theorem toSetRel_gt_subset_comp_self_iff :
    (toSetRel {.gt} : SetRel T T) ⊆ toSetRel {.gt} ○ toSetRel {.gt} ↔ DenselyOrdered T where
  mp h := ⟨fun _ _ hab ↦ let ⟨c, h₁, h₂⟩ := h (mem_toSetRel_gt.2 hab)
    ⟨c, mem_toSetRel_gt.1 h₁, mem_toSetRel_gt.1 h₂⟩⟩
  mpr _ := fun _ h ↦ let ⟨c, h₁, h₂⟩ := exists_between (mem_toSetRel_gt.1 h)
    ⟨c, mem_toSetRel_gt.2 h₁, mem_toSetRel_gt.2 h₂⟩

end LT

/-- The relation of the top element is comparability. -/
theorem mem_toSetRel_top_iff_le [PartialOrder T] : x ~[toSetRel ⊤] y ↔ x ≤ y ∨ y ≤ x := by
  rw [mem_toSetRel_top]
  refine ⟨?_, fun h ↦ h.elim (fun h ↦ ?_) fun h ↦ ?_⟩
  · rintro (h | rfl | h)
    exacts [.inr h.le, .inl le_rfl, .inl h.le]
  · obtain rfl | h := h.eq_or_lt
    exacts [.inr (.inl rfl), .inr (.inr h)]
  · obtain rfl | h := h.eq_or_lt
    exacts [.inr (.inl rfl), .inl h]

instance [Preorder T] : (toSetRel {.lt} : SetRel T T).IsTrans :=
  ⟨fun _ _ _ h₁ h₂ ↦ mem_toSetRel_lt.2 ((mem_toSetRel_lt.1 h₂).trans (mem_toSetRel_lt.1 h₁))⟩

instance [Preorder T] : (toSetRel {.gt} : SetRel T T).IsTrans :=
  ⟨fun _ _ _ h₁ h₂ ↦ mem_toSetRel_gt.2 ((mem_toSetRel_gt.1 h₁).trans (mem_toSetRel_gt.1 h₂))⟩

section LinearOrder

variable [LinearOrder T]

@[simp] theorem mem_toSetRel_iff : x ~[toSetRel C] y ↔ compare y x ∈ C :=
  ⟨fun ⟨_, ho, hc⟩ ↦ (compare_iff y x).2 hc ▸ ho, fun h ↦ ⟨_, h, (compare_iff y x).1 rfl⟩⟩

instance : Decidable (x ~[toSetRel C] y) := decidable_of_iff _ mem_toSetRel_iff.symm

theorem compare_mem_mul {a b c : T} (h₁ : compare a b ∈ D) (h₂ : compare b c ∈ C) :
    compare a c ∈ C * D :=
  mem_mul.2 ⟨_, h₁, _, h₂, Ordering.compare_mem_comp a b c⟩

theorem compare_mem_mul_iff [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] {a c : T} :
    compare a c ∈ C * D ↔ ∃ b, compare a b ∈ D ∧ compare b c ∈ C := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h₁, h₂⟩ ↦ compare_mem_mul h₁ h₂⟩
  obtain ⟨d, hd, c, hc, h⟩ := mem_mul.1 h
  obtain ⟨b, rfl, rfl⟩ := Ordering.exists_compare_eq_of_mem_comp h
  exact ⟨b, hd, hc⟩

@[simp] theorem toSetRel_top : (toSetRel ⊤ : SetRel T T) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_toSetRel_iff.2 mem_top

/-- On a linear order with two points the relations of two elements are ordered as the elements
are. -/
theorem toSetRel_subset_toSetRel_iff [Nontrivial T] :
    (toSetRel C : SetRel T T) ⊆ toSetRel D ↔ C ≤ D := by
  refine ⟨fun h o ho ↦ ?_, toSetRel_mono⟩
  obtain ⟨a, b, hab⟩ := exists_pair_lt T
  obtain ⟨x, y, rfl⟩ : ∃ x y : T, compare y x = o := by
    cases o
    exacts [⟨b, a, compare_lt_iff_lt.2 hab⟩, ⟨a, a, compare_eq_iff_eq.2 rfl⟩,
      ⟨a, b, compare_gt_iff_gt.2 hab⟩]
  exact mem_toSetRel_iff.1 (h (mem_toSetRel_iff.2 ho))

theorem toSetRel_injective [Nontrivial T] :
    Function.Injective (toSetRel : PointAlgebra → SetRel T T) := fun _ _ h ↦
  le_antisymm (toSetRel_subset_toSetRel_iff.1 h.subset) (toSetRel_subset_toSetRel_iff.1 h.superset)

theorem toSetRel_compl (C : PointAlgebra) : (toSetRel Cᶜ : SetRel T T) = (toSetRel C)ᶜ := by
  ext ⟨x, y⟩
  simp only [mem_toSetRel_iff, Set.mem_compl_iff, mem_compl]

theorem toSetRel_comp_subset (C D : PointAlgebra) :
    toSetRel C ○ toSetRel D ⊆ (toSetRel (C * D) : SetRel T T) :=
  fun _ ⟨_, h₁, h₂⟩ ↦
    mem_toSetRel_iff.2 (compare_mem_mul (mem_toSetRel_iff.1 h₂) (mem_toSetRel_iff.1 h₁))

/-- On a dense order without endpoints the relation of a product is the composite of the
relations. -/
theorem toSetRel_mul [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] (C D : PointAlgebra) :
    (toSetRel (C * D) : SetRel T T) = toSetRel C ○ toSetRel D := by
  refine (Set.Subset.antisymm (fun ⟨x, y⟩ h ↦ ?_) (toSetRel_comp_subset C D))
  obtain ⟨b, hd, hc⟩ := compare_mem_mul_iff.1 (mem_toSetRel_iff.1 h)
  exact ⟨b, mem_toSetRel_iff.2 hc, mem_toSetRel_iff.2 hd⟩

/-- The relation of a product is the composite of the relations for all elements exactly when
the order is dense and has no least or greatest point: density comes from `<` composed with
itself, and a point below and above each point from `<` composed with `>`, which is `⊤`. -/
theorem toSetRel_mul_iff :
    (∀ C D : PointAlgebra, (toSetRel (C * D) : SetRel T T) = toSetRel C ○ toSetRel D) ↔
      DenselyOrdered T ∧ NoMinOrder T ∧ NoMaxOrder T := by
  refine ⟨fun h ↦ ⟨?_, ⟨fun t ↦ ?_⟩, ⟨fun t ↦ ?_⟩⟩, fun ⟨_, _, _⟩ ↦ toSetRel_mul⟩
  · exact toSetRel_lt_subset_comp_self_iff.1 (h {.lt} {.lt}).subset
  · obtain ⟨s, hs, -⟩ := (h {.lt} {.gt}).subset
      (mem_toSetRel_iff.2 ((by decide : ({.lt} : PointAlgebra) * {.gt} = ⊤) ▸ mem_top) : (t, t) ∈ _)
    exact ⟨s, mem_toSetRel_lt.1 hs⟩
  · obtain ⟨s, hs, -⟩ := (h {.gt} {.lt}).subset
      (mem_toSetRel_iff.2 ((by decide : ({.gt} : PointAlgebra) * {.lt} = ⊤) ▸ mem_top) : (t, t) ∈ _)
    exact ⟨s, mem_toSetRel_gt.1 hs⟩

/-! ### The partition scheme of a linear order -/

/-- The partition scheme of a linear order: two points stand in `<`, `=` or `>`. -/
def scheme (T : Type*) [LinearOrder T] : PartitionScheme T Ordering where
  index p := compare p.2 p.1
  inv := Ordering.swap
  index_swap _ := Std.OrientedCmp.eq_swap

/-- The relation of an element is the relation of its orderings in the scheme of the order. -/
theorem toSetRel_eq_rel (C : PointAlgebra) :
    (toSetRel C : SetRel T T) = (scheme T).rel {o | o ∈ C} := by
  ext ⟨x, y⟩
  exact mem_toSetRel_iff

/-- The weak composition of two elements on any linear order lies in their product. -/
theorem weakComp_subset_mul (C D : PointAlgebra) :
    (scheme T).weakComp {o | o ∈ C} {o | o ∈ D} ⊆ {o | o ∈ C * D} := by
  rintro _ ⟨⟨x, z⟩, ⟨y, h₁, h₂⟩, rfl⟩
  exact compare_mem_mul h₂ h₁

/-- On dense time without endpoints the product of two elements is their weak composition, so
the point algebra is the algebra of the partition scheme of such an order. -/
theorem weakComp_eq_mul [DenselyOrdered T] [NoMinOrder T] [NoMaxOrder T] [Nontrivial T]
    (C D : PointAlgebra) : (scheme T).weakComp {o | o ∈ C} {o | o ∈ D} = {o | o ∈ C * D} := by
  refine (weakComp_subset_mul C D).antisymm fun o ho ↦ ?_
  obtain ⟨a, b, hab⟩ := exists_pair_lt T
  obtain ⟨x, z, rfl⟩ : ∃ x z : T, compare z x = o := by
    cases o
    exacts [⟨b, a, compare_lt_iff_lt.2 hab⟩, ⟨a, a, compare_eq_iff_eq.2 rfl⟩,
      ⟨a, b, compare_gt_iff_gt.2 hab⟩]
  obtain ⟨y, hD, hC⟩ := compare_mem_mul_iff.1 ho
  exact ⟨(x, z), ⟨y, hC, hD⟩, rfl⟩

end LinearOrder

end PointAlgebra
