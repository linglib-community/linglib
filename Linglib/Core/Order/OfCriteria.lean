module

public import Linglib.Core.Order.PreorderLattice
public import Mathlib.Order.Concept

/-!
# The criteria-derived preorder

This file defines the preorder that a family of criteria induces on a type. Given a relation
`sat : α → C → Prop` and a set of criteria, `Preorder.ofCriteria sat criteria` ranks `a` below
`b` when `a` satisfies every criterion of the set that `b` satisfies. It is the pullback of `⊇`
along the map sending an element to the set of criteria it satisfies
(`ofCriteria_le_iff_subset`). Adding a criterion meets the preorder with the preorder of that
single criterion, under which the elements satisfying it form a lower set.

## Main declarations

* `Preorder.ofCriteria`: the criteria-derived preorder.
* `Preorder.ofCriteria_empty`: no criteria give the total order.
* `Preorder.ofCriterion`, `Preorder.ofCriteria_insert`: the preorder of a single criterion.
* `Preorder.satisfied`: the criteria that an element satisfies.
-/

@[expose] public section

namespace Preorder

variable {α C : Type*}

/-- The criteria-derived preorder ranks `a` below `b` when `a` satisfies every criterion in
`criteria` that `b` satisfies. -/
@[reducible] def ofCriteria (sat : α → C → Prop) (criteria : Set C) :
    Preorder α where
  le a b := ∀ c ∈ criteria, sat b c → sat a c
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc c hc h := hab c hc (hbc c hc h)

theorem ofCriteria_le_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).le a b ↔ ∀ c ∈ criteria, sat b c → sat a c :=
  Iff.rfl

theorem ofCriteria_lt_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).lt a b ↔
      (ofCriteria sat criteria).le a b ∧ ¬ (ofCriteria sat criteria).le b a :=
  Iff.rfl

theorem ofCriteria_le_iff_subset (sat : α → C → Prop) (criteria : Set C)
    (a b : α) :
    (ofCriteria sat criteria).le a b ↔
      {c ∈ criteria | sat b c} ⊆ {c ∈ criteria | sat a c} :=
  ⟨fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩, fun h _ hc hb ↦ (h ⟨hc, hb⟩).2⟩

/-- No criteria give the order relating every two elements. -/
@[simp] theorem ofCriteria_empty (sat : α → C → Prop) : ofCriteria sat ∅ = ⊤ :=
  top_unique fun _ _ _ _ h ↦ h.elim

/-! ### A single criterion -/

section ofCriterion

variable {p : Preorder α} {P : α → Prop} {a b : α}

/-- The preorder of a single criterion ranks `a` below `b` when `a` satisfies the criterion
whenever `b` does. It is defined directly rather than as `ofCriteria` on a singleton, so that its
meet with another preorder unfolds to a conjunction. -/
@[reducible] def ofCriterion (P : α → Prop) : Preorder α :=
  ofLE (fun a b ↦ P b → P a) (fun _ ↦ id) fun _ _ _ hab hbc h ↦ hab (hbc h)

theorem le_ofCriterion_iff : p ≤ ofCriterion P ↔ ∀ ⦃a b⦄, p.le a b → P b → P a :=
  Iff.rfl

/-- A preorder lies below the preorder of a criterion exactly when the elements satisfying the
criterion form a lower set. -/
theorem le_ofCriterion_iff_isLowerSet : p ≤ ofCriterion P ↔ @IsLowerSet α p.toLE {a | P a} :=
  ⟨fun h _ _ hba ↦ h hba, fun h _ _ hab ↦ h hab⟩

@[simp] theorem ofCriterion_const (q : Prop) : ofCriterion (fun _ : α ↦ q) = ⊤ :=
  top_unique fun _ _ _ ↦ id

/-- A preorder ranks `a` below `b` exactly when `a` satisfies every criterion that `b` satisfies
among the criteria whose satisfiers form a lower set. -/
theorem le_iff_forall_le_ofCriterion : p.le a b ↔ ∀ P, p ≤ ofCriterion P → P b → P a :=
  ⟨fun h _ hP ↦ hP h,
    fun h ↦ h (p.le · b) (fun _ _ hac hcb ↦ p.le_trans _ _ _ hac hcb) (p.le_refl b)⟩

theorem ofCriteria_singleton (sat : α → C → Prop) (c : C) :
    ofCriteria sat {c} = ofCriterion (sat · c) :=
  Preorder.ext fun _ _ ↦ forall_eq

/-- Adding a criterion meets the criteria-derived preorder with the preorder of that criterion. -/
theorem ofCriteria_insert (sat : α → C → Prop) (c : C) (criteria : Set C) :
    ofCriteria sat (insert c criteria) = ofCriteria sat criteria ⊓ ofCriterion (sat · c) :=
  Preorder.ext fun _ _ ↦ Set.forall_mem_insert.trans and_comm

end ofCriterion

/-! ### The satisfied criteria as a valuation -/

/-- The criteria that `a` satisfies. The criteria-derived order is the pullback of `⊇` along this
map (`satisfied_subset_iff`), so the minimal elements of the order are the `MaximalFor` elements of
the map: the best elements are those satisfying a maximal set of criteria, with no order instance
on the type. -/
def satisfied (sat : α → C → Prop) (criteria : Set C) (a : α) : Set C :=
  {c ∈ criteria | sat a c}

@[simp] theorem mem_satisfied {sat : α → C → Prop} {criteria : Set C} {a : α} {c : C} :
    c ∈ satisfied sat criteria a ↔ c ∈ criteria ∧ sat a c :=
  Iff.rfl

@[simp] theorem mem_satisfied_univ {sat : α → C → Prop} {a : α} {c : C} :
    c ∈ satisfied sat Set.univ a ↔ sat a c :=
  ⟨And.right, fun h ↦ ⟨trivial, h⟩⟩

theorem satisfied_subset_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    satisfied sat criteria a ⊆ satisfied sat criteria b ↔ (ofCriteria sat criteria).le b a :=
  (ofCriteria_le_iff_subset sat criteria b a).symm

instance (sat : α → C → Prop) (l : List C) [DecidableEq C] [∀ a c, Decidable (sat a c)]
    (a b : α) : Decidable (satisfied sat {c | c ∈ l} a ≤ satisfied sat {c | c ∈ l} b) :=
  decidable_of_iff (∀ c ∈ l, sat a c → sat b c) (by
    simp only [satisfied_subset_iff, ofCriteria_le_iff, Set.mem_ofPred_eq])

end Preorder
