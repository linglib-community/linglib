module

public import Linglib.Core.Order.PreorderLattice
public import Linglib.Core.Order.OfLowerSets.Defs
public import Mathlib.Order.Concept

/-!
# The lattice of orderings that families of sets induce

Every member of a family `A` is a lower set of `≤[A]`, and `≤[A]` is the coarsest preorder of
which that holds. Every preorder is induced by the family of its own lower sets. So `≤[A]` and
`Preorder.lowerSets` form a Galois insertion between families of sets and preorders, from which it
follows that more sets give a finer preorder, no sets give the preorder relating every two points,
and a union of families gives the meet.

## Main definitions

* `Preorder.lowerSets`: the lower sets of a preorder given as a term.
* `PremiseOrdering.gi`: the Galois insertion between families of sets and preorders.

## Main results

* `Preorder.le_ofLowerSets_iff`: a preorder refines `≤[A]` just in case every member of `A` is one
  of its lower sets.
* `Preorder.ofLowerSets_lowerSets`: every preorder is the ordering its lower sets induce.
* `Preorder.ofLowerSets_insert`: adding a set meets the ordering with that of the set.

## References

* [kratzer-1981]
* [lewis-1981]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Preorder

variable {α : Type*} {A B : Set (Set α)} {a b : α}

/-! ### A single predicate -/

section ofCriterion

variable {p : Preorder α} {P : α → Prop}

theorem le_ofCriterion_iff : p ≤ ofCriterion P ↔ ∀ ⦃a b⦄, p.le a b → P b → P a :=
  Iff.rfl

/-- A preorder lies below the preorder of a predicate exactly when the elements satisfying the
predicate form a lower set. -/
theorem le_ofCriterion_iff_isLowerSet : p ≤ ofCriterion P ↔ @IsLowerSet α p.toLE {a | P a} :=
  ⟨fun h _ _ hba ↦ h hba, fun h _ _ hab ↦ h hab⟩

@[simp] theorem ofCriterion_const (q : Prop) : ofCriterion (fun _ : α ↦ q) = ⊤ :=
  top_unique fun _ _ _ ↦ id

/-- A preorder ranks `a` below `b` exactly when `a` satisfies every predicate that `b` satisfies
among the predicates whose satisfiers form a lower set. -/
theorem le_iff_forall_le_ofCriterion : p.le a b ↔ ∀ P, p ≤ ofCriterion P → P b → P a :=
  ⟨fun h _ hP ↦ hP h,
    fun h ↦ h (p.le · b) (fun _ _ hac hcb ↦ p.le_trans _ _ _ hac hcb) (p.le_refl b)⟩

theorem ofLowerSets_singleton (s : Set α) : ≤[{s}] = ofCriterion (· ∈ s) :=
  Preorder.ext fun _ _ ↦ forall_eq

end ofCriterion

/-! ### The Galois insertion with the lower sets of a preorder -/

/-- The lower sets of a preorder given as a term. -/
def lowerSets (p : Preorder α) : Set (Set α) := {s | @IsLowerSet α p.toLE s}

@[simp] theorem mem_lowerSets {p : Preorder α} {s : Set α} :
    s ∈ p.lowerSets ↔ @IsLowerSet α p.toLE s := Iff.rfl

/-- A preorder refines the ordering of `A` just in case every member of `A` is one of its lower
sets. -/
theorem le_ofLowerSets_iff {p : Preorder α} : p ≤ ≤[A] ↔ A ⊆ p.lowerSets :=
  ⟨fun h _ hs _ _ hba ha ↦ h hba _ hs ha, fun h _ _ hab _ hs hb ↦ h hs hab hb⟩

/-- Every member of a family is a lower set of the ordering it induces. -/
theorem subset_lowerSets_ofLowerSets (A : Set (Set α)) : A ⊆ (≤[A]).lowerSets :=
  le_ofLowerSets_iff.1 le_rfl

/-- If every member of `A` is closed downward under a relation `r`, then at a point `b` related to
itself, with `{a | r a b}` a member, the ordering of `A` is `r`. No transitivity is assumed. -/
theorem ofLowerSets_le_iff_of_mem {r : α → α → Prop}
    (hlow : ∀ s ∈ A, ∀ ⦃a b⦄, r a b → b ∈ s → a ∈ s) (hr : r b b) (hb : {a | r a b} ∈ A) :
    (a ≤[A] b) ↔ r a b :=
  ⟨fun h ↦ h _ hb hr, fun h s hs ↦ hlow s hs h⟩

/-- A family of lower sets of a preorder that contains every principal lower set induces that
preorder. -/
theorem ofLowerSets_eq_of_subset_lowerSets (p : Preorder α) (hlow : A ⊆ p.lowerSets)
    (hprin : ∀ b, {a | p.le a b} ∈ A) : ≤[A] = p :=
  Preorder.ext fun _ b ↦
    ofLowerSets_le_iff_of_mem (fun _ hs _ _ h hb ↦ hlow hs h hb) (p.le_refl b) (hprin b)

/-- Every preorder is the ordering its lower sets induce. -/
@[simp] theorem ofLowerSets_lowerSets (p : Preorder α) : ≤[p.lowerSets] = p :=
  ofLowerSets_eq_of_subset_lowerSets p subset_rfl
    fun b _ _ hab (ha : p.le _ b) ↦ p.le_trans _ _ _ hab ha

end Preorder

/-- The ordering a family of sets induces and the lower sets of a preorder form a Galois insertion
between families of sets and preorders: a preorder refines `≤[A]` just in case every member of `A`
is one of its lower sets, and every preorder is induced by its own lower sets. Both maps reverse
inclusion, so it is stated into the dual order. Its closure operator sends `A` to
`(≤[A]).lowerSets`, the largest family inducing the ordering of `A`. -/
protected def PremiseOrdering.gi {α : Type*} :
    GaloisInsertion (fun A : Set (Set α) ↦ OrderDual.toDual (≤[A]))
      (fun p ↦ (OrderDual.ofDual p).lowerSets) :=
  GaloisConnection.toGaloisInsertion (fun _ _ ↦ Preorder.le_ofLowerSets_iff)
    fun p ↦ (Preorder.ofLowerSets_lowerSets (OrderDual.ofDual p)).le

namespace Preorder

variable {α : Type*} {A B : Set (Set α)}

/-- More sets give a finer ordering. -/
theorem ofLowerSets_anti : Antitone (ofLowerSets (α := α)) :=
  fun _ _ h ↦ PremiseOrdering.gi.gc.monotone_l h

/-- No sets give the ordering relating every two points. -/
@[simp] theorem ofLowerSets_empty : ≤[(∅ : Set (Set α))] = ⊤ :=
  congrArg OrderDual.ofDual (PremiseOrdering.gi (α := α)).gc.l_bot

/-- The ordering of a union of families is the meet of their orderings. -/
theorem ofLowerSets_union (A B : Set (Set α)) : ≤[A ∪ B] = ≤[A] ⊓ ≤[B] :=
  congrArg OrderDual.ofDual (PremiseOrdering.gi.gc.l_sup (a₁ := A) (a₂ := B))

/-- Adding a set meets the ordering with the ordering of that set. -/
theorem ofLowerSets_insert (s : Set α) (A : Set (Set α)) :
    ≤[insert s A] = ≤[A] ⊓ ofCriterion (· ∈ s) := by
  rw [← Set.union_singleton, ofLowerSets_union, ofLowerSets_singleton]

/-- Sets that are lower sets of the ordering of `A` can be added to `A` without changing it. -/
theorem ofLowerSets_eq_of_subset (h₁ : A ⊆ B) (h₂ : ∀ s ∈ B, ≤[A] ≤ ofCriterion (· ∈ s)) :
    ≤[B] = ≤[A] :=
  le_antisymm (ofLowerSets_anti h₁)
    (le_ofLowerSets_iff.2 fun _ hs ↦ le_ofCriterion_iff_isLowerSet.1 (h₂ _ hs))

end Preorder
