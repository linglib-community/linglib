module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.Antisymmetrization

/-!
# The ordering a family of sets induces

A family `A` of sets orders the points: `a` lies below `b` when every member of `A` containing `b`
contains `a`. We write this preorder `≤[A]`. It is the pullback of `⊇` along the map sending a
point to the members of `A` containing it, two points are equivalent in it exactly when they lie
in the same members, and the complements of the members induce the reverse ordering.

## Main definitions

* `Preorder.ofCriterion`: the ordering of a single predicate.
* `Preorder.ofLowerSets`, with notation `≤[A]`, `w ≤[A] z`, `w <[A] z` in the scope
  `PremiseOrdering`: the ordering a family of sets induces.

## Main results

* `Preorder.ofLowerSets_le_iff_subset`: a point lies below another just in case it lies in every
  member the other lies in.
* `Preorder.ofLowerSets_image_compl_le_iff`: the complements of a family induce the reverse
  ordering.
* `Preorder.ofLowerSets_eq_lift`: the ordering is the pullback of `⊇` along the map sending a
  point to the members of `A` containing it.

## Implementation notes

`Preorder.ofLowerSets` is defined by its unfolded condition `∀ s ∈ A, b ∈ s → a ∈ s` and not as
`Preorder.lift` along the map `fun a ↦ {s ∈ A | a ∈ s}`, so that the order of an inserted set
unfolds to a conjunction and membership in `A` is not repeated on both sides. The two agree by
`Preorder.ofLowerSets_eq_lift`.

## References

* [kratzer-1981]
* [lewis-1981]
-/

@[expose] public section

namespace Preorder

variable {α : Type*}

/-- The ordering a family `A` of sets induces ranks `a` below `b` when every member of `A`
containing `b` contains `a`. -/
@[reducible] def ofLowerSets (A : Set (Set α)) : Preorder α where
  le a b := ∀ s ∈ A, b ∈ s → a ∈ s
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc s hs h := hab s hs (hbc s hs h)

end Preorder

/-- `≤[A]` is the ordering a family `A` of propositions induces on the worlds, ranking `w` below
`z` when every proposition of `A` true at `z` is true at `w`. -/
scoped[PremiseOrdering] notation "≤[" A "]" => Preorder.ofLowerSets A

/-- `w ≤[A] z` says that `w` is at least as good as `z` under the premise set `A`, verifying every
premise of `A` that `z` verifies. -/
scoped[PremiseOrdering] notation:50 w " ≤[" A "] " z =>
  @LE.le _ (@Preorder.toLE _ (Preorder.ofLowerSets A)) w z

/-- `w <[A] z` says that `w` is strictly better than `z` under the premise set `A`. -/
scoped[PremiseOrdering] notation:50 w " <[" A "] " z =>
  @LT.lt _ (@Preorder.toLT _ (Preorder.ofLowerSets A)) w z

open scoped PremiseOrdering

namespace Preorder

variable {α : Type*} {A B : Set (Set α)} {a b : α}

theorem ofLowerSets_le_iff (A : Set (Set α)) (a b : α) :
    (a ≤[A] b) ↔ ∀ s ∈ A, b ∈ s → a ∈ s :=
  Iff.rfl

theorem ofLowerSets_lt_iff (A : Set (Set α)) (a b : α) :
    (a <[A] b) ↔ (a ≤[A] b) ∧ ¬ (b ≤[A] a) :=
  Iff.rfl

theorem ofLowerSets_le_iff_subset (A : Set (Set α)) (a b : α) :
    (a ≤[A] b) ↔ {s ∈ A | b ∈ s} ⊆ {s ∈ A | a ∈ s} :=
  ⟨fun h _ hs ↦ ⟨hs.1, h _ hs.1 hs.2⟩, fun h _ hs hb ↦ (h ⟨hs, hb⟩).2⟩

/-- A family indexed by another type induces the ordering of its image. -/
theorem ofLowerSets_image_le_iff {ι : Type*} (f : ι → Set α) (I : Set ι) (a b : α) :
    (a ≤[f '' I] b) ↔ ∀ i ∈ I, b ∈ f i → a ∈ f i :=
  Set.forall_mem_image

/-- The complements of a family induce the reverse ordering. -/
theorem ofLowerSets_image_compl_le_iff (A : Set (Set α)) (a b : α) :
    (a ≤[compl '' A] b) ↔ (b ≤[A] a) := by
  simp only [ofLowerSets_le_iff, Set.forall_mem_image, Set.mem_compl_iff, not_imp_not]

/-- The ordering is the pullback of `⊇` along the map sending a point to the members of `A`
containing it. -/
theorem ofLowerSets_eq_lift (A : Set (Set α)) :
    ≤[A] = Preorder.lift fun a ↦ OrderDual.toDual {s ∈ A | a ∈ s} :=
  Preorder.ext fun a b ↦ ofLowerSets_le_iff_subset A a b

/-- Two points are equivalent exactly when they lie in the same members of `A`. -/
theorem antisymmRel_ofLowerSets_iff :
    AntisymmRel (≤[A]).le a b ↔ {s ∈ A | a ∈ s} = {s ∈ A | b ∈ s} :=
  ((ofLowerSets_le_iff_subset A a b).and (ofLowerSets_le_iff_subset A b a))
    |>.trans (and_comm.trans Set.Subset.antisymm_iff.symm)

/-! ### A single predicate -/

/-- The preorder of a single predicate ranks `a` below `b` when `a` satisfies the predicate
whenever `b` does. It is defined directly rather than as the ordering of a singleton, so that its
meet with another preorder unfolds to a conjunction. -/
@[reducible] def ofCriterion (P : α → Prop) : Preorder α where
  le a b := P b → P a
  le_refl _ := id
  le_trans _ _ _ hab hbc h := hab (hbc h)
  lt a b := (P b → P a) ∧ ¬ (P a → P b)
  lt_iff_le_not_ge _ _ := Iff.rfl

instance {C : Type*} (sat : α → C → Prop) (l : List C) [∀ a c, Decidable (sat a c)] (a b : α) :
    Decidable ({c ∈ {c | c ∈ l} | sat a c} ⊆ {c ∈ {c | c ∈ l} | sat b c}) :=
  decidable_of_iff (∀ c ∈ l, sat a c → sat b c)
    ⟨fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩, fun h _ hc ha ↦ (h ⟨hc, ha⟩).2⟩

end Preorder
