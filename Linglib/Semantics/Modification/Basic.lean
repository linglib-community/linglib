module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.PropInstances

/-!
# Modifiers

A modifier of `τ` is a function from `τ` to itself, as Parsons treats adjectives and adverbs as
functions on the predicates they modify; adjectives, adverbs and relative clauses are modifiers
of different types `τ`, and modifiers stack by composition. Kamp's classification of adjective
meanings is order-theoretic: over an ordered type, a modifier is subsective when it maps each
argument below itself, privative when its value is disjoint from its argument, and intersective
when it is the meet with a fixed element. Its order dual, a modifier mapping each argument above
itself, is extensive.

A modifier of sets can act pointwise, sending a set to the union of the values of a map on its
members, which is `SetRel.image`. The modifiers of numerals and of scalar alternatives are of this
kind, and Kamp's classes then read off the map: extensive when every point is in its own value,
subsective when no value leaves its point, and privative only for the empty map, while being
disjoint from every singleton argument is irreflexivity.

`Semantics/Modification/Classification.lean` specializes the classes to intensional properties.

## Main definitions

* `Modifier τ`: the functions from `τ` to `τ`.
* `Modifier.intersective q`: the meet with `q`.
* `Modifier.IsSubsective`, `IsPrivative`, `IsIntersective`: Kamp's classes, and
  `Modifier.IsExtensive`, the dual of subsective.
* `Modifier.pointwise r`: the modifier of sets acting pointwise through `r`.

## Main results

* `Modifier.isExtensive_pointwise_iff`, `isSubsective_pointwise_iff`: the classes of a
  pointwise modifier, read off its map.
* `Modifier.isPrivative_pointwise_iff`: a pointwise modifier is privative only when its
  map is empty everywhere.

## References

* [parsons-1970]
* [kamp-1975]
-/

@[expose] public section

/-- A modifier of `τ` is a function from `τ` to `τ`; modifiers stack by composition. -/
abbrev Modifier (τ : Type*) := τ → τ

namespace Modifier

variable {α : Type*}

/-- A modifier `m` is subsective if `m x ≤ x` for every `x`, so that a skillful surgeon is a
surgeon. -/
def IsSubsective [LE α] (m : Modifier α) : Prop :=
  ∀ x, m x ≤ x

theorem isSubsective_iff_le_id [LE α] {m : Modifier α} :
    IsSubsective m ↔ m ≤ id :=
  Iff.rfl

/-- A modifier `m` is privative if `m x` is disjoint from `x` for every `x`, so that a fake gun is
not a gun. -/
def IsPrivative [PartialOrder α] [OrderBot α] (m : Modifier α) : Prop :=
  ∀ x, Disjoint (m x) x

theorem IsPrivative.eq_bot [PartialOrder α] [OrderBot α] {m : Modifier α}
    (hp : IsPrivative m) (hs : IsSubsective m) (x : α) : m x = ⊥ :=
  le_bot_iff.mp (hp x le_rfl (hs x))

section SemilatticeInf

variable [SemilatticeInf α]

/-- A modifier is intersective if it is the meet with some fixed element. -/
def IsIntersective (m : Modifier α) : Prop :=
  ∃ q, ∀ x, m x = q ⊓ x

theorem IsIntersective.isSubsective {m : Modifier α} (h : IsIntersective m) :
    IsSubsective m :=
  fun x ↦ h.elim fun _ hq ↦ (hq x).trans_le inf_le_right

/-- `intersective q` meets its argument with `q`; on predicates it is pointwise conjunction, the
meaning of restrictive relative clauses, intersective adjectives and manner adverbs. -/
def intersective (q : α) : Modifier α := (q ⊓ ·)

@[simp] theorem intersective_apply {β : Type*} (P Q : β → Prop) (x : β) :
    intersective P Q x = (P x ∧ Q x) := rfl

theorem intersective_comm (q r : α) : intersective q r = intersective r q :=
  inf_comm q r

theorem intersective_isIntersective (q : α) : IsIntersective (intersective q) :=
  ⟨q, fun _ ↦ rfl⟩

end SemilatticeInf

/-- A modifier `m` is extensive if `x ≤ m x` for every `x`, the order dual of subsective, so that
*at least three* holds of three. -/
def IsExtensive [LE α] (m : Modifier α) : Prop :=
  ∀ x, x ≤ m x

theorem isExtensive_iff_id_le [LE α] {m : Modifier α} : IsExtensive m ↔ id ≤ m :=
  Iff.rfl

theorem IsSubsective.comp [Preorder α] {m n : Modifier α} (hm : IsSubsective m)
    (hn : IsSubsective n) : IsSubsective (m ∘ n) :=
  fun x ↦ (hm (n x)).trans (hn x)

theorem IsExtensive.comp [Preorder α] {m n : Modifier α} (hm : IsExtensive m)
    (hn : IsExtensive n) : IsExtensive (m ∘ n) :=
  fun x ↦ (hn x).trans (hm (n x))

/-! ### Pointwise modifiers of sets -/

section Pointwise

variable {β : Type*}

/-- `pointwise r` sends a set to the union of the values of `r` on its members. -/
def pointwise (r : α → Set β) : Set α → Set β := fun s ↦ ⋃ a ∈ s, r a

variable {r : α → Set β} {s : Set α} {b : β}

@[simp] theorem mem_pointwise : b ∈ pointwise r s ↔ ∃ a ∈ s, b ∈ r a := by
  simp [pointwise]

@[simp] theorem pointwise_singleton (r : α → Set β) (a : α) : pointwise r {a} = r a :=
  Set.biUnion_singleton a r

theorem pointwise_eq_image (r : α → Set β) (s : Set α) :
    pointwise r s = SetRel.image {p | p.2 ∈ r p.1} s := by
  ext b; simp [SetRel.image]

theorem pointwise_singleton_eq_id : pointwise (fun a : α ↦ ({a} : Set α)) = id :=
  funext Set.biUnion_of_singleton

variable {r : α → Set α}

theorem isExtensive_pointwise_iff : IsExtensive (pointwise r) ↔ ∀ a, a ∈ r a :=
  ⟨fun h a ↦ by simpa using h {a}, fun h _ a ha ↦ mem_pointwise.2 ⟨a, ha, h a⟩⟩

theorem isSubsective_pointwise_iff : IsSubsective (pointwise r) ↔ ∀ a, r a ⊆ {a} := by
  refine ⟨fun h a ↦ by simpa using h {a}, fun h s b hb ↦ ?_⟩
  obtain ⟨a, ha, hba⟩ := mem_pointwise.1 hb
  exact (h a hba).symm ▸ ha

/-- A pointwise modifier is privative only when its map is empty everywhere, since an argument
`{a, b}` with `b ∈ r a` meets its own value. -/
theorem isPrivative_pointwise_iff : IsPrivative (pointwise r) ↔ ∀ a, r a = ∅ := by
  refine ⟨fun h a ↦ Set.eq_empty_iff_forall_notMem.2 fun b hb ↦ ?_, fun h s ↦ ?_⟩
  · exact Set.disjoint_left.1 (h {a, b}) (mem_pointwise.2 ⟨a, by simp, hb⟩) (by simp)
  · refine Set.disjoint_left.2 fun b hb _ ↦ ?_
    obtain ⟨a, _, hba⟩ := mem_pointwise.1 hb
    simp [h a] at hba

theorem disjoint_pointwise_singleton_iff :
    (∀ a, Disjoint (pointwise r {a}) {a}) ↔ ∀ a, a ∉ r a := by
  simp [Set.disjoint_singleton_right]

end Pointwise

end Modifier
