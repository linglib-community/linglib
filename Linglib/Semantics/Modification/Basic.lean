module

public import Linglib.Core.Relation.SetRel
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.PropInstances

/-!
# Modifiers

A modifier combines with an expression to give another of the same type ([mcnally-2016]), so a
modifier of `τ` is a function from `τ` to itself. [parsons-1970] construes adjectives and adverbs
as such functions on properties, which makes repeated modification composition. The classes of
[parsons-1970] and [kamp-1975] are order-theoretic: a modifier is subsective, Parsons's standard
and Kamp's affirmative, when each value lies below its argument, privative when value and argument
are disjoint, and intersective, Kamp's predicative, when it is the meet with a fixed element; a
modifier whose values lie above its arguments is extensive. Stacking intersective modifiers
[meets their elements](##Modifier.intersective_inf), and the intersective modifiers are
[those that commute with all of them](##Modifier.isIntersective_iff_forall_commute) and, over a
Boolean algebra, [the subsective ones that distribute over
joins](##Modifier.isIntersective_iff_isSubsective_and_map_sup).
The image of a relation is a modifier of sets that acts on each member separately, as the
modifiers of numerals do, and relations are ordered as their images are. So the image is
[extensive](##Modifier.isExtensive_image_iff) when the relation is reflexive,
[subsective](##Modifier.isSubsective_image_iff) when the relation relates nothing to anything
else, and [privative](##Modifier.isPrivative_image_iff) only when the relation is empty.

## References

* [parsons-1970]
* [kamp-1975]
* [mcnally-2016]
-/

@[expose] public section

/-- A modifier of `τ` is a function from `τ` to `τ`; modifiers stack by composition. -/
abbrev Modifier (τ : Type*) := τ → τ

namespace Modifier

variable {α : Type*}

section LE

variable [LE α] {m : Modifier α}

/-- A modifier `m` is subsective if `m x ≤ x` for every `x`, so that a skillful surgeon is a
surgeon. -/
def IsSubsective (m : Modifier α) : Prop :=
  ∀ x, m x ≤ x

theorem isSubsective_iff_le_id : IsSubsective m ↔ m ≤ id :=
  Iff.rfl

/-- A modifier `m` is extensive if `x ≤ m x` for every `x`, the order dual of subsective, so that
*at least three* holds of three. -/
def IsExtensive (m : Modifier α) : Prop :=
  ∀ x, x ≤ m x

theorem isExtensive_iff_id_le : IsExtensive m ↔ id ≤ m :=
  Iff.rfl

end LE

section Preorder

variable [Preorder α] {m n : Modifier α}

theorem IsSubsective.comp (hm : IsSubsective m) (hn : IsSubsective n) : IsSubsective (m ∘ n) :=
  fun x ↦ (hm (n x)).trans (hn x)

theorem IsExtensive.comp (hm : IsExtensive m) (hn : IsExtensive n) : IsExtensive (m ∘ n) :=
  fun x ↦ (hn x).trans (hm (n x))

end Preorder

section OrderBot

variable [PartialOrder α] [OrderBot α] {m : Modifier α}

/-- A modifier `m` is privative if `m x` is disjoint from `x` for every `x`, so that a fake gun is
not a gun. -/
def IsPrivative (m : Modifier α) : Prop :=
  ∀ x, Disjoint (m x) x

/-- A modifier that is both privative and subsective holds of nothing. -/
theorem IsPrivative.eq_bot (hp : IsPrivative m) (hs : IsSubsective m) (x : α) : m x = ⊥ :=
  le_bot_iff.mp (hp x le_rfl (hs x))

/-- A modifier is both privative and subsective exactly when it holds of nothing. -/
theorem isPrivative_and_isSubsective_iff : IsPrivative m ∧ IsSubsective m ↔ ∀ x, m x = ⊥ :=
  ⟨fun h ↦ h.1.eq_bot h.2, fun h ↦ ⟨fun x ↦ h x ▸ disjoint_bot_left, fun x ↦ h x ▸ bot_le⟩⟩

end OrderBot

/-- Over a Heyting algebra a modifier is privative exactly when it lies below the complement, as
a subsective one lies below the identity. -/
theorem isPrivative_iff_le_compl [HeytingAlgebra α] {m : Modifier α} : IsPrivative m ↔ m ≤ compl :=
  forall_congr' fun _ ↦ le_compl_iff_disjoint_right.symm

/-- A privative modifier maps the top element to the bottom, as nothing is a fake entity. -/
theorem IsPrivative.map_top [PartialOrder α] [BoundedOrder α] {m : Modifier α}
    (hp : IsPrivative m) : m ⊤ = ⊥ :=
  disjoint_top.mp (hp ⊤)

section SemilatticeInf

variable [SemilatticeInf α] {m : Modifier α}

/-- `intersective q` meets its argument with `q`; on predicates it is pointwise conjunction, the
meaning of restrictive relative clauses, intersective adjectives and manner adverbs. -/
def intersective (q : α) : Modifier α := (q ⊓ ·)

@[simp] theorem intersective_apply (q x : α) : intersective q x = q ⊓ x := rfl

/-- Stacking two intersective modifiers is intersective modification by the meet. -/
theorem intersective_inf (q r : α) : intersective (q ⊓ r) = intersective q ∘ intersective r :=
  funext fun _ ↦ inf_assoc ..

@[simp] theorem intersective_top [OrderTop α] : intersective (⊤ : α) = id :=
  funext fun _ ↦ top_inf_eq _

/-- A modifier is intersective if it is the meet with some fixed element. -/
def IsIntersective (m : Modifier α) : Prop :=
  ∃ q, ∀ x, m x = q ⊓ x

theorem intersective_isIntersective (q : α) : IsIntersective (intersective q) :=
  ⟨q, fun _ ↦ rfl⟩

theorem IsIntersective.isSubsective (h : IsIntersective m) : IsSubsective m :=
  fun x ↦ h.elim fun _ hq ↦ (hq x).trans_le inf_le_right

/-- A modifier is subsective exactly when what it yields from the meet of `q` with anything lies
below `q`, so that an intersective modifier under a subsective one still holds. -/
theorem isSubsective_iff_forall_map_inf_le : IsSubsective m ↔ ∀ q x, m (q ⊓ x) ≤ q :=
  ⟨fun h _ _ ↦ (h _).trans inf_le_left, fun h x ↦ by simpa using h x x⟩

section OrderTop

variable [OrderTop α]

/-- An intersective modifier is the meet with its value at `⊤`. -/
theorem isIntersective_iff_forall_eq_map_top_inf : IsIntersective m ↔ ∀ x, m x = m ⊤ ⊓ x :=
  ⟨fun ⟨q, hq⟩ x ↦ by rw [hq ⊤, inf_top_eq, hq], fun h ↦ ⟨m ⊤, h⟩⟩

/-- A modifier is intersective exactly when meeting its argument with `q` meets its value with
`q`. -/
theorem isIntersective_iff_map_inf : IsIntersective m ↔ ∀ x q, m (x ⊓ q) = m x ⊓ q :=
  ⟨fun ⟨r, hr⟩ x q ↦ by simp only [hr, inf_assoc],
    fun h ↦ isIntersective_iff_forall_eq_map_top_inf.2 fun x ↦ by simpa using h ⊤ x⟩

/-- A modifier is intersective exactly when it commutes with every intersective modifier, so that
the order of an intersective modifier and another one matters only when the other is not
intersective. -/
theorem isIntersective_iff_forall_commute :
    IsIntersective m ↔ ∀ q, Function.Commute m (intersective q) := by
  rw [isIntersective_iff_map_inf]
  refine ⟨fun h q x ↦ ?_, fun h x q ↦ ?_⟩
  · rw [intersective_apply, intersective_apply, inf_comm q x, h, inf_comm]
  · rw [inf_comm x q, inf_comm (m x) q]
    exact h q x

end OrderTop

end SemilatticeInf

/-- Over a Boolean algebra a modifier is intersective exactly when it is subsective and
distributes over joins, so that a gray cat or dog is a gray cat or a gray dog. -/
theorem isIntersective_iff_isSubsective_and_map_sup [BooleanAlgebra α] {m : Modifier α} :
    IsIntersective m ↔ IsSubsective m ∧ ∀ x y, m (x ⊔ y) = m x ⊔ m y := by
  refine ⟨fun h ↦ ⟨h.isSubsective, fun x y ↦ ?_⟩,
    fun ⟨hs, hm⟩ ↦ isIntersective_iff_forall_eq_map_top_inf.2 fun x ↦ ?_⟩
  · obtain ⟨q, hq⟩ := h
    simp only [hq, inf_sup_left]
  · rw [← sup_compl_eq_top (x := x), hm, inf_sup_right, inf_eq_left.2 (hs x),
      (disjoint_compl_left.mono_left (hs xᶜ)).eq_bot, sup_bot_eq]

/-! ### Images of relations -/

section Image

variable {R : SetRel α α}

/-- The image of a relation is extensive exactly when the relation is reflexive. -/
theorem isExtensive_image_iff : IsExtensive R.image ↔ R.IsRefl := by
  rw [← SetRel.id_subset_iff, ← SetRel.image_le_image_iff, SetRel.image_id_eq]
  rfl

/-- The image of a relation is subsective exactly when the relation relates nothing to anything
else. -/
theorem isSubsective_image_iff : IsSubsective R.image ↔ R ⊆ .id := by
  rw [← SetRel.image_le_image_iff, SetRel.image_id_eq]
  rfl

/-- The image of a relation is privative only when the relation is empty, since a set `{a, b}`
with `a` related to `b` meets its own image. -/
theorem isPrivative_image_iff : IsPrivative R.image ↔ R = ∅ := by
  refine ⟨fun h ↦ Set.eq_empty_iff_forall_notMem.2 fun ⟨a, b⟩ hab ↦ ?_, fun h s ↦ by simp [h]⟩
  exact Set.disjoint_left.1 (h {a, b}) ⟨a, by simp, hab⟩ (by simp)

end Image

end Modifier
