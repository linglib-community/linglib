module

public import Linglib.Semantics.Modification.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Closure

/-!
# Degree comparison

A `Comparison` is one of the five ways a measured value can relate to a threshold, `=`, `≥`, `>`,
`≤` and `<`, kept as data so that numerals, measure phrases and comparatives can share it. It
selects an order interval, and the entities a measure `μ` sends into that interval form the preimage
`μ ⁻¹' c.interval n`. A comparison is strict when [its threshold lies outside the
interval](##Comparison.self_mem_interval_iff), and as a modifier of degree sets it is [extensive
exactly when not strict](##Comparison.isExtensive_modifier_iff). [Reversing the scale exchanges its
two sides](##Comparison.rel_dual), and an order embedding [preserves it when the threshold moves
along](##Comparison.preimage_interval). Maximality on a scale is the
[greatest](##Comparison.mem_maxOnScale_gt) or [least](##Comparison.mem_maxOnScale_lt) member of a
set, the two [exchanged by reversing the scale](##Comparison.mem_maxOnScale_dual).

## Implementation notes

Strictness belongs to the comparison and not to its interval: over the integers *fewer than 11*
and *at most 10* select the same numbers. `maxOnScale` returns a member of its set, so on a dense
scale an open interval has no maximum at its open end; mathlib's `IsLUB` and `IsGLB` are the
versions that do not require membership.

## References

* [kennedy-2015]
* [kennedy-2007]
* [nouwen-2010]
* [geurts-nouwen-2007]
* [rett-2015a]
* [rett-2020a]
* [rett-2026]
-/

@[expose] public section

/-- A comparison is the ordering relation a degree modifier draws between a measured value and a
threshold. The bare and modified numerals of [kennedy-2015] differ only in this relation (73), as
the comparative and equative of [rett-2015a] (33) do. -/
inductive Comparison where
  /-- The relation `μ x = n` of a bare numeral (73a). -/
  | eq
  /-- The relation `μ x ≥ n` of *at least `n`* (42a). -/
  | ge
  /-- The relation `μ x > n` of *more than `n`* (41a). -/
  | gt
  /-- The relation `μ x ≤ n` of *at most `n`* (42b). -/
  | le
  /-- The relation `μ x < n` of *fewer than `n`* (41b). -/
  | lt
  deriving DecidableEq, Repr, Inhabited

namespace Comparison

variable {α β : Type*}

/-- A comparison is strict when it excludes its threshold, as `>` and `<` do. [kennedy-2015] (4)
and [rett-2015a] take strictness to separate the Class A modifiers of [nouwen-2010] from Class B,
Rett setting the superlatives aside. [nouwen-2010] and [geurts-nouwen-2007] reject this reading of
the modifiers as the naive view, the latter giving *at least* and *at most* a modal meaning. -/
def IsStrict : Comparison → Prop
  | .gt | .lt => True
  | _         => False

instance : DecidablePred IsStrict
  | .gt | .lt => .isTrue trivial
  | .eq | .ge | .le => .isFalse not_false

section Preorder

variable [Preorder α]

/-- The order relation a `Comparison` stands for. -/
def Rel : Comparison → α → α → Prop
  | .eq => (· = ·) | .ge => (· ≥ ·) | .gt => (· > ·)
  | .le => (· ≤ ·) | .lt => (· < ·)

/-- The order interval a comparison selects is `{n}`, `[n, ∞)`, `(n, ∞)`, `(-∞, n]` or `(-∞, n)`. -/
def interval (c : Comparison) (n : α) : Set α := {a | c.Rel a n}

variable (c : Comparison) (a n : α)

@[simp] theorem interval_eq : Comparison.eq.interval n = {n} := rfl
@[simp] theorem interval_ge : Comparison.ge.interval n = Set.Ici n := rfl
@[simp] theorem interval_gt : Comparison.gt.interval n = Set.Ioi n := rfl
@[simp] theorem interval_le : Comparison.le.interval n = Set.Iic n := rfl
@[simp] theorem interval_lt : Comparison.lt.interval n = Set.Iio n := rfl

@[simp] theorem rel_eq : Comparison.eq.Rel a n ↔ a = n := Iff.rfl
@[simp] theorem rel_ge : Comparison.ge.Rel a n ↔ n ≤ a := Iff.rfl
@[simp] theorem rel_gt : Comparison.gt.Rel a n ↔ n < a := Iff.rfl
@[simp] theorem rel_le : Comparison.le.Rel a n ↔ a ≤ n := Iff.rfl
@[simp] theorem rel_lt : Comparison.lt.Rel a n ↔ a < n := Iff.rfl

@[simp] theorem mem_interval : a ∈ c.interval n ↔ c.Rel a n := Iff.rfl

instance decidableRel [DecidableEq α] [DecidableLE α] [DecidableLT α] :
    Decidable (c.Rel a n) :=
  match c with
  | .eq => inferInstanceAs (Decidable (a = n))
  | .ge => inferInstanceAs (Decidable (n ≤ a))
  | .gt => inferInstanceAs (Decidable (n < a))
  | .le => inferInstanceAs (Decidable (a ≤ n))
  | .lt => inferInstanceAs (Decidable (a < n))

instance decidableMemInterval [DecidableEq α] [DecidableLE α] [DecidableLT α] :
    Decidable (a ∈ c.interval n) :=
  decidableRel c a n

/-- A comparison keeps its threshold exactly when it is not strict, the inclusive and exclusive
orderings of [kennedy-2015] (4). -/
@[simp] theorem self_mem_interval_iff : n ∈ c.interval n ↔ ¬ c.IsStrict := by
  cases c <;> simp [IsStrict]

/-! ### Comparisons as modifiers

A comparison is a modifier of degree sets acting pointwise through its interval, so the modified
numeral is the modifier applied to the bare numeral's two-sided meaning: *at least* is the upward
closure, *at most* the downward closure and *exactly* the identity. The two halves of
[kennedy-2015] (4) are then properties of the modifier, extensive when the comparison is inclusive
and disjoint from each singleton when it is strict. -/

/-- The modifier of degree sets that a comparison is, pointwise through its interval. -/
def modifier (c : Comparison) : Modifier (Set α) := Modifier.pointwise c.interval

@[simp] theorem modifier_singleton (c : Comparison) (n : α) : c.modifier {n} = c.interval n :=
  Modifier.pointwise_singleton _ n

theorem modifier_ge (s : Set α) : Comparison.ge.modifier s = upperClosure s :=
  (coe_upperClosure s).symm

theorem modifier_le (s : Set α) : Comparison.le.modifier s = lowerClosure s :=
  (coe_lowerClosure s).symm

theorem modifier_eq : (Comparison.eq.modifier : Modifier (Set α)) = id :=
  Modifier.pointwise_singleton_eq_id

theorem isExtensive_modifier_iff [Nonempty α] (c : Comparison) :
    Modifier.IsExtensive (c.modifier : Modifier (Set α)) ↔ ¬ c.IsStrict := by
  rw [modifier, Modifier.isExtensive_pointwise_iff]
  exact ⟨fun h ↦ (c.self_mem_interval_iff (Classical.arbitrary α)).1 (h _),
    fun h n ↦ (c.self_mem_interval_iff n).2 h⟩

theorem disjoint_modifier_singleton_iff [Nonempty α] (c : Comparison) :
    (∀ n : α, Disjoint (c.modifier {n}) {n}) ↔ c.IsStrict := by
  rw [modifier, Modifier.disjoint_pointwise_singleton_iff]
  exact ⟨fun h ↦ by_contra fun hs ↦ h (Classical.arbitrary α) ((c.self_mem_interval_iff _).2 hs),
    fun h n hn ↦ (c.self_mem_interval_iff n).1 hn h⟩

end Preorder

/-- The interval of a comparison is convex. -/
instance ordConnected_interval [PartialOrder α] (c : Comparison) (n : α) :
    (c.interval n).OrdConnected := by
  cases c <;> simp only [interval_eq, interval_ge, interval_gt, interval_le, interval_lt] <;>
    infer_instance

/-! ### The antonymous comparison

Polar antonyms measure the same degrees under inverse orderings, an observation [kennedy-2007]
traces to Sapir. Its note 29 leaves open whether degrees are points, as they are here, or
intervals. -/

/-- The dual of a comparison reads it on the reversed scale, turning `>` into `<` and `≥` into `≤`
and fixing `=`. -/
def dual : Comparison → Comparison
  | .eq => .eq
  | .ge => .le
  | .gt => .lt
  | .le => .ge
  | .lt => .gt

@[simp] theorem dual_eq : Comparison.eq.dual = .eq := rfl
@[simp] theorem dual_ge : Comparison.ge.dual = .le := rfl
@[simp] theorem dual_gt : Comparison.gt.dual = .lt := rfl
@[simp] theorem dual_le : Comparison.le.dual = .ge := rfl
@[simp] theorem dual_lt : Comparison.lt.dual = .gt := rfl

theorem dual_involutive : Function.Involutive dual := fun c ↦ by cases c <;> rfl

@[simp] theorem dual_dual (c : Comparison) : c.dual.dual = c := dual_involutive c

section Dual

variable [Preorder α] (c : Comparison)

/-- The dual comparison exchanges its arguments, so *a is taller than b* exactly when *b is shorter
than a*, [kennedy-2007] (60). -/
theorem rel_dual (a b : α) : c.dual.Rel a b ↔ c.Rel b a := by
  cases c <;> simp only [dual, Rel, eq_comm]

/-- The interval of the dual comparison is the interval of the comparison on the dual scale. -/
theorem interval_dual (n : α) :
    c.dual.interval n = OrderDual.toDual ⁻¹' c.interval (OrderDual.toDual n) := by
  cases c <;> rfl

end Dual

/-! ### Change of scale -/

section Comp

variable [Preorder α] [Preorder β]

theorem rel_map_iff (f : α ↪o β) (c : Comparison) {a n : α} :
    c.Rel (f a) (f n) ↔ c.Rel a n := by
  cases c <;> simp [Rel, f.lt_iff_lt, f.le_iff_le, f.injective.eq_iff]

/-- An order embedding of the scale pulls the interval at `f n` back to the interval at `n`, so a
comparison is invariant when its threshold moves along with the measure. -/
theorem preimage_interval (f : α ↪o β) (c : Comparison) (n : α) :
    f ⁻¹' c.interval (f n) = c.interval n :=
  Set.ext fun _ ↦ rel_map_iff f c

end Comp

section CompLinear

variable [LinearOrder α]

theorem interval_injective (c : Comparison) : Function.Injective (c.interval : α → Set α) := by
  cases c
  exacts [Set.singleton_injective, Set.Ici_injective, Set.Ioi_injective, Set.Iic_injective,
    Set.Iio_injective]

theorem preimage_interval_eq_iff (g : α ≃o α) (c : Comparison) (n : α) :
    g ⁻¹' c.interval n = c.interval n ↔ Function.IsFixedPt g n := by
  have h : g ⁻¹' c.interval n = c.interval (g.symm n) := by
    simpa using preimage_interval g.toOrderEmbedding c (g.symm n)
  rw [h, c.interval_injective.eq_iff, g.symm_apply_eq, eq_comm]
  rfl

theorem forall_preimage_interval_eq_iff (g : α ≃o α) (c : Comparison) :
    (∀ n, g ⁻¹' c.interval n = c.interval n) ↔ g = OrderIso.refl α := by
  simp only [preimage_interval_eq_iff, Function.IsFixedPt]
  refine ⟨fun h ↦ OrderIso.ext (funext h), ?_⟩
  rintro rfl n
  rfl

end CompLinear

/-! ### Scale-sensitive maximality

What counts as maximal depends on the ordering of the scale, so the same operator picks the latest
time of a clause under *after* and the earliest under *before*. -/

section Maximality

variable [Preorder α] {X : Set α} {x : α}

/-- Scale-sensitive maximality, [rett-2015a] (32), [rett-2020a] (17) and [rett-2026] (44), picks
the members of `X` that stand in `c` to every other member. The papers let the relation range over
`>` and `<`. -/
def maxOnScale (c : Comparison) (X : Set α) : Set α :=
  {x | x ∈ X ∧ ∀ x' ∈ X, x' ≠ x → c.Rel x x'}

/-- Maximality on the dual comparison is maximality on the reversed scale, "the same relation
involved in each, just applied to reverse scales" ([rett-2026] n. 13). -/
theorem mem_maxOnScale_dual (c : Comparison) :
    x ∈ maxOnScale c.dual X ↔ OrderDual.toDual x ∈ maxOnScale c (OrderDual.ofDual ⁻¹' X) := by
  cases c <;> exact Iff.rfl

end Maximality

section MaximalityPartial

variable [PartialOrder α] {X : Set α} {x : α}

theorem mem_maxOnScale_gt : x ∈ maxOnScale .gt X ↔ IsGreatest X x :=
  and_congr_right fun _ ↦ forall₂_congr fun y _ ↦ by
    rw [Comparison.rel_gt, le_iff_lt_or_eq, or_comm, or_iff_not_imp_left]

theorem mem_maxOnScale_lt : x ∈ maxOnScale .lt X ↔ IsLeast X x :=
  (mem_maxOnScale_dual (X := X) .gt).trans mem_maxOnScale_gt

end MaximalityPartial

end Comparison
