module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Core.Order.StrictBounds
public import Linglib.Semantics.Modification.Basic
public import Mathlib.Order.UpperLower.Closure

/-!
# Reified degree comparison

A `Comparison` is one of the five ways a measured value can relate to a threshold, `=`, `≥`, `>`,
`≤` and `<`, kept as data so that numeral modifiers, measure phrases and comparatives can share
it, as in the joint treatment of Kennedy and Rett. A comparison selects an order interval, and the
entities a measure `μ` sends into it form the preimage `μ ⁻¹' c.interval n`; `Comparison.bounds`
generalizes the threshold to a set of degrees, the clausal standard of Hoeksema's comparative.
The point-standard comparative *a is taller than b* is `a ∈ μ ⁻¹' Set.Ioi (μ b)`, that is
`μ b < μ a`, and the equative is `Comparison.ge`.

The antonym of a comparison is its order dual, `Comparison.dual`: *a is shorter than b* is the
dual comparison, which holds exactly when *b is taller than a* does and is the same comparison
read on the reversed scale, Kennedy's account of antonymy. Comparisons are invariant under a
strictly monotone change of scale. As a modifier of degree sets acting pointwise, a comparison
sends the bare numeral's meaning to the modified numeral's, and its Kamp class is the Class A/B
split.

## Main definitions

* `Degree.Comparison`, with `Comparison.Rel` and `Comparison.interval`.
* `Degree.Comparison.bounds`: the set-standard interval.
* `Degree.Comparison.dual`: the antonymous comparison.
* `Degree.Comparison.modifier`: the comparison as a modifier of degree sets.
* `Degree.maxOnScale`: Rett's order-sensitive maximality.
* `Degree.ThresholdSignificant`: some member of the comparison class clears the threshold, the
  presupposition Uegaki and Sudo attribute to degree constructions.

## Main results

* `Degree.Comparison.bounds_singleton`: a singleton standard is a point standard.
* `Degree.Comparison.rel_dual`, `Degree.Comparison.interval_dual`: antonymy as argument exchange
  and as scale reversal.
* `Degree.Comparison.preimage_interval`: invariance under an order embedding of the scale.
* `Degree.Comparison.boundary_mem`: the Class A/B distinction as endpoint membership.
* `Degree.Comparison.modifier_ge`, `Degree.Comparison.isExtensive_modifier_iff`: *at least* is
  upward closure, and a comparison's modifier is extensive exactly when the comparison is not
  strict.

## References

* [kennedy-2015]
* [rett-2014]
* [hoeksema-1983]
* [kennedy-2007]
* [geurts-nouwen-2007]
* [nouwen-2010]
* [rett-2026]
* [uegaki-sudo-2019]
-/

@[expose] public section

namespace Degree

/-- A comparison is the relation a degree modifier draws between a measured value and a threshold,
[kennedy-2015]'s `REL` reified. -/
inductive Comparison where
  /-- The exact comparison `μ x = n` of a bare numeral. -/
  | eq
  /-- The comparison `μ x ≥ n` of *at least `n`*. -/
  | ge
  /-- The comparison `μ x > n` of *more than `n`*. -/
  | gt
  /-- The comparison `μ x ≤ n` of *at most `n`*. -/
  | le
  /-- The comparison `μ x < n` of *fewer than `n`*. -/
  | lt
  deriving DecidableEq, Repr, Inhabited

/-- A comparison is strict when it excludes its threshold, as `>` and `<` do; the Class A/B split of
modified numerals ([geurts-nouwen-2007], [nouwen-2010]) is strictness restricted to the four
modified forms. -/
def Comparison.IsStrict : Comparison → Prop
  | .gt | .lt => True
  | _         => False

instance : DecidablePred Comparison.IsStrict := fun c => by
  cases c <;> unfold Comparison.IsStrict <;> infer_instance

/-- The order relation a `Comparison` stands for. -/
def Comparison.Rel {α : Type*} [Preorder α] : Comparison → α → α → Prop
  | .eq => (· = ·) | .ge => (· ≥ ·) | .gt => (· > ·)
  | .le => (· ≤ ·) | .lt => (· < ·)

/-- The order interval a comparison selects is `{n}`, `[n, ∞)`, `(n, ∞)`, `(-∞, n]` or `(-∞, n)`. -/
def Comparison.interval {α : Type*} [Preorder α] : Comparison → α → Set α
  | .eq => fun n => {n}
  | .ge => Set.Ici
  | .gt => Set.Ioi
  | .le => Set.Iic
  | .lt => Set.Iio

section

variable {α : Type*} [Preorder α] (a n : α)

@[simp] theorem Comparison.interval_eq : Comparison.eq.interval n = {n} := rfl
@[simp] theorem Comparison.interval_ge : Comparison.ge.interval n = Set.Ici n := rfl
@[simp] theorem Comparison.interval_gt : Comparison.gt.interval n = Set.Ioi n := rfl
@[simp] theorem Comparison.interval_le : Comparison.le.interval n = Set.Iic n := rfl
@[simp] theorem Comparison.interval_lt : Comparison.lt.interval n = Set.Iio n := rfl

@[simp] theorem Comparison.rel_eq : Comparison.eq.Rel a n ↔ a = n := Iff.rfl
@[simp] theorem Comparison.rel_ge : Comparison.ge.Rel a n ↔ n ≤ a := Iff.rfl
@[simp] theorem Comparison.rel_gt : Comparison.gt.Rel a n ↔ n < a := Iff.rfl
@[simp] theorem Comparison.rel_le : Comparison.le.Rel a n ↔ a ≤ n := Iff.rfl
@[simp] theorem Comparison.rel_lt : Comparison.lt.Rel a n ↔ a < n := Iff.rfl

end

@[simp] theorem Comparison.mem_interval {α : Type*} [Preorder α]
    (c : Comparison) (a n : α) : a ∈ c.interval n ↔ c.Rel a n := by
  cases c <;> simp [Comparison.interval, Comparison.Rel]

/-- The interval of a comparison is convex. -/
instance Comparison.ordConnected_interval {α : Type*} [PartialOrder α] (c : Comparison) (n : α) :
    (c.interval n).OrdConnected := by
  cases c <;> simp only [interval_eq, interval_ge, interval_gt, interval_le, interval_lt] <;>
    infer_instance

instance Comparison.relDecidable {α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (a n : α) : Decidable (c.Rel a n) := by
  cases c <;> simp only [Comparison.Rel, ge_iff_le, gt_iff_lt] <;> infer_instance

instance Comparison.intervalDecidable {α : Type*} [Preorder α] [DecidableEq α] [DecidableLE α]
    [DecidableLT α] (c : Comparison) (a n : α) : Decidable (a ∈ c.interval n) :=
  decidable_of_iff _ (Comparison.mem_interval c a n).symm

@[simp] theorem Comparison.boundary_mem {α : Type*} [Preorder α]
    (c : Comparison) (n : α) : n ∈ c.interval n ↔ ¬ c.IsStrict := by
  cases c <;> simp [Comparison.interval, Comparison.IsStrict]

/-! ### Comparisons as modifiers

A comparison is a modifier of degree sets acting pointwise through its interval, so the modified
numeral is the modifier applied to the bare numeral's two-sided meaning: *at least* is the upward
closure, *at most* the downward closure and *exactly* the identity. Its Kamp class is the
Class A/B split, extensive when the comparison is inclusive and disjoint from each singleton when
it is strict. -/

section Modifier

variable {α : Type*} [Preorder α]

/-- The modifier of degree sets that a comparison is, pointwise through its interval. -/
def Comparison.modifier (c : Comparison) : Modifier (Set α) := Modifier.pointwise c.interval

@[simp] theorem Comparison.modifier_singleton (c : Comparison) (n : α) :
    c.modifier {n} = c.interval n :=
  Modifier.pointwise_singleton _ n

theorem Comparison.modifier_ge (s : Set α) : Comparison.ge.modifier s = upperClosure s :=
  (coe_upperClosure s).symm

theorem Comparison.modifier_le (s : Set α) : Comparison.le.modifier s = lowerClosure s :=
  (coe_lowerClosure s).symm

theorem Comparison.modifier_eq : (Comparison.eq.modifier : Modifier (Set α)) = id :=
  Modifier.pointwise_singleton_eq_id

theorem Comparison.isExtensive_modifier_iff [Nonempty α] (c : Comparison) :
    Modifier.IsExtensive (c.modifier : Modifier (Set α)) ↔ ¬ c.IsStrict := by
  rw [Comparison.modifier, Modifier.isExtensive_pointwise_iff]
  exact ⟨fun h ↦ (c.boundary_mem (Classical.arbitrary α)).1 (h _),
    fun h n ↦ (c.boundary_mem n).2 h⟩

theorem Comparison.disjoint_modifier_singleton_iff [Nonempty α] (c : Comparison) :
    (∀ n : α, Disjoint (c.modifier {n}) {n}) ↔ c.IsStrict := by
  rw [Comparison.modifier, Modifier.disjoint_pointwise_singleton_iff]
  exact ⟨fun h ↦ by_contra fun hs ↦ h (Classical.arbitrary α) ((c.boundary_mem _).2 hs),
    fun h n hn ↦ (c.boundary_mem n).1 hn h⟩

end Modifier

/-! ### Threshold significance

A degree construction whose threshold `θ C` depends on a comparison class `C` presupposes that
some member of the class exceeds the threshold; otherwise the construction draws no distinction
in the class. -/

/-- A threshold function `θ` is significant on the comparison class `C` when some member of `C`
measures above `θ C`. -/
def ThresholdSignificant {E α : Type*} [Preorder α] (μ : E → α) (θ : Set E → α)
    (C : Set E) : Prop :=
  (C ∩ μ ⁻¹' Set.Ioi (θ C)).Nonempty

theorem thresholdSignificant_iff {E α : Type*} [Preorder α] {μ : E → α} {θ : Set E → α}
    {C : Set E} : ThresholdSignificant μ θ C ↔ ∃ y ∈ C, θ C < μ y :=
  ⟨fun ⟨y, hy, h⟩ ↦ ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ ↦ ⟨y, hy, h⟩⟩

/-! ### Set-standard comparison

The than-clause of a comparative supplies not a point but a *set* of degrees.
`Comparison.bounds` lifts `Comparison.interval` from a point `n` to a standard set
`Δ`, the upper or lower bounds, strict or not, matching the comparison's relation. The entities
whose measure bounds `Δ` are the preimage `μ ⁻¹' c.bounds Δ`, the order-theoretic core of
Hoeksema's clausal comparative, and a singleton standard is a point standard
(`bounds_singleton`). -/

/-- The bounds a comparison imposes on a standard set `Δ` are its upper, strict upper, lower or
strict lower bounds, generalizing `Comparison.interval` from a point to a set. -/
def Comparison.bounds {α : Type*} [Preorder α] : Comparison → Set α → Set α
  | .eq => fun Δ => {x | ∀ a ∈ Δ, x = a}
  | .ge => upperBounds
  | .gt => strictUpperBounds
  | .le => lowerBounds
  | .lt => strictLowerBounds

theorem Comparison.bounds_singleton {α : Type*} [Preorder α] (c : Comparison) (n : α) :
    c.bounds {n} = c.interval n := by
  cases c
  case eq =>
    ext x; simp only [Comparison.bounds, Comparison.interval, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, forall_eq]
  case ge => simp only [Comparison.bounds, Comparison.interval]; exact upperBounds_singleton
  case gt => simp only [Comparison.bounds, Comparison.interval, strictUpperBounds_singleton]
  case le => simp only [Comparison.bounds, Comparison.interval]; exact lowerBounds_singleton
  case lt => simp only [Comparison.bounds, Comparison.interval, strictLowerBounds_singleton]

/-! ### The antonymous comparison -/

/-- The dual of a comparison reads it on the reversed scale, turning `>` into `<` and `≥` into `≤`
and fixing `=`. -/
def Comparison.dual : Comparison → Comparison
  | .eq => .eq
  | .ge => .le
  | .gt => .lt
  | .le => .ge
  | .lt => .gt

@[simp] theorem Comparison.dual_eq : Comparison.eq.dual = .eq := rfl
@[simp] theorem Comparison.dual_ge : Comparison.ge.dual = .le := rfl
@[simp] theorem Comparison.dual_gt : Comparison.gt.dual = .lt := rfl
@[simp] theorem Comparison.dual_le : Comparison.le.dual = .ge := rfl
@[simp] theorem Comparison.dual_lt : Comparison.lt.dual = .gt := rfl

theorem Comparison.dual_involutive : Function.Involutive Comparison.dual := fun c ↦ by
  cases c <;> rfl

@[simp] theorem Comparison.dual_dual (c : Comparison) : c.dual.dual = c :=
  Comparison.dual_involutive c

@[simp] theorem Comparison.isStrict_dual (c : Comparison) : c.dual.IsStrict ↔ c.IsStrict := by
  cases c <;> exact Iff.rfl

section Dual

variable {α : Type*} [Preorder α] (c : Comparison)

theorem Comparison.rel_dual (a b : α) : c.dual.Rel a b ↔ c.Rel b a := by
  cases c <;> simp only [Comparison.dual, Comparison.Rel, eq_comm]

theorem Comparison.rel_dual_toDual (a b : α) :
    c.dual.Rel a b ↔ c.Rel (OrderDual.toDual a) (OrderDual.toDual b) := by
  cases c <;> exact Iff.rfl

theorem Comparison.interval_dual (n : α) :
    c.dual.interval n = OrderDual.toDual ⁻¹' c.interval (OrderDual.toDual n) := by
  cases c <;> rfl

theorem Comparison.bounds_dual (Δ : Set α) :
    c.dual.bounds Δ = OrderDual.toDual ⁻¹' c.bounds (OrderDual.toDual '' Δ) := by
  cases c <;> ext x <;>
    simp [Comparison.bounds, upperBounds, lowerBounds, strictUpperBounds, strictLowerBounds]

end Dual

/-! ### Change of scale -/

section Comp

variable {α β : Type*} [Preorder α] [Preorder β]

theorem Comparison.rel_map_iff (f : α ↪o β) (c : Comparison) {a n : α} :
    c.Rel (f a) (f n) ↔ c.Rel a n := by
  cases c <;> simp [Comparison.Rel, f.lt_iff_lt, f.le_iff_le, f.injective.eq_iff]

theorem Comparison.preimage_interval (f : α ↪o β) (c : Comparison) (n : α) :
    f ⁻¹' c.interval (f n) = c.interval n := by
  ext a
  simp only [Set.mem_preimage, Comparison.mem_interval, Comparison.rel_map_iff]

theorem Comparison.preimage_interval_of_isFixedPt (g : α ≃o α) (c : Comparison) {n : α}
    (hn : Function.IsFixedPt g n) : g ⁻¹' c.interval n = c.interval n := by
  conv_lhs => rw [← hn.eq]
  exact Comparison.preimage_interval g.toOrderEmbedding c n

end Comp

section CompLinear

variable {α : Type*} [LinearOrder α]

theorem Comparison.interval_injective (c : Comparison) :
    Function.Injective (c.interval : α → Set α) := by
  cases c
  exacts [Set.singleton_injective, Set.Ici_injective, Set.Ioi_injective, Set.Iic_injective,
    Set.Iio_injective]

theorem Comparison.preimage_interval_eq_iff (g : α ≃o α) (c : Comparison) (n : α) :
    g ⁻¹' c.interval n = c.interval n ↔ Function.IsFixedPt g n := by
  have h : g ⁻¹' c.interval n = c.interval (g.symm n) := by
    simpa using Comparison.preimage_interval g.toOrderEmbedding c (g.symm n)
  rw [h, c.interval_injective.eq_iff, g.symm_apply_eq, eq_comm]
  rfl

theorem Comparison.forall_preimage_interval_eq_iff (g : α ≃o α) (c : Comparison) :
    (∀ n, g ⁻¹' c.interval n = c.interval n) ↔ g = OrderIso.refl α := by
  simp only [Comparison.preimage_interval_eq_iff, Function.IsFixedPt]
  refine ⟨fun h ↦ OrderIso.ext (funext h), ?_⟩
  rintro rfl n
  rfl

end CompLinear

/-! ### Scale-sensitive maximality

[rett-2026]: MAX_c(X) picks the element(s) of X that c-dominate all other members. For the
`<` scale (`.lt`) this is the GLB (earliest / smallest), for `>` (`.gt`) the LUB (latest /
largest). The same operator underlies both temporal connectives (*before* / *after*) and
degree comparatives. `maxOnScale_lt_eq` / `maxOnScale_ge_eq` / `maxOnScale_gt_eq` ground the
operator in mathlib's `IsLeast` / `IsGreatest`, and the interval evaluations are corollaries. -/

/-- Order-sensitive maximality, [rett-2026] (44), picks the elements of `X` that dominate every
other element under the comparison `c`. -/
def maxOnScale {α : Type*} [Preorder α] (c : Comparison) (X : Set α) : Set α :=
  { x | x ∈ X ∧ ∀ x' ∈ X, x' ≠ x → c.Rel x x' }

theorem maxOnScale_singleton {α : Type*} [Preorder α] (c : Comparison) (x : α) :
    maxOnScale c {x} = {x} := by
  ext y
  simp only [maxOnScale, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl
    exact ⟨rfl, fun x' hx' hne => absurd hx' hne⟩

theorem maxOnScale_ge_eq {α : Type*} [Preorder α] (X : Set α) :
    maxOnScale .ge X = {x | IsGreatest X x} := by
  ext x
  simp only [maxOnScale, Comparison.Rel, Set.mem_ofPred_eq, IsGreatest,
    upperBounds, ge_iff_le]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩,
    fun ⟨hx, hub⟩ => ⟨hx, fun y hy _ => hub hy⟩⟩
  rcases eq_or_ne y x with rfl | hne
  · exact le_refl _
  · exact hdom y hy hne

theorem maxOnScale_lt_eq {α : Type*} [PartialOrder α] (X : Set α) :
    maxOnScale .lt X = {x | IsLeast X x} := by
  ext x
  simp only [maxOnScale, Comparison.Rel, Set.mem_ofPred_eq, IsLeast, lowerBounds]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩, fun ⟨hx, hlb⟩ => ⟨hx, fun y hy hne => ?_⟩⟩
  · rcases eq_or_ne y x with rfl | hne
    · exact le_refl _
    · exact (hdom y hy hne).le
  · exact lt_of_le_of_ne (hlb hy) (Ne.symm hne)

theorem maxOnScale_gt_eq {α : Type*} [PartialOrder α] (X : Set α) :
    maxOnScale .gt X = {x | IsGreatest X x} := by
  ext x
  simp only [maxOnScale, Comparison.Rel, Set.mem_ofPred_eq, IsGreatest, upperBounds,
    gt_iff_lt]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩, fun ⟨hx, hub⟩ => ⟨hx, fun y hy hne => ?_⟩⟩
  · rcases eq_or_ne y x with rfl | hne
    · exact le_refl _
    · exact (hdom y hy hne).le
  · exact lt_of_le_of_ne (hub hy) hne

theorem maxOnScale_lt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale .lt { x : α | s ≤ x ∧ x ≤ f } = {s} := by
  rw [maxOnScale_lt_eq]
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨isLeast_Icc hsf, fun _ h => h.unique (isLeast_Icc hsf)⟩

theorem maxOnScale_gt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale .gt { x : α | s ≤ x ∧ x ≤ f } = {f} := by
  rw [maxOnScale_gt_eq]
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨isGreatest_Icc hsf, fun _ h => h.unique (isGreatest_Icc hsf)⟩

end Degree
