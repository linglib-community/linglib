module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Concept
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.UpperLower.Closure

/-!
# Strict bounds of a set

`[UPSTREAM]` The strict analogues of mathlib's `upperBounds` and `lowerBounds`:
`strictUpperBounds s` is the set of points strictly above every element of `s`. They are the
[polars](##strictUpperBounds_eq_upperPolar) of `<`, as `upperBounds` and `lowerBounds` are the
polars of `≤`, so they turn unions into intersections and are antitone.
-/

@[expose] public section

variable {α : Type*} [Preorder α] {s : Set α} {a x : α}

/-- The set of points strictly greater than every element of `s`. -/
@[to_dual /-- The set of points strictly less than every element of `s`. -/]
def strictUpperBounds (s : Set α) : Set α := {x | ∀ ⦃a⦄, a ∈ s → a < x}

@[to_dual]
theorem mem_strictUpperBounds : x ∈ strictUpperBounds s ↔ ∀ ⦃a⦄, a ∈ s → a < x :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem strictUpperBounds_singleton : strictUpperBounds {a} = Set.Ioi a := by
  ext; simp [strictUpperBounds]

/-- The strict upper bounds of a set are its polar under `<`. -/
theorem strictUpperBounds_eq_upperPolar (s : Set α) :
    strictUpperBounds s = upperPolar (· < ·) s :=
  rfl

/-- The strict lower bounds of a set are its polar under `<`. -/
theorem strictLowerBounds_eq_lowerPolar (s : Set α) :
    strictLowerBounds s = lowerPolar (· < ·) s :=
  rfl

@[simp]
theorem strictUpperBounds_empty : strictUpperBounds (∅ : Set α) = Set.univ :=
  upperPolar_empty _

@[simp]
theorem strictLowerBounds_empty : strictLowerBounds (∅ : Set α) = Set.univ :=
  lowerPolar_empty _

theorem strictUpperBounds_union (s t : Set α) :
    strictUpperBounds (s ∪ t) = strictUpperBounds s ∩ strictUpperBounds t :=
  upperPolar_union _ s t

theorem strictLowerBounds_union (s t : Set α) :
    strictLowerBounds (s ∪ t) = strictLowerBounds s ∩ strictLowerBounds t :=
  lowerPolar_union _ s t

theorem strictUpperBounds_anti : Antitone (strictUpperBounds : Set α → Set α) :=
  upperPolar_anti _

theorem strictLowerBounds_anti : Antitone (strictLowerBounds : Set α → Set α) :=
  lowerPolar_anti _

@[to_dual]
theorem isUpperSet_strictUpperBounds (s : Set α) : IsUpperSet (strictUpperBounds s) :=
  fun _ _ hxy hx _ ha ↦ (hx ha).trans_le hxy

@[to_dual]
theorem IsGreatest.strictUpperBounds_eq (h : IsGreatest s a) : strictUpperBounds s = Set.Ioi a :=
  Set.ext fun _ ↦ ⟨fun hx ↦ hx h.1, fun hx _ hb ↦ (h.2 hb).trans_lt hx⟩

@[to_dual /-- In a linear order the points strictly below a set are those outside its upper
closure. -/]
theorem strictUpperBounds_eq_compl_lowerClosure {α : Type*} [LinearOrder α] (s : Set α) :
    strictUpperBounds s = (lowerClosure s : Set α)ᶜ := by
  ext; simp [strictUpperBounds]
