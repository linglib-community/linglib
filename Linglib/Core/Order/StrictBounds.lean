module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.UpperLower.Closure

/-!
# Strict bounds of a set

`[UPSTREAM]` The strict analogues of mathlib's `upperBounds` and `lowerBounds`:
`strictUpperBounds s` is the set of points strictly above every element of `s`. Mathlib has no
strict-bounds primitive, routing strictness through `Set.Ioi` or `ssubset` instead.
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

@[to_dual (attr := simp)]
theorem strictUpperBounds_empty : strictUpperBounds (∅ : Set α) = Set.univ := by
  ext; simp [strictUpperBounds]

@[to_dual]
theorem strictUpperBounds_union (s t : Set α) :
    strictUpperBounds (s ∪ t) = strictUpperBounds s ∩ strictUpperBounds t := by
  ext; simp [strictUpperBounds, or_imp, forall_and]

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
