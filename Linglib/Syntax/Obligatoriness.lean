module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Obligatoriness

This file defines `Obligatoriness`, whether an element or process is obligatory, optional or
excluded in a context: a particle in a sentence type, verb second in an embedding context, overt
case on an object of a given prominence, a Case a language's verbs assign. The values are ordered by
how far the element is required. In a context the element is obligatory when every form the
grammar admits there has it, excluded when none does, and optional otherwise. Its distribution
gives its obligatoriness in each context, and the distribution's two zones, where the element is
required and where it may occur, determine it.

## Main definitions

* `Obligatoriness`, with its linear order from `excluded` to `obligatory`.
* `Obligatoriness.allowed`, `Obligatoriness.ofAllowed`: the presence values a value allows, and
  the value allowing a set of them.
* `Obligatoriness.of`: the obligatoriness of a property over the forms a grammar admits.
* `Obligatoriness.required`, `Obligatoriness.possible`: the zones of a distribution.

## Main results

* `Obligatoriness.monotone_iff`: a distribution rises along an order iff both zones are upper sets.

## References

* [aissen-2003]
-/

@[expose] public section

/-- Whether an element or process is obligatory, optional or excluded in a context, the three
classes of objects that differential object marking distinguishes, in [aissen-2003]'s words. -/
inductive Obligatoriness where
  | excluded
  | optional
  | obligatory
  deriving DecidableEq, Repr, Fintype

namespace Obligatoriness

/-- Ordered by how far the element is required. -/
instance : LinearOrder Obligatoriness := .lift' (·.ctorIdx) (by decide)

instance : BoundedOrder Obligatoriness where
  bot := .excluded
  bot_le o := by cases o <;> decide
  top := .obligatory
  le_top o := by cases o <;> decide

/-- The values the presence of the element may take: presence where it is obligatory, absence
where it is excluded, either where it is optional. -/
def allowed : Obligatoriness → Finset Bool
  | .obligatory => {true}
  | .excluded => {false}
  | .optional => .univ

theorem allowed_injective : Function.Injective allowed := by decide

/-- The value allowing exactly the presence values in `a`: obligatory for presence alone, excluded
for absence alone, optional for both, and excluded for the empty set. -/
def ofAllowed (a : Finset Bool) : Obligatoriness :=
  if true ∈ a then if false ∈ a then .optional else .obligatory else .excluded

@[simp] theorem ofAllowed_allowed (o : Obligatoriness) : ofAllowed o.allowed = o := by
  decide +revert

theorem allowed_ofAllowed {a : Finset Bool} (h : a.Nonempty) : (ofAllowed a).allowed = a := by
  obtain ⟨b, hb⟩ := h
  ext x
  by_cases ht : true ∈ a <;> by_cases hf : false ∈ a <;> cases x <;> cases b <;>
    simp_all [ofAllowed, allowed]

theorem optional_le_ofAllowed_iff {a : Finset Bool} : .optional ≤ ofAllowed a ↔ true ∈ a := by
  unfold ofAllowed; split_ifs <;> simp [*] <;> decide

theorem obligatory_le_ofAllowed_iff {a : Finset Bool} :
    .obligatory ≤ ofAllowed a ↔ true ∈ a ∧ false ∉ a := by
  unfold ofAllowed; split_ifs <;> simp [*] <;> decide

/-! ### Over admitted forms -/

section Forms

variable {α : Type*} {S : Finset α} {p : α → Bool}

/-- The obligatoriness of the property `p` over the forms `S` a grammar admits in a context:
obligatory when every form has it, excluded when none does, and optional otherwise. -/
def of (S : Finset α) (p : α → Bool) : Obligatoriness := ofAllowed (S.image p)

theorem allowed_of (hS : S.Nonempty) : (of S p).allowed = S.image p :=
  allowed_ofAllowed (hS.image p)

theorem optional_le_of_iff : .optional ≤ of S p ↔ ∃ x ∈ S, p x := by
  simp [of, optional_le_ofAllowed_iff]

theorem obligatory_le_of_iff (hS : S.Nonempty) : .obligatory ≤ of S p ↔ ∀ x ∈ S, p x := by
  obtain ⟨y, hy⟩ := hS
  simp only [of, obligatory_le_ofAllowed_iff, Finset.mem_image]
  refine ⟨fun ⟨_, h⟩ x hx ↦ ?_,
    fun h ↦ ⟨⟨y, hy, h y hy⟩, fun ⟨x, hx, hpx⟩ ↦ by simp [h x hx] at hpx⟩⟩
  by_contra hpx
  exact h ⟨x, hx, by simpa using hpx⟩

end Forms

/-! ### Distributions

The distribution of an element gives its obligatoriness in each context. Its zones are the
contexts where it is required and those where it may occur, which differential object marking
calls the obligatory and the possible zone. -/

section Distribution

variable {C : Type*} (μ : C → Obligatoriness)

/-- The contexts in which the element is required. -/
def required : Set C := {c | .obligatory ≤ μ c}

/-- The contexts in which the element may occur. -/
def possible : Set C := {c | .optional ≤ μ c}

variable {μ} {c : C}

@[simp] theorem mem_required : c ∈ required μ ↔ μ c = .obligatory := by
  change _ ≤ μ c ↔ _; cases μ c <;> decide

@[simp] theorem mem_possible : c ∈ possible μ ↔ μ c ≠ .excluded := by
  change _ ≤ μ c ↔ _; cases μ c <;> decide

theorem required_subset_possible : required μ ⊆ possible μ :=
  fun _ h ↦ le_trans (show Obligatoriness.optional ≤ .obligatory by decide) h

/-- A distribution rises along an order exactly when both its zones are upper sets. -/
theorem monotone_iff [Preorder C] :
    Monotone μ ↔ IsUpperSet (required μ) ∧ IsUpperSet (possible μ) := by
  refine ⟨fun h ↦ ⟨fun _ _ hab ha ↦ le_trans ha (h hab), fun _ _ hab ha ↦ le_trans ha (h hab)⟩,
    fun ⟨hr, hp⟩ a b hab ↦ ?_⟩
  cases ha : μ a
  · exact bot_le
  · exact hp hab (show .optional ≤ μ a from ha ▸ le_rfl)
  · exact hr hab (show .obligatory ≤ μ a from ha ▸ le_rfl)

/-- A distribution falls along an order exactly when both its zones are lower sets. -/
theorem antitone_iff [Preorder C] :
    Antitone μ ↔ IsLowerSet (required μ) ∧ IsLowerSet (possible μ) := by
  refine ⟨fun h ↦ ⟨fun _ _ hab ha ↦ le_trans ha (h hab), fun _ _ hab ha ↦ le_trans ha (h hab)⟩,
    fun ⟨hr, hp⟩ a b hab ↦ ?_⟩
  cases hb : μ b
  · exact bot_le
  · exact hp hab (show .optional ≤ μ b from hb ▸ le_rfl)
  · exact hr hab (show .obligatory ≤ μ b from hb ▸ le_rfl)

end Distribution

end Obligatoriness
