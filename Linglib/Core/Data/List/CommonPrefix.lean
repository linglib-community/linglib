/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Infix

/-!
# The longest common prefix of two lists

`List.commonPrefix l₁ l₂` is the longest list that is a prefix of both `l₁` and `l₂`. It is the
meet of the prefix order: the prefixes of `commonPrefix l₁ l₂` are exactly the common prefixes of
`l₁` and `l₂`, so `commonPrefix` is commutative, associative and idempotent, as `Nat.gcd` is for
divisibility.

## Main definitions

* `List.commonPrefix`: the longest common prefix of two lists.

## Main results

* `List.prefix_commonPrefix_iff`: the prefixes of `commonPrefix l₁ l₂` are the common prefixes of
  `l₁` and `l₂`.
* `List.commonPrefix_comm`, `List.commonPrefix_assoc`, `List.commonPrefix_self`: the meet laws.
* `List.commonPrefix_eq_left`: `commonPrefix l₁ l₂ = l₁` exactly when `l₁ <+: l₂`.

## Implementation notes

[UPSTREAM] candidate: Batteries, beside `List.inits`. Neither core, Batteries nor mathlib defines
a longest common prefix of lists.
-/

@[expose] public section

namespace List

variable {α : Type*} [DecidableEq α] {a b : α} {r l₁ l₂ : List α}

/-- `commonPrefix l₁ l₂` is the longest common prefix of `l₁` and `l₂`. -/
def commonPrefix : List α → List α → List α
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

@[simp] theorem commonPrefix_nil_left (l : List α) : commonPrefix [] l = [] := rfl

@[simp] theorem commonPrefix_nil_right (l : List α) : commonPrefix l [] = [] := by
  cases l <;> rfl

theorem commonPrefix_cons_cons (a b : α) (l₁ l₂ : List α) :
    commonPrefix (a :: l₁) (b :: l₂) = if a = b then a :: commonPrefix l₁ l₂ else [] := rfl

@[simp] theorem commonPrefix_cons_cons_self (a : α) (l₁ l₂ : List α) :
    commonPrefix (a :: l₁) (a :: l₂) = a :: commonPrefix l₁ l₂ := ite_eq_left rfl

@[simp] theorem commonPrefix_cons_cons_of_ne (h : a ≠ b) (l₁ l₂ : List α) :
    commonPrefix (a :: l₁) (b :: l₂) = [] := ite_eq_right h

theorem commonPrefix_prefix_left : ∀ l₁ l₂ : List α, commonPrefix l₁ l₂ <+: l₁
  | [], _ | _ :: _, [] => by simp
  | a :: as, b :: bs => by
    by_cases h : a = b
    · subst h
      simpa using commonPrefix_prefix_left as bs
    · simp [h]

theorem commonPrefix_prefix_right : ∀ l₁ l₂ : List α, commonPrefix l₁ l₂ <+: l₂
  | [], _ | _ :: _, [] => by simp
  | a :: as, b :: bs => by
    by_cases h : a = b
    · subst h
      simpa using commonPrefix_prefix_right as bs
    · simp [h]

theorem prefix_commonPrefix : ∀ {r l₁ l₂ : List α}, r <+: l₁ → r <+: l₂ → r <+: commonPrefix l₁ l₂
  | [], _, _, _, _ => nil_prefix
  | _ :: rs, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => by
    simpa using prefix_commonPrefix (r := rs) (prefix_append _ _) (prefix_append _ _)

theorem prefix_commonPrefix_iff : r <+: commonPrefix l₁ l₂ ↔ r <+: l₁ ∧ r <+: l₂ :=
  ⟨fun h ↦ ⟨h.trans (commonPrefix_prefix_left _ _), h.trans (commonPrefix_prefix_right _ _)⟩,
    fun h ↦ prefix_commonPrefix h.1 h.2⟩

theorem commonPrefix_comm (l₁ l₂ : List α) : commonPrefix l₁ l₂ = commonPrefix l₂ l₁ :=
  eq_of_forall_prefix_iff fun _ ↦ by simp only [prefix_commonPrefix_iff, and_comm]

theorem commonPrefix_assoc (l₁ l₂ l₃ : List α) :
    commonPrefix (commonPrefix l₁ l₂) l₃ = commonPrefix l₁ (commonPrefix l₂ l₃) :=
  eq_of_forall_prefix_iff fun _ ↦ by simp only [prefix_commonPrefix_iff, and_assoc]

@[simp] theorem commonPrefix_self (l : List α) : commonPrefix l l = l :=
  eq_of_forall_prefix_iff fun _ ↦ by simp only [prefix_commonPrefix_iff, and_self]

@[simp] theorem commonPrefix_eq_left : commonPrefix l₁ l₂ = l₁ ↔ l₁ <+: l₂ :=
  ⟨fun h ↦ h ▸ commonPrefix_prefix_right l₁ l₂,
    fun h ↦ antisymm (commonPrefix_prefix_left l₁ l₂) (prefix_commonPrefix prefix_rfl h)⟩

@[simp] theorem commonPrefix_eq_right : commonPrefix l₁ l₂ = l₂ ↔ l₂ <+: l₁ := by
  rw [commonPrefix_comm, commonPrefix_eq_left]

end List
