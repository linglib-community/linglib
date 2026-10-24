/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic

/-!
# Set-relation decidability over finite types

`Set.decidableSubsetOfFintype`, `Set.decidableSSubsetOfFintype` and `Set.decidableEqOfFintype`
derive `Decidable (s ⊆ t)`, `Decidable (s ⊂ t)` and `Decidable (s = t)`, and
`Set.decidableEqOnOfFintype` derives `Decidable (Set.EqOn f g s)`, from `Fintype` plus decidable
membership. Deliberately `def`s, not `instance`s, following
mathlib's `Set.decidableMemOfFintype`: global `Decidable` instances on `Set`
relations risk instance loops and higher-order `DecidablePred` searches.
Activate with `attribute [local instance] Set.decidableSubsetOfFintype`.
-/

@[expose] public section

/-- `Decidable (s ⊆ t)` from `Fintype` plus decidable membership.
Not an instance; activate locally. -/
@[implicit_reducible]
def Set.decidableSubsetOfFintype {α : Type*} [Fintype α]
    (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (s ⊆ t) :=
  show Decidable (∀ ⦃a⦄, a ∈ s → a ∈ t) from inferInstance

/-- `Decidable (s ⊂ t)` from `Fintype` plus decidable membership.
Not an instance; activate locally. -/
@[implicit_reducible]
def Set.decidableSSubsetOfFintype {α : Type*} [Fintype α]
    (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (s ⊂ t) :=
  haveI := decidableSubsetOfFintype s t
  haveI := decidableSubsetOfFintype t s
  decidable_of_iff _ ssubset_iff_subset_not_subset.symm

/-- `Decidable (s = t)` from `Fintype` plus decidable membership.
Not an instance; activate locally. -/
@[implicit_reducible]
def Set.decidableEqOfFintype {α : Type*} [Fintype α]
    (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (s = t) :=
  decidable_of_iff _ Set.ext_iff.symm

/-- `Decidable (Set.EqOn f g s)` from `Fintype` plus decidable membership.
Not an instance; activate locally. -/
@[implicit_reducible]
def Set.decidableEqOnOfFintype {α β : Type*} [Fintype α] [DecidableEq β]
    (f g : α → β) (s : Set α) [DecidablePred (· ∈ s)] :
    Decidable (Set.EqOn f g s) :=
  show Decidable (∀ ⦃a⦄, a ∈ s → f a = g a) from inferInstance
