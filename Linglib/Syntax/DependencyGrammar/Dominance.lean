/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Maps
public import Linglib.Core.Relation.ReflTransGen

/-!
# Dominance

A position of a dependency graph dominates another when a chain of arcs leads from the first to
the second, and its yield is the set of positions it dominates.

## Main definitions

* `Graph.Dominates`: the reflexive-transitive closure of the arc relation.
* `Graph.yield`: the set of positions a position dominates.

## Main statements

* `Graph.exists_adj_adj_of_not_dominates`: positions under a common dominator, neither dominating the
  other, lie under distinct dependents of one position.
* `Graph.dominates_map`: dominance is invariant under transport.

## Implementation notes

`Graph.Dominates` is an `abbrev` for `Relation.ReflTransGen g.Adj`, so mathlib's closure API applies
to dominance directly and decidability comes from `Core/Relation/ReflTransGen.lean`. Dot
notation on a dominance hypothesis therefore resolves in `Relation.ReflTransGen`.

## References

* [kuhlmann-nivre-2006]
-/

@[expose] public section

namespace DependencyGrammar

open Relation

variable {L : Type*} {n : ℕ} {g : Graph L n} {u v w x y : Fin n}

/-! ### Dominance -/

/-- `v` dominates `x` when a possibly empty chain of arcs leads from `v` to `x`. -/
abbrev Graph.Dominates (g : Graph L n) : Fin n → Fin n → Prop :=
  ReflTransGen g.Adj

/-- The yield of `v` is the set of positions `v` dominates, `v` itself included. -/
def Graph.yield (g : Graph L n) (v : Fin n) : Set (Fin n) :=
  {x | g.Dominates v x}

@[simp] theorem Graph.mem_yield : x ∈ g.yield v ↔ g.Dominates v x := Iff.rfl

instance (g : Graph L n) (v : Fin n) : DecidablePred (· ∈ g.yield v) :=
  fun _ ↦ inferInstanceAs (Decidable (g.Dominates v _))


theorem Graph.exists_adj_mem_yield (hx : x ∈ g.yield v) (hne : x ≠ v) :
    ∃ u, g.Adj v u ∧ x ∈ g.yield u :=
  (ReflTransGen.cases_head hx).resolve_left hne.symm

theorem Graph.exists_link_across {S : Set (Fin n)} (hx : g.Dominates v x) (hy : g.Dominates v y)
    (hxS : x ∈ S) (hyS : y ∉ S) :
    ∃ p q, g.Linked p q ∧ g.Dominates v p ∧ g.Dominates v q ∧ p ∈ S ∧ q ∉ S := by
  by_cases hv : v ∈ S
  · obtain ⟨p, q, hpq, hpS, hqS, hvp, -⟩ := hy.exists_boundary hv hyS
    exact ⟨p, q, .inl hpq, hvp, hvp.tail hpq, hpS, hqS⟩
  · obtain ⟨p, q, hpq, hpS, hqS, hvp, -⟩ := hx.exists_boundary (S := Sᶜ) hv (not_not_intro hxS)
    exact ⟨q, p, .inr hpq, hvp.tail hpq, hvp, not_not.1 hqS, hpS⟩

/-- Positions under a common dominator, neither of which dominates the other, lie under distinct
dependents of one position, their lowest common governor. -/
theorem Graph.exists_adj_adj_of_not_dominates (hu : g.Dominates x u) (hv : g.Dominates x v)
    (huv : ¬ g.Dominates u v) (hvu : ¬ g.Dominates v u) :
    ∃ p u' v', g.Adj p u' ∧ g.Adj p v' ∧ u' ≠ v' ∧ g.Dominates u' u ∧ g.Dominates v' v := by
  obtain ⟨p, u', hpu', hp, hu', -, hu'u⟩ :=
    hu.exists_boundary (S := {z | g.Dominates z v}) hv huv
  obtain rfl | ⟨v', hpv', hv'v⟩ := ReflTransGen.cases_head hp
  · exact absurd (hu'u.head hpu') hvu
  · exact ⟨p, u', v', hpu', hpv', fun h ↦ hu' (h ▸ hv'v), hu'u, hv'v⟩

theorem Graph.dominates_map {g : Graph L n} {σ : Equiv.Perm (Fin n)} {v w : Fin n} :
    (g.map σ).Dominates v w ↔ g.Dominates (σ.symm v) (σ.symm w) :=
  ⟨fun h ↦ ReflTransGen.lift (r := (g.map σ).Adj) (p := g.Adj) σ.symm (fun _ _ h ↦ h) _ _ h,
    fun h ↦ by
      simpa [Function.onFun] using ReflTransGen.lift (r := g.Adj) (p := (g.map σ).Adj) σ
        (fun a b h ↦ by simpa [Function.onFun] using h) _ _ h⟩

end DependencyGrammar
