/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get

/-!
# Simultaneous grafting on rose trees

This file defines `multiGraft T pairs`, which grafts several trees onto `T` at once. Each pair
`(p, S)` names a vertex of `T` by its address `p` and a tree `S` to become a new child of that
vertex; every address is read in the original `T`, as in Foissy's multiple grafting. Trees
grafted at the same vertex are prepended in the order of the pair list, so `multiGraft` depends on
that order, and `Insertion.lean` recovers independence of it once children are unordered.

## Main definitions

* `multiGraft`, `multiGraftChildren`: simultaneous grafting into a tree and into a forest.
* `rootPrependFilter`, `headChildFilter`, `tailChildFilter`: the pairs aimed at the root, at the
  first child, and at the later children, with the addresses shortened accordingly.

## Main results

* `filterMap_rootPrependFilter`, `filterMap_headChildFilter`, `filterMap_tailChildFilter`: each
  filter is a `List.filter` on the address followed by a projection.
* `multiGraft_nil`: grafting nothing leaves the tree unchanged.

## Implementation notes

The three filters are top-level definitions rather than inline `match` expressions so that every
caller elaborates the same matcher, which lets their `filterMap` equations rewrite across files.

## References

* [foissy-2021]
* [foissy-introduction-hopf-algebras-trees]
-/
@[expose] public section

namespace RoseTree

variable {α : Type*}

/-! ### Routing the pairs -/

/-- A pair aimed at the root yields its tree. -/
def rootPrependFilter (pair : List ℕ × RoseTree α) : Option (RoseTree α) :=
  match pair.fst with
  | []     => some pair.snd
  | _ :: _ => none

@[simp] theorem rootPrependFilter_of_nil (T : RoseTree α) :
    rootPrependFilter ((([], T) : List ℕ × RoseTree α)) = some T := rfl

@[simp] theorem rootPrependFilter_of_cons (i : ℕ) (rest : List ℕ) (T : RoseTree α) :
    rootPrependFilter ((i :: rest, T) : List ℕ × RoseTree α) = none := rfl

/-- A pair aimed inside the first child yields the pair with the leading index removed. -/
def headChildFilter (pair : List ℕ × RoseTree α) : Option (List ℕ × RoseTree α) :=
  match pair.fst with
  | 0 :: rest => some (rest, pair.snd)
  | _         => none

@[simp] theorem headChildFilter_of_nil (T : RoseTree α) :
    headChildFilter ((([], T) : List ℕ × RoseTree α)) = none := rfl

@[simp] theorem headChildFilter_of_zero_cons (rest : List ℕ) (T : RoseTree α) :
    headChildFilter ((0 :: rest, T) : List ℕ × RoseTree α) = some (rest, T) := rfl

@[simp] theorem headChildFilter_of_succ_cons (k : ℕ) (rest : List ℕ) (T : RoseTree α) :
    headChildFilter (((k + 1) :: rest, T) : List ℕ × RoseTree α) = none := rfl

/-- A pair aimed inside a later child yields the pair with the leading index decremented. -/
def tailChildFilter (pair : List ℕ × RoseTree α) : Option (List ℕ × RoseTree α) :=
  match pair.fst with
  | (k + 1) :: rest => some (k :: rest, pair.snd)
  | _               => none

@[simp] theorem tailChildFilter_of_nil (T : RoseTree α) :
    tailChildFilter ((([], T) : List ℕ × RoseTree α)) = none := rfl

@[simp] theorem tailChildFilter_of_zero_cons (rest : List ℕ) (T : RoseTree α) :
    tailChildFilter ((0 :: rest, T) : List ℕ × RoseTree α) = none := rfl

@[simp] theorem tailChildFilter_of_succ_cons (k : ℕ) (rest : List ℕ) (T : RoseTree α) :
    tailChildFilter (((k + 1) :: rest, T) : List ℕ × RoseTree α) = some (k :: rest, T) := rfl

/-! ### Simultaneous grafting -/

mutual
/-- `multiGraft T pairs` grafts the tree of each pair at the vertex its address names. The trees
aimed at the root are prepended to its children in pair-list order; the other pairs descend into
the child their first index names. -/
def multiGraft : RoseTree α → List (List ℕ × RoseTree α) → RoseTree α
  | .node a cs, pairs =>
      RoseTree.node a (pairs.filterMap rootPrependFilter ++ multiGraftChildren cs pairs)
/-- `multiGraftChildren cs pairs` grafts into the forest `cs`, where the first index of each
address names a tree of `cs`. -/
def multiGraftChildren :
    List (RoseTree α) → List (List ℕ × RoseTree α) → List (RoseTree α)
  | [],      _     => []
  | c :: cs, pairs =>
      multiGraft c (pairs.filterMap headChildFilter) ::
        multiGraftChildren cs (pairs.filterMap tailChildFilter)
end

@[simp] theorem multiGraft_node (a : α) (cs : List (RoseTree α))
    (pairs : List (List ℕ × RoseTree α)) :
    multiGraft (RoseTree.node a cs) pairs =
      RoseTree.node a (pairs.filterMap rootPrependFilter ++ multiGraftChildren cs pairs) := rfl

@[simp] theorem multiGraftChildren_nil_cs (pairs : List (List ℕ × RoseTree α)) :
    multiGraftChildren ([] : List (RoseTree α)) pairs = [] := rfl

@[simp] theorem multiGraftChildren_cons_cs (c : RoseTree α) (cs : List (RoseTree α))
    (pairs : List (List ℕ × RoseTree α)) :
    multiGraftChildren (c :: cs) pairs =
      multiGraft c (pairs.filterMap headChildFilter) ::
        multiGraftChildren cs (pairs.filterMap tailChildFilter) := rfl

/-! ### Filter characterizations

Each pair filter is a `List.filter` on the address followed by a projection, so `Insertion.lean`
can split the pair lists by a predicate on addresses. -/

theorem filterMap_rootPrependFilter (pairs : List (List ℕ × RoseTree α)) :
    pairs.filterMap rootPrependFilter =
      (pairs.filter fun p => decide (p.1 = [])).map Prod.snd := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    obtain ⟨q, T⟩ := p
    cases q <;> simp [ih]

theorem filterMap_headChildFilter (pairs : List (List ℕ × RoseTree α)) :
    pairs.filterMap headChildFilter =
      (pairs.filter fun p => decide (p.1.head? = some 0)).map (Prod.map List.tail id) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    obtain ⟨q, T⟩ := p
    rcases q with _ | ⟨_ | k, rest⟩ <;> simp [ih]

theorem filterMap_tailChildFilter (pairs : List (List ℕ × RoseTree α))
    (h : ∀ p ∈ pairs, p.1 ≠ []) :
    pairs.filterMap tailChildFilter =
      (pairs.filter fun p => decide (¬ p.1.head? = some 0)).map
        (Prod.map (List.modifyHead (· - 1)) id) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    obtain ⟨q, T⟩ := p
    have ih := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
    rcases q with _ | ⟨_ | k, rest⟩
    · exact absurd rfl (h ([], T) List.mem_cons_self)
    · simp [ih]
    · simp [ih]

@[simp] theorem value_multiGraft (T : RoseTree α) (pairs : List (List ℕ × RoseTree α)) :
    (multiGraft T pairs).value = T.value := by
  cases T; rfl

theorem multiGraftChildren_congr {cs : List (RoseTree α)}
    {pairs₁ pairs₂ : List (List ℕ × RoseTree α)}
    (h₁ : pairs₁.filterMap headChildFilter = pairs₂.filterMap headChildFilter)
    (h₂ : pairs₁.filterMap tailChildFilter = pairs₂.filterMap tailChildFilter) :
    multiGraftChildren cs pairs₁ = multiGraftChildren cs pairs₂ := by
  cases cs with
  | nil => rfl
  | cons c cs => rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs, h₁, h₂]

theorem multiGraftChildren_filter_ne_nil (cs : List (RoseTree α))
    (pairs : List (List ℕ × RoseTree α)) :
    multiGraftChildren cs (pairs.filter fun p => decide (¬ p.1 = [])) =
      multiGraftChildren cs pairs := by
  refine multiGraftChildren_congr ?_ ?_ <;>
  · rw [List.filterMap_filter]
    refine List.filterMap_congr fun p _ => ?_
    obtain ⟨q, T⟩ := p
    cases q <;> simp

theorem multiGraftChildren_length :
    ∀ (cs : List (RoseTree α)) (pairs : List (List ℕ × RoseTree α)),
    (multiGraftChildren cs pairs).length = cs.length
  | [], _ => rfl
  | c :: cs, pairs => by
    rw [multiGraftChildren_cons_cs, List.length_cons, List.length_cons,
      multiGraftChildren_length cs (pairs.filterMap tailChildFilter)]

mutual
theorem multiGraft_nil : ∀ (T : RoseTree α), multiGraft T [] = T
  | .node a cs => by
    show RoseTree.node a ([] ++ multiGraftChildren cs []) = RoseTree.node a cs
    rw [List.nil_append, multiGraftChildren_nil_pairs cs]
theorem multiGraftChildren_nil_pairs : ∀ (cs : List (RoseTree α)),
    multiGraftChildren cs [] = cs
  | [] => rfl
  | c :: cs => by
    show multiGraft c [] :: multiGraftChildren cs [] = c :: cs
    rw [multiGraft_nil c, multiGraftChildren_nil_pairs cs]
end

end RoseTree
