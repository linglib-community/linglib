/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Situation.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Closure
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Closure

/-!
# The world of a situation

In a situation semantics whose situations are particulars, every situation is part of exactly one
world. The map that sends a situation to its world is then a closure operator on the order of
situations whose closed situations are the worlds, and there is such an operator exactly when
every situation is part of a unique maximal one. Parthood stays within a world, and a proposition
about the world of a situation is persistent.

The propositions of a possible-worlds semantics are the persistent propositions about the world.
A persistent proposition is true in only the worlds of `q` exactly when it is true in only the
situations whose world is in `q`, and the proposition that the world of a situation is in `q` is
true in the worlds of `q` and no others. So a persistent proposition implies `q` exactly when it
is included in the proposition that the world is in `q`.

Where a situation may be part of several worlds, as a state is in truthmaker semantics, or where
the worlds are given from outside the order by the situation each one is, a proposition is true
at a world when some situation in which it is true is part of the world. For a persistent
proposition this is truth in the situation that the world is.

## Main definitions

* `Situation.IsWorldMap`: a closure operator whose closed situations are the worlds.
* `Situation.partOf`: the relation of a situation to the worlds it is part of, for worlds given by
  the situations they are.

## Main results

* `Situation.exists_isWorldMap_iff`: there is a world map exactly when every situation is part of
  a unique world.
* `Situation.IsWorldMap.inter_worlds_subset_iff`,
  `Situation.IsWorldMap.preimage_inter_worlds`: restriction of a persistent proposition to the
  worlds is left adjoint to pullback along the world map, and restricting a pullback returns the
  set of worlds.
* `Situation.diamond_inv_partOf_iff_mem`: a persistent proposition is true at a world exactly
  when it is true in the situation the world is.
* `Situation.mem_worlds_possible_iff`: the worlds of the possible states of a state space are the
  maximal possible states.

## Implementation notes

The world map is a hypothesis on a closure operator and not a class on the order, since an order
has at most one. That every situation is part of some world is `IsCofinal (worlds S)`.

## References

* [kratzer-1989]
* [kratzer-2012]
* [fine-2017a]
-/

@[expose] public section

namespace Situation

open Set ModalLogic
open scoped SetRel

variable {S : Type*} [PartialOrder S] {p q : Set S} {s t w : S}

/-! ### Situations that are part of some world -/

/-- Where every situation is part of a world, a persistent proposition is consistent exactly when
it is true in some situation. -/
theorem isConsistent_singleton_iff (hS : IsCofinal (worlds S)) (hp : IsUpperSet p) :
    IsConsistent {p} ↔ p.Nonempty := by
  rw [IsConsistent, sInter_singleton]
  exact ⟨fun ⟨w, _, hw⟩ ↦ ⟨w, hw⟩, fun ⟨s, hs⟩ ↦ let ⟨w, hw, hsw⟩ := hS s; ⟨w, hw, hp hsw hs⟩⟩

/-! ### Situations that are part of exactly one world -/

/-- A closure operator on situations is the world map when its closed situations are the worlds:
it sends each situation to the world it is part of. -/
def IsWorldMap (c : ClosureOperator S) : Prop := ∀ s, c.IsClosed s ↔ IsMax s

namespace IsWorldMap

variable {c c' : ClosureOperator S}

theorem mem_worlds (hc : IsWorldMap c) (s : S) : c s ∈ worlds S :=
  (hc _).1 (c.isClosed_closure s)

/-- A world is its own world. -/
theorem apply_eq_self (hc : IsWorldMap c) (hw : w ∈ worlds S) : c w = w :=
  ((hc w).2 hw).closure_eq

/-- A situation and a situation it is part of have the same world. -/
theorem eq_of_le (hc : IsWorldMap c) (h : s ≤ t) : c s = c t :=
  le_antisymm (c.monotone h) (hc.mem_worlds s (c.monotone h))

/-- The world of a situation is the only world it is part of. -/
theorem eq_of_mem_worlds (hc : IsWorldMap c) (hw : w ∈ worlds S) (h : s ≤ w) : c s = w :=
  (hc.eq_of_le h).trans (hc.apply_eq_self hw)

theorem existsUnique (hc : IsWorldMap c) (s : S) : ∃! w, w ∈ worlds S ∧ s ≤ w :=
  ⟨c s, ⟨hc.mem_worlds s, c.le_closure s⟩, fun _ ⟨hw, h⟩ ↦ (hc.eq_of_mem_worlds hw h).symm⟩

/-- An order of situations has at most one world map. -/
protected theorem unique (hc : IsWorldMap c) (hc' : IsWorldMap c') : c = c' :=
  ClosureOperator.ext _ _ fun s ↦
    hc.eq_of_mem_worlds (hc'.mem_worlds s) (c'.le_closure s)

/-- A persistent proposition true in a situation is true in its world. -/
theorem mem_of_mem (_ : IsWorldMap c) (hp : IsUpperSet p) (hs : s ∈ p) : c s ∈ p :=
  hp (c.le_closure s) hs

/-- A proposition about the world of a situation is persistent. -/
theorem isUpperSet_preimage (hc : IsWorldMap c) (q : Set S) : IsUpperSet (c ⁻¹' q) :=
  fun _ _ h hs ↦ mem_preimage.2 (hc.eq_of_le h ▸ hs)

/-- A persistent proposition is true in only the worlds of `q` exactly when it is true in only the
situations whose world is in `q`. -/
theorem inter_worlds_subset_iff (hc : IsWorldMap c) (hp : IsUpperSet p) :
    p ∩ worlds S ⊆ q ↔ p ⊆ c ⁻¹' q :=
  ⟨fun h _ hs ↦ h ⟨hc.mem_of_mem hp hs, hc.mem_worlds _⟩,
    fun h _ ⟨hw, hm⟩ ↦ hc.apply_eq_self hm ▸ h hw⟩

/-- The proposition that the world of a situation is in `q` is true in the worlds of `q` and no
others. -/
theorem preimage_inter_worlds (hc : IsWorldMap c) (q : Set S) :
    c ⁻¹' q ∩ worlds S = q ∩ worlds S :=
  Set.ext fun _ ↦ and_congr_left fun hw ↦ by rw [mem_preimage, hc.apply_eq_self hw]

/-- A persistent proposition implies `q` exactly when it is included in the proposition that the
world is in `q`. -/
theorem follows_singleton_iff (hc : IsWorldMap c) (hp : IsUpperSet p) :
    Follows {p} q ↔ p ⊆ c ⁻¹' q := by
  rw [Follows, sInter_singleton, inter_comm, hc.inter_worlds_subset_iff hp]

end IsWorldMap

/-- There is a world map exactly when every situation is part of a unique world. -/
theorem exists_isWorldMap_iff :
    (∃ c : ClosureOperator S, IsWorldMap c) ↔ ∀ s : S, ∃! w, w ∈ worlds S ∧ s ≤ w := by
  refine ⟨fun ⟨_, hc⟩ ↦ hc.existsUnique, fun h ↦ ?_⟩
  choose f hf huniq using fun s ↦ (h s)
  have hfw (s : S) (hs : s ∈ worlds S) : f s = s := (huniq s s ⟨hs, le_rfl⟩).symm
  refine ⟨ClosureOperator.mk' f (fun s t hst ↦ ?_) (fun s ↦ (hf s).2)
    fun s ↦ (hfw _ (hf s).1).le, fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩⟩
  · exact (huniq s (f t) ⟨(hf t).1, hst.trans (hf t).2⟩).ge
  · exact (ClosureOperator.IsClosed.closure_eq hs : f s = s) ▸ (hf s).1
  · exact (ClosureOperator.isClosed_iff _).2 (hfw s hs)

/-! ### Worlds given by the situations they are -/

section PartOf

variable {W : Type*} {state : W → S}

/-- The relation of a situation to the worlds it is part of, where `state w` is the situation
that the world `w` is. -/
def partOf (state : W → S) : SetRel S W := {x | x.1 ≤ state x.2}

@[simp] theorem mem_partOf {v : W} : s ~[partOf state] v ↔ s ≤ state v := Iff.rfl

/-- A proposition is true at a world when some situation in which it is true is part of the world:
the situation that the world is belongs to the persistent closure of the proposition. -/
theorem diamond_inv_partOf_iff {v : W} :
    ◇[(partOf state).inv] (· ∈ p) v ↔ state v ∈ upperClosure p :=
  ⟨fun ⟨s, h, hp⟩ ↦ ⟨s, hp, h⟩, fun ⟨s, hp, h⟩ ↦ ⟨s, h, hp⟩⟩

/-- A persistent proposition is true at a world exactly when it is true in the situation the world
is. -/
theorem diamond_inv_partOf_iff_mem (hp : IsUpperSet p) {v : W} :
    ◇[(partOf state).inv] (· ∈ p) v ↔ state v ∈ p :=
  diamond_inv_partOf_iff.trans ⟨fun ⟨_, hs, h⟩ ↦ hp h hs, fun h ↦ ⟨_, h, le_rfl⟩⟩

end PartOf

/-! ### Possible states -/

/-- The worlds of the possible states of a state space are the maximal possible states. -/
theorem mem_worlds_possible_iff (P : LowerSet S) (x : P) :
    x ∈ worlds P ↔ Maximal (· ∈ P) (x : S) :=
  ⟨fun h ↦ ⟨x.2, fun y hy hxy ↦ h (b := ⟨y, hy⟩) hxy⟩, fun h y hxy ↦ h.2 y.2 hxy⟩

end Situation
