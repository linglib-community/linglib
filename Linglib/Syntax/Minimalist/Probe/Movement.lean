/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Probe.BestMatch

/-!
# Movement probes

A head may carry conditions on movement as well as on agreement, each an interaction and a
satisfaction specification, a relativized EPP. A movement probe searches its domain as Agree does
and attracts the goal it interacts with to its specifier. Merge being binary, it attracts at most
one goal, so a probe that interacts with two goals attracts neither, the Ban on Multiple Move.

## Main definitions

* `Minimalist.Probe.Spec.attract`: the goal a movement probe attracts.

## Main results

* `Minimalist.Probe.Spec.attract_eq_some_iff`: a probe attracts the one goal it interacts with.
* `Minimalist.Probe.Spec.attract_eq_none_of_mem_of_mem_of_ne`: the Ban on Multiple Move.
* `Minimalist.Probe.Spec.attract_map_singleton`: on singleton classes a probe whose interacting
  goals satisfy it attracts the goal of the linear search.

## Implementation notes

Movement is a search of its own, with its own conditions. The movement subfeatures of the
algorithm `Probe.Spec.agree` implements, which move goals of the agreement search, are not
modelled.

## References

* [hammerly-mathieu-2026]
* [coon-keine-2021]
* [deal-2025a]
-/

@[expose] public section

namespace Minimalist.Probe.Spec

variable {α F : Type*} [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- The goal a movement probe attracts, the one goal it interacts with. Binary Merge cannot move
two goals at once ([coon-keine-2021]), and a probe that interacts with several attracts none, the
Ban on Multiple Move of [hammerly-mathieu-2026]. -/
def attract (d : List (List α)) : Option α :=
  match sp.interacted feats d with
  | [a] => some a
  | _ => none

variable {sp feats} {a b : α} {d : List (List α)}

theorem attract_eq_some_iff : sp.attract feats d = some a ↔ sp.interacted feats d = [a] := by
  unfold attract
  split <;> simp_all

/-- The Ban on Multiple Move: a probe interacting with two goals attracts neither. -/
theorem attract_eq_none_of_mem_of_mem_of_ne (ha : a ∈ sp.interacted feats d)
    (hb : b ∈ sp.interacted feats d) (hab : a ≠ b) : sp.attract feats d = none :=
  Option.eq_none_iff_forall_ne_some.2 fun x hx ↦ by
    rw [attract_eq_some_iff.1 hx, List.mem_singleton] at ha hb
    exact hab (ha.trans hb.symm)

/-- An attracted goal is a goal of the domain. -/
theorem mem_flatten_of_attract_eq_some (h : sp.attract feats d = some a) : a ∈ d.flatten :=
  mem_flatten_of_mem_interacted (sp := sp) (feats := feats) <| by
    rw [attract_eq_some_iff.mp h]; exact List.mem_singleton_self a

/-- On singleton classes a probe whose interacting goals satisfy it attracts the goal of the
linear search. -/
theorem attract_map_singleton (l : List α)
    (h : ∀ a, (sp.toProbe feats).int a → (sp.toProbe feats).sat a) :
    sp.attract feats (l.map ([·])) = (sp.toProbe feats).goal l := by
  rw [attract, interacted_map_singleton, inspected_filter_int_eq_goal h]
  cases (sp.toProbe feats).goal l <;> rfl

@[simp] theorem attract_bot : (⊥ : Spec F).attract feats d = none := by
  simp [attract]

end Minimalist.Probe.Spec
