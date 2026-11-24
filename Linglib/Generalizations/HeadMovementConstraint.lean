/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.OrdConnected
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The Head Movement Constraint

The heads of a clause form a spine, listed from the bottom up, and a word may express several of
them. A hosting of the spine gives, for each of its positions, the head at which that position is
pronounced. The Head Movement Constraint, stated of hostings, says that the positions pronounced
at one head form an unbroken stretch of the spine: a word does not skip a head that lies between
two of its own. In Svenonius's terms the heads of a word are a span.

A hosting is a list, the head for each position in order, and the constraint is the predicate
`HMC.Holds` on it. A hosting obeys it exactly when the positions can be numbered, in an order
that never decreases up the spine, so that two positions are pronounced at the same head when they
have the same number. Blocks of positions, each block pronounced at a head of its own, obey it,
and a hosting that returns to a head after leaving it does not.

## Main definitions

* `HMC.Holds`: the positions pronounced at one head form a stretch of the spine.

## Main results

* `HMC.holds_iff_exists_monotone`: the constraint holds exactly when a monotone numbering of the
  positions has the hosting's kernel.
* `HMC.holds_flatMap_replicate`: blocks pronounced at distinct heads obey the constraint.
* `HMC.not_holds_of_ne`: a hosting that returns to a head does not.

## Implementation notes

The constraint is stated of what is pronounced where, and mentions no operation that forms words.
An account of word formation gives a hosting for each spine, and whether its hostings obey the
constraint is a theorem about the account, stated with it.

## References

* [travis-1984]
* [svenonius-2016]
* [brody-2000]
-/

@[expose] public section

namespace HMC

variable {H : Type*}

/-- A hosting obeys the Head Movement Constraint when the positions pronounced at any one head
form a stretch of the spine. -/
def Holds (h : List H) : Prop := IsContiguous h.get

instance [DecidableEq H] (h : List H) : Decidable (Holds h) :=
  inferInstanceAs (Decidable (IsContiguous _))

theorem holds_iff_exists_monotone (h : List H) :
    Holds h ↔ ∃ g : Fin h.length → ℕ, Monotone g ∧ ∀ i j, h.get i = h.get j ↔ g i = g j :=
  isContiguous_iff_exists_monotone _

theorem holds_nil : Holds ([] : List H) := fun i ↦ i.elim0

theorem holds_flatMap_replicate {l : List (ℕ × H)} (hl : (l.map Prod.snd).Nodup) :
    Holds (l.flatMap fun p ↦ List.replicate p.1 p.2) :=
  List.isContiguous_get_flatMap_replicate hl

theorem not_holds_of_ne {a b : H} (hab : a ≠ b) : ¬ Holds [a, b, a] := fun h ↦
  hab (@h (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (Fin.zero_le _) (Fin.le_of_lt (by simp)) rfl)

end HMC
