/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.WordOrder

/-!
# Agreement with conjoined noun phrases

A target whose controller consists of conjoined noun phrases agrees with one of them or with all
of them. This file defines the options, `Agreement.ConjunctAgreement`: agreement with the conjunct
at an edge `e` of the coordination, `single e`, and agreement with all conjuncts, `all`. For the
conjuncts `cs` in linear order, `a.conjuncts cs` lists the conjuncts whose features the option `a`
gives the target access to, `e.takeAt 1 cs` for `single e` and `cs` for `all`. Agreement with the
first conjunct is `single .left`, agreement with the last is `single .right`, and agreement with
the conjunct nearest a target on side `d` of the conjuncts is `single d.headEdge`, which is
agreement with the first when the target precedes them. A head that checks its selectional
features against coordinated arguments has the same options.

The conjuncts an option selects stand together in the coordination
(`Agreement.ConjunctAgreement.conjuncts_infix`) and are selected by their position alone, so
selection commutes with any reading of the conjuncts
(`Agreement.ConjunctAgreement.conjuncts_map`), and distinct options select different conjuncts of
some coordination (`Agreement.ConjunctAgreement.conjuncts_injective`). The mirror image of an
option, `Agreement.ConjunctAgreement.swap`, selects from the reversed coordination what the option
selects (`Agreement.ConjunctAgreement.revConj_conjuncts`).

## Implementation notes

* The side of the conjuncts the target is on is a `HeadDirection`, the target counting as the
  head, so a verb before its conjoined subject is head-initial.
* An option says which conjuncts the target accesses, not how its values are computed from
  theirs: agreement with one conjunct takes that conjunct's values, agreement with all resolves
  them (`Agreement.ResolutionRule`).
* The first conjunct is first in linear order; whether an analysis picks it for its position or
  as the structurally highest conjunct is left to the analysis.
* Agreement with the last conjunct is an option whether or not the target follows the conjuncts,
  so that the options are closed under mirror image. A target that precedes the conjuncts is not
  reported to agree with the last, to it the more distant; a study states that restriction on
  the options it admits.

## References

* [corbett-2000]
* [corbett-1991]
* [bruening-alkhalaf-2020]
-/

@[expose] public section

namespace Agreement

/-- A target agrees with conjoined noun phrases by agreeing with one conjunct, the first or the
last, or with all of them. -/
inductive ConjunctAgreement where
  /-- Agreement with the conjunct at the edge `e` of the coordination. -/
  | single (e : Edge)
  /-- Agreement with all conjuncts, by resolution. -/
  | all
  deriving DecidableEq, Fintype, Repr

namespace ConjunctAgreement

variable {α β : Type*} {a : ConjunctAgreement} {d : HeadDirection} {e : Edge} {cs l : List α}
  {x : α}

/-- Agreement with the first conjunct. -/
def first : ConjunctAgreement := single .left

/-- Agreement with the last conjunct. -/
def last : ConjunctAgreement := single .right

/-- Agreement with the conjunct nearest a target on side `d` of the conjuncts. -/
def nearest (d : HeadDirection) : ConjunctAgreement := single d.headEdge

@[simp] theorem nearest_headInitial : nearest .headInitial = first := rfl

@[simp] theorem nearest_headFinal : nearest .headFinal = last := rfl

/-- The mirror image of an option exchanges the first conjunct and the last. -/
def swap : ConjunctAgreement → ConjunctAgreement
  | single e => single e.swap
  | all => all

@[simp] theorem swap_single : (single e).swap = single e.swap := rfl

@[simp] theorem swap_all : all.swap = all := rfl

@[simp] theorem swap_first : first.swap = last := rfl

@[simp] theorem swap_last : last.swap = first := rfl

@[simp] theorem swap_nearest (d : HeadDirection) : (nearest d).swap = nearest d.swap := by
  simp [nearest]

@[simp] theorem swap_swap : ∀ a : ConjunctAgreement, a.swap.swap = a := by decide

theorem swap_involutive : Function.Involutive swap := swap_swap

/-! ### The conjuncts an option selects -/

/-- `a.conjuncts cs` lists the conjuncts, of the conjuncts `cs` in linear order, whose features a
target accesses when it agrees by the option `a`. -/
def conjuncts : ConjunctAgreement → List α → List α
  | single e, cs => e.takeAt 1 cs
  | all, cs => cs

@[simp] theorem conjuncts_single : (single e).conjuncts cs = e.takeAt 1 cs := rfl

@[simp] theorem conjuncts_all : all.conjuncts cs = cs := rfl

@[simp] theorem conjuncts_first : first.conjuncts cs = cs.take 1 := rfl

@[simp] theorem conjuncts_last : last.conjuncts cs = cs.rtake 1 := rfl

@[simp] theorem conjuncts_nearest : (nearest d).conjuncts cs = d.headEdge.takeAt 1 cs := rfl

/-- The conjuncts an option selects stand together in the coordination. -/
theorem conjuncts_infix (a : ConjunctAgreement) (cs : List α) : a.conjuncts cs <:+: cs := by
  cases a
  exacts [Edge.takeAt_infix .., List.infix_rfl]

/-- An option selects conjuncts by their position, so selecting commutes with reading each
conjunct through `f`. -/
theorem conjuncts_map (f : α → β) (a : ConjunctAgreement) (cs : List α) :
    a.conjuncts (cs.map f) = (a.conjuncts cs).map f := by
  cases a
  exacts [Edge.takeAt_map .., rfl]

/-- Distinct options select different conjuncts of some coordination. -/
theorem conjuncts_injective [Nontrivial α] :
    Function.Injective (conjuncts (α := α)) := fun a b h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  have := congrFun h [x, y]
  rcases a with (_ | _) | _ <;> rcases b with (_ | _) | _ <;> simp_all [List.rtake]

/-- The mirror image of an option selects from the reversed coordination what the option
selects. -/
theorem revConj_conjuncts (a : ConjunctAgreement) :
    List.revConj a.conjuncts = a.swap.conjuncts (α := α) := by
  funext cs
  cases a <;> simp [List.revConj, Edge.takeAt_reverse]

/-- Only agreement with the last conjunct selects the last of several conjuncts alone. -/
theorem conjuncts_concat_eq_singleton_iff (hl : l ≠ []) (hx : x ∉ l) :
    a.conjuncts (l ++ [x]) = [x] ↔ a = last := by
  obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  have hy : y ≠ x := fun h ↦ hx (h ▸ List.mem_cons_self)
  rcases a with (_ | _) | _ <;> simp [hy, last, List.rtake_eq_reverse_take_reverse]

end ConjunctAgreement

end Agreement
