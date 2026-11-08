/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype

/-!
# Discourse status

The discourse status of a referent is whether the prior discourse has evoked it: a referent is
given, or discourse-old, when it has been evoked, and new otherwise. Discourse status is one of two
kinds of information status, beside hearer status, whether the hearer already knows the referent,
and a discourse-old referent is hearer-old, since hearers remember what they have been told.

## References

* [prince-1992]
-/

@[expose] public section

/-- A referent's discourse status is given when the prior discourse has evoked it and new
otherwise ([prince-1992]). -/
inductive DiscourseStatus where
  /-- The referent is discourse-old. -/
  | given
  /-- The referent is discourse-new. -/
  | new
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace DiscourseStatus

/-- The rank of a discourse status, higher for given. -/
def rank : DiscourseStatus → ℕ
  | .given => 1
  | .new   => 0

/-- `new < given`. -/
instance : LinearOrder DiscourseStatus := LinearOrder.lift' rank (by decide)

/-- `⊥ = new`, `⊤ = given`. -/
instance : BoundedOrder DiscourseStatus where
  top := .given
  le_top := by decide
  bot := .new
  bot_le := by decide

instance : IsSimpleOrder DiscourseStatus where
  exists_pair_ne := ⟨.new, .given, by decide⟩
  eq_bot_or_eq_top := by decide

end DiscourseStatus
