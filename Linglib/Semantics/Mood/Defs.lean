/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical mood

This file defines grammatical mood, the indicative or subjunctive morphology of the verb, which
[portner-2018] calls verbal mood. Verbal mood is distinct from sentence mood, the declarative,
interrogative or imperative character of a root clause, in form and in meaning, though the two are
closely related; and both are distinct from reality status, the realis and irrealis marking of
typological description, whose relation to verbal mood is not understood.

## Main declarations

* `Mood.Grammatical`: the indicative and the subjunctive.

## References

* [portner-2018]
-/

@[expose] public section

namespace Mood

/-- Grammatical (verbal) mood. -/
inductive Grammatical where
  /-- The mood of a clause interpreted against a designated set of worlds. -/
  | indicative
  /-- The mood of a clause interpreted against a comparison of worlds. -/
  | subjunctive
  deriving DecidableEq, Repr, Inhabited, Fintype

end Mood
