/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Position

/-!
# Projection on linearized syntactic objects

The theories of headedness differ in which daughter of a phrase projects, so a head function, the
index of the head daughter at each position of each object, is a parameter, and the projections of
`Syntax/Projection.lean` follow from it: the maximal projections, the maximal projection of a
position, and the lexical head of the phrase there. Whatever reads projection takes the head
function its analysis assumes.

## Main definitions

* `Minimalist.HeadFunction`: the head daughter at each position of each linearized object.
* `Minimalist.maximalProjections`, `Minimalist.projectionAt`, `Minimalist.lexicalHeadAt`.

## References

* [chomsky-1995]
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

open Core.Order PhraseStructure

/-- A head function gives, at each position of a linearized syntactic object, the index of its head
daughter, `none` where no daughter projects. -/
abbrev HeadFunction := LinearizedSyntacticObject → TreePath → Option ℕ

variable (hd : HeadFunction) (t : LinearizedSyntacticObject)

/-- The maximal projections of a linearized object, the positions that are no position's head
daughter. -/
def maximalProjections : Set TreePath := {x | IsMaximalProjection (headDaughterRel (hd t)) x}

instance : DecidablePred (· ∈ maximalProjections hd t) :=
  fun x ↦ inferInstanceAs (Decidable (IsMaximalProjection (headDaughterRel (hd t)) x))

theorem maximalProjections_eq :
    maximalProjections hd t = PhraseStructure.maximalProjections (headDaughterRel (hd t)) ⊥ :=
  PhraseStructure.maximalProjections_bot.symm

/-- The maximal projection of the position `p`, the highest position reached from `p` by climbing
while the position is the head daughter of its mother. -/
def projectionAt (p : TreePath) : TreePath := maximalProjectionAt (hd t) p

theorem projectionAt_le (p : TreePath) : projectionAt hd t p ≤ p := maximalProjectionAt_le _ p

/-- The lexical head of the phrase at `p`, reached by descending through head daughters. -/
def lexicalHeadAt (p : TreePath) : TreePath :=
  (fun q ↦ (hd t q).elim q fun i ↦ ⟨q.toList ++ [i]⟩)^[t.val.subtrees.length] p

end Minimalist
