/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# Projection on planar syntactic objects

The theories of headedness differ in which daughter of a phrase projects, so the head daughter, by
its index at each position of each object, is a parameter, and the projections of
`Syntax/Projection/GornAddress.lean` follow from it: the maximal projections, the maximal
projection of a position, and the lexical head of the phrase there. Whatever reads projection
takes the head daughters its analysis assumes.

## Main definitions

* `Minimalist.HeadDaughter`: the head daughter at each position of each planar object.
* `Minimalist.HeadDaughter.ofProjects`: the head daughters a projection relation on objects gives.
* `Minimalist.maximalProjections`, `Minimalist.projectionAt`, `Minimalist.lexicalHeadAt`.

## References

* [chomsky-1995]
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

open PhraseStructure

/-- The head daughter at each position of a planar syntactic object, by its index, `none` where no
daughter projects. -/
abbrev HeadDaughter := PlanarSyntacticObject TokenLeaf → GornAddress → Option ℕ

variable (hd : HeadDaughter) (t : PlanarSyntacticObject TokenLeaf)

/-- The maximal projections of a planar object, the positions that are no position's head
daughter. -/
def maximalProjections : Set GornAddress := {x | IsMaximalProjection (headDaughterRel (hd t)) x}

instance : DecidablePred (· ∈ maximalProjections hd t) :=
  fun x ↦ inferInstanceAs (Decidable (IsMaximalProjection (headDaughterRel (hd t)) x))

theorem maximalProjections_eq :
    maximalProjections hd t = PhraseStructure.maximalProjections (headDaughterRel (hd t)) ⊥ :=
  PhraseStructure.maximalProjections_bot.symm

/-- The maximal projection of the position `p`, the highest position reached from `p` by climbing
while the position is the head daughter of its mother. -/
def projectionAt (p : GornAddress) : GornAddress := maximalProjectionAt (hd t) p

theorem projectionAt_le (p : GornAddress) : projectionAt hd t p ≤ p := maximalProjectionAt_le _ p

/-- The lexical head of the phrase at `p`, reached by descending through head daughters. -/
def lexicalHeadAt (p : GornAddress) : GornAddress :=
  (fun q ↦ (hd t q).elim q (q * .of ·))^[t.toRoseTree.subtrees.length] p

/-! ### The head daughters of a projection relation -/

/-- The head daughter of the subtree at an address of a planar object, where `P x y` says that the
object `x` projects over `y`: of the two daughters there, the one that projects. -/
def headDaughterAt {L ι : Type}
    (P : SyntacticObject (SyntacticObject.Leaf L ι) → SyntacticObject (SyntacticObject.Leaf L ι) →
    Prop)
    [DecidableRel P] : PlanarSyntacticObject (SyntacticObject.Leaf L ι) → List ℕ → Option ℕ
  | .mul l r, [] => if P l r then some 0 else if P r l then some 1 else none
  | .mul l _, 0 :: q => headDaughterAt P l q
  | .mul _ r, 1 :: q => headDaughterAt P r q
  | _, _ => none

/-- The head daughters a projection relation on objects gives: at each position, the daughter
that projects over its sister. -/
def HeadDaughter.ofProjects (P : SyntacticObject TokenLeaf → SyntacticObject TokenLeaf → Prop)
    [DecidableRel P] :
    HeadDaughter :=
  fun t q ↦ headDaughterAt P t q.toList

end Minimalist
