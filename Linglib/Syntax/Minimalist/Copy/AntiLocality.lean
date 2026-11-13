/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain

/-!
# Anti-locality

Anti-locality bars movement that is too short. Abels's version bars the complement of a head
from moving to a specifier of the head's phrase, a `CompToSpec` link; Erlewine's bars a specifier
from moving unless it crosses a maximal projection other than the one it leaves, a `SpecToSpec`
link, a projection being `crossed` when it dominates the phrase that moves but not its landing
site. That Abels's version, with the Phase Impenetrability Condition, leaves the complement of a
phase head no way out is proved in `Phase/Transfer.lean`.

## Implementation notes

* A link pairs the phrase that lands with the position of the lower copy (`Minimalist.links`); the
  phrase that moves is the projection of the lower copy.
* Erlewine restricts his version to Ā-movement. The definitions apply to any link, and an analysis
  picks the links it constrains.

## References

* [abels-2003]
* [erlewine-2016]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree

variable (hd : HeadFunction) (t : PlanarSyntacticObject)

/-- A pronounced head occupies the position. -/
def IsHeadPosition (p : TreePath) : Prop := ∃ x ∈ tokenList t.toRoseTree, x.1 = p

instance (p : TreePath) : Decidable (IsHeadPosition t p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The maximal projections a link crosses, those dominating the phrase that moves but not its
landing site ([erlewine-2016]). -/
def crossed (x : TreePath × TreePath) : Finset TreePath :=
  ((projectionAt hd t x.2).toList.inits.map TreePath.mk).toFinset.filter fun Y ↦
    Y ∈ maximalProjections hd t ∧ x.1.parent < Y ∧ Y < projectionAt hd t x.2

/-- A link moves a specifier, a phrase whose sister is no head, across no maximal projection but
the one it leaves, which [erlewine-2016]'s Spec-to-Spec anti-locality bans. -/
def SpecToSpec (x : TreePath × TreePath) : Prop :=
  projectionAt hd t x.2 ≠ ⊥ ∧ ¬ IsHeadPosition t (complement (projectionAt hd t x.2)) ∧
    (crossed hd t x).card ≤ 1

instance (x : TreePath × TreePath) : Decidable (SpecToSpec hd t x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- No link of any chain moves a specifier across no maximal projection but its own. -/
def ObeysAntiLocality : Prop :=
  ∀ y ∈ tokenList t.toRoseTree, ∀ l ∈ links hd t y.2, ¬ SpecToSpec hd t l

instance : Decidable (ObeysAntiLocality hd t) :=
  inferInstanceAs (Decidable (∀ y ∈ tokenList t.toRoseTree, _))

/-- A link moves the complement of a head to a specifier of the head's phrase, which
[abels-2003]'s anti-locality bans. -/
def CompToSpec (x : TreePath × TreePath) : Prop :=
  IsHeadPosition t (complement (projectionAt hd t x.2)) ∧
    projectionAt hd t (complement (projectionAt hd t x.2)) ≤ x.1.parent

instance (x : TreePath × TreePath) : Decidable (CompToSpec hd t x) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Minimalist
