/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Order.Basic
public import Mathlib.Logic.Relator

/-!
# Control: Basic Definitions

A control dependency is a relation `SetRel Pos Pos` on argument positions, read
`antecedent ~[r] dependent`, with a valuation `val : Pos → Ref` assigning referents. This is
Stiebels's definition of control as referential inclusion, "open as to how the control reading
is obtained". The reading types are Landau's: exhaustive, partial and split. Control shift varies
the antecedent across readings of one construction, so it is not a property of a single
dependency. `Mechanism` names what a dependency shares, after Bresnan's cut between functional
and anaphoric control, and `IsSaturating` is the bi-unique, exhaustive profile of saturation
(predication, structure sharing). Grammatical dependencies share Koster's configurational-matrix
format, as Neeleman and van de Koot state it, and its clauses are mathlib vocabulary: refinement
`r ⊆ s`, `Relator.LeftUnique` and `dependent ⊆ r.cod`. Lemmas are in
`Syntax/Control/Basic.lean`.

## Main definitions

* `Control.IsExhaustive`, `Control.IsPartial`, `Control.IsSplit`
* `Control.Mechanism`
* `Control.IsSaturating`

## References

* [stiebels-2007]
* [landau-2000]
* [bresnan-1982]
* [koster-1987]
* [neeleman-vandekoot-2002]
-/

@[expose] public section

namespace Control

open SetRel

variable {Pos Ref : Type*}

/-- A dependency is exhaustive ([landau-2000]) when it relates only co-valued positions, that is,
when it refines the kernel of the valuation. -/
def IsExhaustive (val : Pos → Ref) (ante : SetRel Pos Pos) : Prop :=
  ante ⊆ {(a, b) | val a = val b}

/-- A dependency has a partial reading ([landau-2000]) when some dependent's referent strictly
extends its controller's. -/
def IsPartial [Preorder Ref] (val : Pos → Ref) (d : SetRel Pos Pos) : Prop :=
  ∃ a b, a ~[d] b ∧ val a < val b

/-- A dependency is split when some dependent has two distinct controllers, that is, when it is
not left-unique. -/
abbrev IsSplit (d : SetRel Pos Pos) : Prop :=
  ¬ Relator.LeftUnique (· ~[d] ·)

/-- What a control dependency shares, the cut behind the oppositions of movement and
base generation and of functional and anaphoric control ([bresnan-1982]). -/
inductive Mechanism where
  /-- The occupant assignment itself is shared, as in movement chains and LFG functional
  control. -/
  | occupant
  /-- Only the referents are shared, as in LFG anaphoric control and predication. -/
  | referent
  /-- A binding leg is composed over a predication leg ([landau-2024a]). -/
  | composite
  /-- There is no grammatical dependency, as in non-obligatory control. -/
  | free
  deriving DecidableEq, Repr

/-- The profile of a dependency enforced by saturation (predication, structure sharing): each
dependent has a unique controller, each controller saturates a single slot, and the referent is
shared exhaustively. -/
structure IsSaturating (val : Pos → Ref) (d : SetRel Pos Pos) : Prop where
  biUnique : Relator.BiUnique (· ~[d] ·)
  exhaustive : IsExhaustive val d

end Control
