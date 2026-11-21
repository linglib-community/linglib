module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Clause.Basic

/-!
# Clause particles

A clause particle is a word or clitic, not an affix, that goes with a clause as a whole: a question
particle such as Mandarin *ma*, or a modal particle such as German *denn*. This file defines its
lexical record, which gives its morphs, what it is placed by, and a `Clause.Distribution` saying
for each cell whether the particle is obligatory, optional or excluded there. A particle is placed
either in its clause, at the beginning, in second position, at the end or elsewhere, or beside the
focus of the clause, as Turkish *mI* is.

## Main definitions

* `Clause.Placement`: the positions of a particle in its clause.
* `Clause.Particle.Anchor`: placement in the clause or beside the focus.
* `Clause.Particle`: the morphs, anchor and distribution of a clause particle.
* `Clause.Particle.form`, `Clause.Particle.placements`: the written form, and the positions of a
  particle placed in its clause.

## Implementation notes

* A morph is `Morphology.Morph.free` when it is written as a separate word and its source does
  not call it a clitic, so the kind records the source's label and no analysis of the form.
* A particle in second position follows the first word or constituent of its clause. An enclitic
  need not be in second position: one placed after the focus follows whatever the focus is.
* A particle with several placements may stand in any of them, and one with none has no placement
  recorded.

## References

* [dryer-2013-wals]
* [sadock-zwicky-1985]
* [simik-2024]
-/

@[expose] public section

open Morphology (Morph)

namespace Clause

/-- Where a particle stands in its clause. -/
inductive Placement where
  | initial
  /-- After the first word or constituent. -/
  | second
  /-- Neither at an edge nor in second position, as in the German middle field. -/
  | medial
  | final
  deriving DecidableEq, Repr, Fintype

/-- What a particle is placed by: its clause, in any of the given positions, or the focus of the
clause, on the given side of it. -/
inductive Particle.Anchor where
  | clause (placements : Finset Placement)
  | focus (side : Morph.Side)
  deriving DecidableEq

/-- A clause particle of a language. -/
structure Particle where
  /-- The morphs, in order. -/
  morphs : List Morph
  /-- The spelling in the native script. -/
  script : Option String := none
  /-- What the particle is placed by; no placement where the source gives none. -/
  anchor : Particle.Anchor := .clause ∅
  /-- How far the particle is required in each cell; `none` where the source records nothing. -/
  distribution : Distribution := .empty
  deriving DecidableEq

namespace Particle

variable (p : Particle)

/-- The written form, the forms of the morphs separated by spaces. -/
def form : String :=
  match p.morphs.map (·.form) with
  | [] => ""
  | w :: ws => ws.foldl (· ++ " " ++ ·) w

/-- The positions of a particle placed in its clause; none for one placed by the focus. -/
def placements : Finset Placement :=
  match p.anchor with
  | .clause s => s
  | .focus _ => ∅

/-- The side of the focus on which a particle placed by the focus stands. -/
def focusSide? : Option Morph.Side :=
  match p.anchor with
  | .clause _ => none
  | .focus s => some s

end Particle

end Clause
