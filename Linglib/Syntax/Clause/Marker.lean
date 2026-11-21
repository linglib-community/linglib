module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Clause.Basic

/-!
# Clause markers

A clause marker is a form that goes with a clause as a whole and helps to mark its sentence type or
its use: a question particle such as Mandarin *ma*, a modal particle such as German *denn*, or a
complementizer. This file defines its lexical record, which gives its morphs, what it is placed
by, and a `Clause.Distribution` saying for each cell whether the marker is obligatory, optional or
excluded there. A marker is placed either in its clause, at the beginning, in second position, at
the end or elsewhere, or beside the focus of the clause, as Turkish *mI* is. A particle is a marker
none of whose morphs is an affix; a `Complementizer` is a marker with the properties of the clause
it introduces.

## Main definitions

* `Clause.Placement`: the positions of a marker in its clause.
* `Clause.Marker.Anchor`: placement in the clause or beside the focus.
* `Clause.Marker`: the morphs, anchor and distribution of a clause marker.
* `Clause.Marker.form`, `Clause.Marker.placements`: the written form, and the positions of a
  marker placed in its clause.
* `Clause.Marker.IsParticle`: no morph of the marker is an affix.

## Implementation notes

* A morph is `Morphology.Morph.free` when it is written as a separate word and its source does
  not call it a clitic, so the kind records the source's label and no analysis of the form.
* A marker in second position follows the first word or constituent of its clause. An enclitic
  need not be in second position: one placed after the focus follows whatever the focus is.
* A marker with several placements may stand in any of them, and one with none has no placement
  recorded.

## References

* [dryer-2013-wals]
* [simik-2024]
-/

@[expose] public section

open Morphology (Morph)

namespace Clause

/-- Where a marker stands in its clause. -/
inductive Placement where
  | initial
  /-- After the first word or constituent. -/
  | second
  /-- Neither at an edge nor in second position, as in the German middle field. -/
  | medial
  | final
  deriving DecidableEq, Repr, Fintype

/-- What a marker is placed by: its clause, in any of the given positions, or the focus of the
clause, on the given side of it. -/
inductive Marker.Anchor where
  | clause (placements : Finset Placement)
  | focus (side : Morph.Side)
  deriving DecidableEq

instance : Repr Marker.Anchor where
  reprPrec
    | .clause s, _ => "clause " ++ repr (Placement.enumList.filter (· ∈ s))
    | .focus side, _ => "focus " ++ repr side

/-- A clause marker of a language. -/
structure Marker where
  /-- The morphs, in order. -/
  morphs : List Morph
  /-- The spelling in the native script. -/
  script : Option String := none
  /-- What the marker is placed by; no placement where the source gives none. -/
  anchor : Marker.Anchor := .clause ∅
  /-- How far the marker is required in each cell; `none` where the source records nothing. -/
  distribution : Distribution := .empty
  deriving DecidableEq, Repr

namespace Marker

variable (p : Marker)

/-- The written form, the forms of the morphs separated by spaces. -/
def form : String :=
  match p.morphs.map (·.form) with
  | [] => ""
  | w :: ws => ws.foldl (· ++ " " ++ ·) w

/-- The positions of a marker placed in its clause; none for one placed by the focus. -/
def placements : Finset Placement :=
  match p.anchor with
  | .clause s => s
  | .focus _ => ∅

/-- A particle is a marker none of whose morphs is an affix. -/
def IsParticle : Prop := ∀ m ∈ p.morphs, m.kind.attachment? ≠ some .affix

instance : Decidable p.IsParticle := inferInstanceAs (Decidable (∀ m ∈ p.morphs, _))

end Marker

end Clause
