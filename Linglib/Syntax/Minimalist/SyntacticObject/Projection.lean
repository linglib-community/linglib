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
`Syntax/Projection/GornAddress.lean` follow from it. Whatever reads projection takes the head
daughters its analysis assumes.

## Main definitions

* `Minimalist.HeadDaughter`: the head daughter at each position of each planar object.
* `Minimalist.headDaughter`, `Minimalist.HeadDaughter.ofProjects`: the daughter that projects under
  a projection relation on objects, and the head daughters that gives at every position.
* `Minimalist.headPath`: the address of the leaf that heads a planar object.

## References

* [chomsky-1995]
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

open PhraseStructure

variable {α : Type}

/-- The head daughter at each position of a planar syntactic object, by its index, `none` where no
daughter projects. -/
abbrev HeadDaughter (α : Type) := PlanarSyntacticObject α → GornAddress → Option ℕ

/-! ### The head daughters of a projection relation -/

section Projects

variable (P : SyntacticObject α → SyntacticObject α → Prop) [DecidableRel P]

local notation "toSO" => PlanarSyntacticObject.toSyntacticObject

/-- The head daughter of a planar object, where `P x y` says that the object `x` projects over
`y`: of its two daughters, the one that projects. -/
def headDaughter : PlanarSyntacticObject α → Option ℕ
  | .of _ => none
  | .mul l r =>
    if P (toSO l) (toSO r) then some 0
    else if P (toSO r) (toSO l) then some 1 else none

@[simp] theorem headDaughter_of (a : α) : headDaughter P (FreeMagma.of a) = none := rfl

theorem headDaughter_mul (l r : PlanarSyntacticObject α) :
    headDaughter P (l * r) =
      if P (toSO l) (toSO r) then some 0
      else if P (toSO r) (toSO l) then some 1 else none := rfl

/-- The head daughters a projection relation on objects gives: at each position, the daughter
that projects over its sister. -/
def HeadDaughter.ofProjects : HeadDaughter α :=
  fun t q ↦ (t.subAt? q.toList).bind (headDaughter P)

/-- The address of the leaf that heads a planar object: from the root, the daughter that projects,
down to a leaf, and `none` where neither daughter of a Merge on the way projects. -/
def headPath : PlanarSyntacticObject α → Option (List ℕ)
  | .of _ => some []
  | .mul l r =>
    if P (toSO l) (toSO r) then (headPath l).map (0 :: ·)
    else if P (toSO r) (toSO l) then (headPath r).map (1 :: ·) else none

@[simp] theorem headPath_of (a : α) : headPath P (FreeMagma.of a) = some [] := rfl

theorem headPath_mul (l r : PlanarSyntacticObject α) :
    headPath P (l * r) =
      if P (toSO l) (toSO r) then (headPath P l).map (0 :: ·)
      else if P (toSO r) (toSO l) then (headPath P r).map (1 :: ·)
      else none := rfl

/-- The head path of a Merge starts at its head daughter. -/
theorem head?_headPath_mul {l r : PlanarSyntacticObject α} {q : List ℕ}
    (h : headPath P (l * r) = some q) : q.head? = headDaughter P (l * r) := by
  rw [headPath_mul] at h
  rw [headDaughter_mul]
  split_ifs at h ⊢
  · obtain ⟨q', -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · obtain ⟨q', -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl

end Projects

end Minimalist
