/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain

/-!
# Spell-out of multidominance

When Merge applies to a term a second time, the linearized object lists that term at each of its
occurrences: a term remerged inside its own root, moved, stands above its lower occurrences, and a
term remerged with another root, shared, stands under mothers none of which dominates another. PF
pronounces each term once, under one of its highest mothers, in Gračanin-Yuksek's sense, those no
other mother of it dominates. A moved term has one highest mother and is pronounced at its highest
occurrence. Accounts differ over which highest mother a shared term is pronounced under: de Vries
takes the one pronounced last, so that right-node raising pronounces shared material in the last
conjunct, and Yip's right dislocation the one pronounced first. The choice is a parameter, a pick
among a term's candidate positions in left-to-right order.

## Main definitions

* `Minimalist.mothers`, `Minimalist.IsHighestMother`: the terms a term is a daughter of, and those
  no other mother of it dominates.
* `Minimalist.spellOutPosition`: the position at which a term is pronounced.
* `Minimalist.remergedYield`: the pronounced tokens, left to right.

## Main statements

* `Minimalist.nodup_remergedYield`: a token is pronounced once at most, whatever the pick.

## Implementation notes

* De Vries's spell-out of remerged nodes, his (56), decides at each visit of a term from which of
  its mothers the traversal has reached, and his algorithm (71) counts a visit that omits a term as
  reaching it, which can pronounce a token twice (`DeVries2009`). Here the choice is made once per
  term, and the term is silent at its other occurrences.
* Each step of the recursion moves from a term to a strictly larger mother, so the height of the
  object bounds it.

## TODO

* Every token is pronounced when the pick chooses among the candidates it is given. With
  `List.getLast?`, on objects in which no mother of a term dominates another, a token is pronounced
  at its last occurrence, so that `remergedYield` is `tokens` there; on objects in which the
  mothers of each term are ordered by dominance it is pronounced at its highest, whatever the pick.
* The conditions that exclude structures from linearization, such as Wilder's restriction of
  shared material to the right edge, as predicates on objects.

## References

* [de-vries-2009]
* [gracanin-yuksek-2013]
* [yip-k-f-2026]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order

variable (pick : List TreePath → Option TreePath) (t : LinearizedSyntacticObject)

/-- The mothers of `s` in `t`: the terms of `t` with `s` as a daughter. -/
def mothers (s : RoseTree Vertex) : List (RoseTree Vertex) :=
  (t.val.subtrees.filter (s ∈ ·.children)).dedup

/-- `m` is a highest mother of `s`: a mother of `s` that no other mother of `s` dominates. -/
def IsHighestMother (s m : RoseTree Vertex) : Prop :=
  s ∈ m.children ∧ ∀ g ∈ mothers t s, ¬ (IsSubtree m g ∧ m ≠ g)

instance (s m : RoseTree Vertex) : Decidable (IsHighestMother t s m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Where `s` is pronounced, within `n` steps of the root: the root at the root, and any other term
at the position `pick` chooses among its occurrences, left to right, under a highest mother
pronounced there. -/
def spellOutPositionAux : ℕ → RoseTree Vertex → Option TreePath
  | 0, _ => none
  | n + 1, s =>
    if s = t.val then some ⊥ else
      pick ((t.val.positionedSubtrees.filter fun x ↦ x.2 = s ∧
          (subtreeAt t.val x.1.parent.toList).any fun m ↦
            decide (IsHighestMother t s m) && spellOutPositionAux n m == some x.1.parent).map
        Prod.fst)

/-- The position at which `s` is pronounced, `none` when `s` is not a term of `t`. -/
def spellOutPosition (s : RoseTree Vertex) : Option TreePath :=
  spellOutPositionAux pick t (t.val.height + 1) s

/-- The pronounced tokens, left to right: each at the position where its leaf is pronounced. -/
def remergedYield : List LexicalItem.Token :=
  (tokenList t.val).filterMap fun x ↦
    if spellOutPosition pick t (.node (.lex x.2) []) = some x.1 then some x.2 else none

/-- A token is pronounced once at most, however many times Merge applied to it. -/
theorem nodup_remergedYield : (remergedYield pick t).Nodup := by
  refine ((nodup_map_fst_positions _ t.val).of_map Prod.fst).filterMap fun x y tok hx hy ↦ ?_
  simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at hx hy
  obtain ⟨hx, rfl⟩ := hx
  obtain ⟨hy, hxy⟩ := hy
  exact Prod.ext (Option.some_injective _ (hx.symm.trans (hxy ▸ hy))) hxy.symm

end Minimalist
