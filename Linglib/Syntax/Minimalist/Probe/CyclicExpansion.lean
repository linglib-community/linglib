/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.DropRight
public import Linglib.Syntax.Minimalist.Copy.Chain

/-!
# Cyclic expansion

A probe on a head searches the sister of the head, and as the head projects, the sister of each
projection joins its search space. A probe on v between the arguments therefore meets the internal
argument and then, once v projects over it, the external argument, [bejar-rezac-2009]'s cyclic
expansion, and a probe on T above both meets them in the reverse order. Reading the goals off a
planar object makes that order a consequence of where the head stands, instead of a stipulated
list.

## References

* [bejar-rezac-2009]
-/

@[expose] public section

namespace Minimalist

open Core.Order

variable (hd : HeadFunction) (t : PlanarSyntacticObject)

/-- The projections of the position `a`, from `a` up to its maximal projection. -/
def projectionsOf (a : TreePath) : List TreePath :=
  (List.range (a.toList.length - (projectionAt hd t a).toList.length + 1)).map fun k ↦
    ⟨a.toList.rdrop k⟩

/-- The tokens `P` holds of that a probe on the head at `a` meets in search order: projection by
projection, from the head up, the copies each c-commands outside `cut`, nearest first, a token
counting only where it is first met. -/
def cyclicGoals (P : LexicalItem.Token → Prop) [DecidablePred P] (cut : Set TreePath)
    [DecidablePred (· ∈ cut)] (a : TreePath) : List LexicalItem.Token :=
  ((projectionsOf hd t a).flatMap fun p ↦ (List.range t.val.numNodes).flatMap fun n ↦
    ((positions (Sum.elim id id) t.val).filter fun x ↦
      x.1.toList.length == n && decide (P x.2) && decide (t.val.CCommands p x.1) &&
        decide (x.1 ∉ cut)).map (·.2)).eraseDups

variable {hd t} {P : LexicalItem.Token → Prop} [DecidablePred P] {cut : Set TreePath}
  [DecidablePred (· ∈ cut)] {a : TreePath} {x : LexicalItem.Token}

private theorem length_lt_numNodes {β : Type*} {r s : RoseTree β} {q : List ℕ} (h : r[q]? = some s) :
    q.length < r.numNodes := by
  induction q generalizing r with
  | nil => cases r; simp [RoseTree.numNodes_node]
  | cons i q ih =>
    obtain ⟨c, hc, hcs⟩ := RoseTree.getElem?_cons_eq_some_iff.1 h
    have := RoseTree.numNodes_lt_of_mem (List.mem_of_getElem? hc)
    have := ih hcs
    simp only [List.length_cons]
    omega

/-- A probe meets exactly the tokens with a copy that a projection of its head c-commands, outside
the positions closed to it. -/
theorem mem_cyclicGoals :
    x ∈ cyclicGoals hd t P cut a ↔
      P x ∧ ∃ p ∈ projectionsOf hd t a, ∃ q, (q, x) ∈ positions (Sum.elim id id) t.val ∧
        t.val.CCommands p q ∧ q ∉ cut := by
  simp only [cyclicGoals, List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.mem_range]
  constructor
  · rintro ⟨p, hp, n, -, ⟨q, y⟩, ⟨hm, ⟨⟨-, hPy⟩, hcc⟩, hcut⟩, rfl⟩
    exact ⟨hPy, p, hp, q, hm, hcc, hcut⟩
  · rintro ⟨hPx, p, hp, q, hm, hcc, hcut⟩
    obtain ⟨s, hs, -⟩ := mem_positions_iff.1 hm
    exact ⟨p, hp, q.toList.length, length_lt_numNodes hs, (q, x), ⟨hm, ⟨⟨rfl, hPx⟩, hcc⟩, hcut⟩, rfl⟩

end Minimalist
