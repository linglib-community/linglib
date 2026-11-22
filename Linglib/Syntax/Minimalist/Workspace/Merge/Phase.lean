/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Merge.Restrict
public import Linglib.Syntax.Minimalist.Phase.Basic

/-!
# The phase coproduct

Marcolli, Chomsky and Berwick read Phase Theory as a restriction of the coproduct: their phase
coproduct (Definition 1.14.5) extracts the accessible terms that are not in the interior of a lower
phase. `phaseCuts Φ cuts` is that restriction of a cut enumeration, with `Φ` the phase heads, to
the terms that are not `SyntacticObject.Inaccessible`, and the unit stage of Internal Merge at it
vanishes on an inaccessible mover (`mergeOpUnitOfCuts_phaseCuts_eq_zero`).

## TODO

* The phase coproduct is coassociative (their Lemma 1.14.6), its terms being those of the trace
  coproduct on the tree whose lower phase interiors are cut off.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open RoseTree UnorderedTree ConnesKreimer SyntacticObject

variable {R : Type*} [CommSemiring R] {Φ : LexicalItem.Token → Prop} [DecidablePred Φ]
  {cuts : UnorderedTree Vertex → Multiset (Forest (UnorderedTree Vertex) × UnorderedTree Vertex)}

/-- The cuts of the phase coproduct, with `Φ` the phase heads: those of `cuts` that extract no term
in the interior of a lower phase. -/
abbrev phaseCuts (Φ : LexicalItem.Token → Prop) [DecidablePred Φ]
    (cuts : UnorderedTree Vertex →
      Multiset (Forest (UnorderedTree Vertex) × UnorderedTree Vertex)) :
    UnorderedTree Vertex → Multiset (Forest (UnorderedTree Vertex) × UnorderedTree Vertex) :=
  restrictCutsOf (fun T x ↦ ¬ T.Inaccessible Φ x) cuts

/-- The unit stage of Internal Merge at the phase coproduct vanishes on an inaccessible mover: a
term in the interior of a lower phase does not move. -/
theorem mergeOpUnitOfCuts_phaseCuts_eq_zero {T x : SyntacticObject} (hne : T ≠ x)
    (h : T.Inaccessible Φ x) :
    mergeOpUnitOfCuts (R := R) (phaseCuts Φ cuts) x.toUnorderedTree (of' {T.toUnorderedTree}) = 0 :=
  mergeOpUnitOfCuts_restrictCutsOf_eq_zero hne (not_not.2 h)

end Minimalist.Merge
