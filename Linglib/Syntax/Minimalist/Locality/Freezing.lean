/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Freezing

A constituent that has moved is an island for later extraction, though it may itself move again.
This is the Freezing condition, and it is what makes VP-raising analyses of VOS order testable,
since whatever a raised VP still contains cannot be extracted and whatever left it before it
raised can. `Frozen d x` says that `x` sits inside some
mover of `d`, and `ObeysFreezing d` that no mover of `d` sits inside an earlier one, a pairwise
condition on the list of movers in the shape of `List.Nodup`. Movers carry the traces of what
evacuated them earlier, not the evacuees, so a remnant freezes nothing that left it.

## Main definitions

* `Minimalist.Derivation.Frozen`, `Minimalist.Derivation.ObeysFreezing`

## Main results

* `Minimalist.Derivation.frozen_append_iff`: extending a derivation freezes what its new movers
  contain and nothing else.
* `Minimalist.Derivation.obeysFreezing_append_im_iff`: a further movement obeys Freezing exactly
  when its mover is not frozen.

## References

* [muller-1998]
* [chung-2006]
* [collins-2005]
* [cole-hermon-2008]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject

variable {d : Derivation} {steps : List Step} {x : SyntacticObject}

/-- `x` sits inside a constituent `d` has moved. -/
def Frozen (d : Derivation) (x : SyntacticObject) : Prop := ∃ m ∈ d.movedItems, Contains m x

instance (d : Derivation) (x : SyntacticObject) : Decidable (d.Frozen x) :=
  inferInstanceAs (Decidable (∃ m ∈ d.movedItems, Contains m x))

/-- Extending a derivation freezes what its new movers contain and nothing else. -/
theorem frozen_append_iff :
    (d.append steps).Frozen x ↔
      d.Frozen x ∨ ∃ m ∈ steps.filterMap Step.mover?, Contains m x := by
  simp [Frozen, movedItems_append, or_and_right, exists_or]

/-- Freezing is monotone under extension. -/
theorem Frozen.append (h : d.Frozen x) : (d.append steps).Frozen x :=
  frozen_append_iff.2 (Or.inl h)

/-- Freezing is blind to the sides of External Merge. -/
@[simp] theorem frozen_leftward_iff : d.leftward.Frozen x ↔ d.Frozen x := by
  rw [Frozen, Frozen, movedItems_leftward]

/-- A derivation obeys Freezing when no step moves a constituent that an earlier mover
contains. -/
def ObeysFreezing (d : Derivation) : Prop :=
  d.movedItems.Pairwise fun m m' ↦ ¬ Contains m m'

instance (d : Derivation) : Decidable d.ObeysFreezing :=
  inferInstanceAs (Decidable (d.movedItems.Pairwise _))

theorem obeysFreezing_append_iff :
    (d.append steps).ObeysFreezing ↔ d.ObeysFreezing ∧
      (steps.filterMap Step.mover?).Pairwise (fun m m' ↦ ¬ Contains m m') ∧
        ∀ m ∈ steps.filterMap Step.mover?, ¬ d.Frozen m := by
  simp only [ObeysFreezing, movedItems_append, List.pairwise_append, Frozen]
  grind

/-- A further movement obeys Freezing exactly when its mover is not frozen. -/
@[simp] theorem obeysFreezing_append_im_iff {m : SyntacticObject} {side : Edge} :
    (d.append [.im m side]).ObeysFreezing ↔ d.ObeysFreezing ∧ ¬ d.Frozen m := by
  simp [obeysFreezing_append_iff]

/-- A further External Merge obeys Freezing exactly when the derivation does. -/
@[simp] theorem obeysFreezing_append_em_iff {item : LinearizedSyntacticObject} {side : Edge} :
    (d.append [.em side item]).ObeysFreezing ↔ d.ObeysFreezing := by
  simp [obeysFreezing_append_iff]

end Minimalist.Derivation
