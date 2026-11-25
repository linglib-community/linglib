/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Replay
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Freezing

A constituent that has moved is an island for later extraction, though it may itself move again.
This is the Freezing condition, and it is what makes VP-raising analyses of VOS order testable,
since whatever a raised VP still contains cannot be extracted and whatever left it before it
raised can. `Frozen d x` says that `x` sits inside some mover of `d`, and `ObeysFreezing d` that
[no step moves a constituent that the mover of an earlier step
contains](##Minimalist.Derivation.obeysFreezing_iff_forall_mover?), so that [a further movement
obeys Freezing exactly when its mover is not
frozen](##Minimalist.Derivation.obeysFreezing_append_im_iff). Movers carry the traces of what
evacuated them earlier, not the evacuees, so a remnant freezes nothing that left it.

Its rival lets a moved constituent be extracted from and restricts what may move instead, a
condition `∀ m ∈ d.movedItems, L m` on the movers: with `L` the labeled constituents,
[boskovic-2018]'s generalization that unlabeled elements cannot move.

## References

* [muller-1998]
* [chung-2006]
* [collins-2005]
* [cole-hermon-2008]
* [boskovic-2018]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject

variable {ι : Type} {d : Derivation ι} {steps : List (Step ι)}
  {x : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}

/-- `x` sits inside a constituent `d` has moved. -/
def Frozen (d : Derivation ι) (x : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    Prop :=
  ∃ m ∈ d.movedItems, Contains m x

instance [DecidableEq ι] (d : Derivation ι)
    (x : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    Decidable (d.Frozen x) :=
  inferInstanceAs (Decidable (∃ m ∈ d.movedItems, Contains m x))

/-- Extending a derivation freezes what its new movers contain and nothing else. -/
theorem frozen_append_iff :
    (d.append steps).Frozen x ↔
      d.Frozen x ∨ ∃ m ∈ steps.filterMap Step.mover?, Contains m x := by
  simp [Frozen, movedItems_append, or_and_right, exists_or]

theorem Frozen.append (h : d.Frozen x) : (d.append steps).Frozen x :=
  frozen_append_iff.2 (Or.inl h)

@[simp] theorem frozen_leftward_iff : d.leftward.Frozen x ↔ d.Frozen x := by
  rw [Frozen, Frozen, movedItems_leftward]

/-- A derivation obeys Freezing when no step moves a constituent that an earlier mover
contains. -/
def ObeysFreezing (d : Derivation ι) : Prop :=
  d.movedItems.Pairwise fun m m' ↦ ¬ Contains m m'

instance [DecidableEq ι] (d : Derivation ι) : Decidable d.ObeysFreezing :=
  inferInstanceAs (Decidable (d.movedItems.Pairwise _))

/-- A derivation obeys Freezing exactly when no step moves a constituent that the mover of an
earlier step contains. -/
theorem obeysFreezing_iff_forall_mover? :
    d.ObeysFreezing ↔
      ∀ ⦃i j : ℕ⦄, i < j → ∀ m ∈ d.mover? i, ∀ m' ∈ d.mover? j, ¬ Contains m m' := by
  rw [ObeysFreezing, movedItems, List.pairwise_filterMap, List.pairwise_iff_getElem]
  constructor
  · intro h i j hij m hm m' hm'
    have hj := lt_length_of_mem_mover? hm'
    have hi : i < d.steps.length := hij.trans hj
    rw [mover?, List.getElem?_eq_getElem hi] at hm
    rw [mover?, List.getElem?_eq_getElem hj] at hm'
    exact h i j hi hj hij m hm m' hm'
  · intro h i j hi hj hij m hm m' hm'
    exact h hij m (by rw [mover?, List.getElem?_eq_getElem hi]; exact hm)
      m' (by rw [mover?, List.getElem?_eq_getElem hj]; exact hm')

theorem obeysFreezing_append_iff :
    (d.append steps).ObeysFreezing ↔ d.ObeysFreezing ∧
      (steps.filterMap Step.mover?).Pairwise (fun m m' ↦ ¬ Contains m m') ∧
        ∀ m ∈ steps.filterMap Step.mover?, ¬ d.Frozen m := by
  simp only [ObeysFreezing, movedItems_append, List.pairwise_append, Frozen]
  grind

/-- A further movement obeys Freezing exactly when its mover is not frozen. -/
@[simp] theorem obeysFreezing_append_im_iff
    {m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)} {side : Edge} :
    (d.append [.im m side]).ObeysFreezing ↔ d.ObeysFreezing ∧ ¬ d.Frozen m := by
  simp [obeysFreezing_append_iff]

@[simp] theorem obeysFreezing_append_em_iff
    {item : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)} {side : Edge} :
    (d.append [.em side item]).ObeysFreezing ↔ d.ObeysFreezing := by
  simp [obeysFreezing_append_iff]

/-! ### Relabelling -/

section Map

variable {f : LexicalItem.Token → LexicalItem.Token} {d : Derivation} {x : SyntacticObject}

theorem frozen_map_iff (hf : Function.Injective f) : (d.map f).Frozen (x.map f) ↔ d.Frozen x := by
  simp only [Frozen, movedItems_map, List.mem_map, exists_exists_and_eq_and, contains_map_iff hf]

theorem obeysFreezing_map_iff (hf : Function.Injective f) :
    (d.map f).ObeysFreezing ↔ d.ObeysFreezing := by
  simp only [ObeysFreezing, movedItems_map, List.pairwise_map, contains_map_iff hf]

end Map

end Minimalist.Derivation
