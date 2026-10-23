/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Freezing

A constituent that has moved is an island for later extraction, though it may itself move again.
This is the Freezing condition, and it is what makes VP-raising analyses of VOS order testable,
since whatever a raised VP still contains cannot be extracted and whatever left it before it
raised can. `Frozen d x` says that `x` sits inside some
mover of `d`, and `ObeysFreezing d` that no mover of `d` sits inside an earlier one, a pairwise
condition on the list of movers in the shape of `List.Nodup`. Movers carry the traces of what
evacuated them earlier, not the evacuees, so a remnant freezes nothing that left it. Its rival, the
Unlabeled Immobility Condition, lets a moved constituent be extracted from and instead bars a
constituent from moving when it is unlabeled in the object built so far, as a phrase whose specifier
does not agree with it is.

## Main definitions

* `Minimalist.Derivation.Frozen`, `Minimalist.Derivation.ObeysFreezing`
* `Minimalist.Derivation.ObeysUIC`: every mover is labeled when it moves.

## Main results

* `Minimalist.Derivation.frozen_append_iff`: extending a derivation freezes what its new movers
  contain and nothing else.
* `Minimalist.Derivation.obeysFreezing_append_im_iff`: a further movement obeys Freezing exactly
  when its mover is not frozen.
* `Minimalist.Derivation.obeysUIC_append_im_iff`: a further movement obeys the Unlabeled
  Immobility Condition exactly when its mover is labeled.

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

theorem Frozen.append (h : d.Frozen x) : (d.append steps).Frozen x :=
  frozen_append_iff.2 (Or.inl h)

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

@[simp] theorem obeysFreezing_append_em_iff {item : LinearizedSyntacticObject} {side : Edge} :
    (d.append [.em side item]).ObeysFreezing ↔ d.ObeysFreezing := by
  simp [obeysFreezing_append_iff]

/-! ### Unlabeled immobility -/

variable (L : LinearizedSyntacticObject → SyntacticObject → Prop)

/-- [boskovic-2018]'s Unlabeled Immobility Condition: each mover of `d` is labeled, as `L` reads
labels, in the object the derivation has built when it moves. -/
def ObeysUIC (d : Derivation) : Prop :=
  ∀ i < d.length, ∀ m ∈ d.mover? i, ∃ p ∈ (d.take i).externalize?, L p m

instance [∀ p, DecidablePred (L p)] (d : Derivation) : Decidable (d.ObeysUIC L) :=
  inferInstanceAs (Decidable (∀ _ < _, _))

variable {L}

theorem ObeysUIC.mono {L' : LinearizedSyntacticObject → SyntacticObject → Prop}
    (hL : ∀ p x, L p x → L' p x) (h : d.ObeysUIC L) : d.ObeysUIC L' :=
  fun i hi m hm ↦ (h i hi m hm).imp fun p ⟨hp, hpm⟩ ↦ ⟨hp, hL p m hpm⟩

theorem obeysUIC_append_singleton_iff {step : Step} :
    (d.append [step]).ObeysUIC L ↔ d.ObeysUIC L ∧
      ∀ m ∈ step.mover?, ∃ p ∈ d.externalize?, L p m := by
  have hlast : (d.append [step]).mover? d.length = step.mover? := by
    simp [mover?, append, length]
  constructor
  · intro h
    refine ⟨fun i hi m hm ↦ ?_, fun m hm ↦ ?_⟩
    · have := h i (by simp; omega) m (by rwa [mover?_append_of_lt hi])
      rwa [take_append_of_le hi.le] at this
    · have := h d.length (by simp) m (by rwa [hlast])
      rwa [take_length_append] at this
  · rintro ⟨h, hs⟩ i hi m hm
    rcases Nat.lt_or_ge i d.length with hlt | hge
    · rw [take_append_of_le hlt.le]
      exact h i hlt m (by rwa [mover?_append_of_lt hlt] at hm)
    · obtain rfl : i = d.length := by simp at hi; omega
      rw [take_length_append]
      exact hs m (by rwa [hlast] at hm)

/-- A further movement obeys the Unlabeled Immobility Condition exactly when its mover is labeled
in the object built so far. -/
@[simp] theorem obeysUIC_append_im_iff {m : SyntacticObject} {side : Edge} :
    (d.append [.im m side]).ObeysUIC L ↔ d.ObeysUIC L ∧ ∃ p ∈ d.externalize?, L p m := by
  simp [obeysUIC_append_singleton_iff]

@[simp] theorem obeysUIC_append_em_iff {item : LinearizedSyntacticObject} {side : Edge} :
    (d.append [.em side item]).ObeysUIC L ↔ d.ObeysUIC L := by
  simp [obeysUIC_append_singleton_iff]

end Minimalist.Derivation
