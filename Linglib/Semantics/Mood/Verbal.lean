/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Mood.Defs
public import Linglib.Semantics.Mood.State

/-!
# Verbal mood as component selection

Verbal mood is the contrast between indicative and subjunctive in complement clauses. On the
comparison-based theory the subjunctive marks a clause whose embedding attitude ranks worlds by
an ordering. Portner states it as two principles (p. 235): a clause operated on by the
informational modal is indicative, and a clause operated on by the preference modal is
subjunctive. Portner and Rubinstein refine the subjunctive's force to local necessity, truth
throughout a branch of the ordering, which lets an agent want incompatible things and agrees
with the preference modal when the context set has a most normal world. Here the indicative is
simple necessity over the context set, the Truth intuition of Farkas and of Portner's earlier
work, and the subjunctive local necessity under the ordering, the Comparison intuition of
Giorgi and Pianesi.

Portner leaves question-embedding predicates open (p. 237): Italian *chiedere* takes the
indicative when it means 'ask' and the subjunctive when it means 'wonder'.

## Main definitions

* `Mood.Grammatical.target`: the component a grammatical mood relates to.
* `Mood.Grammatical.interp`: a grammatical mood interpreted as the force of its component.

## Main statements

* `Mood.Grammatical.interp_iff_boxOn`: with a most normal world in the context set, each mood
  is the necessity modal of its component.
* `Mood.Grammatical.indicative_ne_subjunctive`: the two moods disagree on some state.

## References

* [portner-2018]
* [portner-rubinstein-2020]
* [farkas-1985]
* [portner-1997]
* [giorgi-pianesi-1997]
-/

@[expose] public section

namespace Mood

open DynamicSemantics

variable {W : Type*}

namespace Grammatical

/-- The indicative targets the informational component and the subjunctive the preferential
one. -/
def target : Grammatical → Component
  | .indicative  => .informational
  | .subjunctive => .preferential

@[simp] theorem target_indicative : indicative.target = .informational := rfl

@[simp] theorem target_subjunctive : subjunctive.target = .preferential := rfl

/-- The indicative is simple necessity over the context set and the subjunctive is local
necessity, good possibility under the ordering. -/
def interp : Grammatical → OrderedInformationState W → (W → Prop) → Prop
  | .indicative, σ, p => σ.boxCs p
  | .subjunctive, σ, p => OrderingSemantics.IsGoodPossibility σ.order σ.info {v | p v}

@[simp] theorem interp_indicative (σ : OrderedInformationState W) (p : W → Prop) :
    indicative.interp σ p = σ.boxCs p := rfl

@[simp] theorem interp_subjunctive (σ : OrderedInformationState W) (p : W → Prop) :
    subjunctive.interp σ p = OrderingSemantics.IsGoodPossibility σ.order σ.info {v | p v} := rfl

/-- When the context set has a world at least as normal as all of its worlds, each mood is the
necessity modal of the component it targets. Without one they come apart, as when two
incomparable optimal worlds each make a different proposition locally necessary. -/
theorem interp_iff_boxOn {c : State W} {b : W} (hb : b ∈ c.info)
    (hleast : ∀ v ∈ c.info, c.order.le b v) (m : Grammatical) (p : W → Prop) :
    m.interp c.toOrderedInformationState p ↔ m.target.boxOn c p := by
  cases m
  · exact Iff.rfl
  · exact (OrderingSemantics.isGoodPossibility_iff_of_least hb hleast).trans
      (OrderingSemantics.minimals_subset_iff_of_least hb hleast).symm

/-- Every world is in the context set, and `false`, the one `sepProp`-world, is the one optimal
world. -/
def sepState : OrderedInformationState Bool := ⟨Set.univ, .ofCriterion State.sepProp⟩

/-- The indicative and the subjunctive disagree on some state and proposition. -/
theorem indicative_ne_subjunctive : ∃ (σ : OrderedInformationState Bool) (p : Bool → Prop),
    subjunctive.interp σ p ∧ ¬ indicative.interp σ p :=
  ⟨sepState, State.sepProp, ⟨false, Set.mem_univ false, fun _ _ hv ↦ hv rfl⟩,
    fun h ↦ Bool.noConfusion (h true (Set.mem_univ true))⟩

theorem target_injective : Function.Injective target := by decide

end Grammatical

end Mood
