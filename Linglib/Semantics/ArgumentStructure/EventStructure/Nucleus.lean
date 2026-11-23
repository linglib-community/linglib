module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation

/-!
# The event nucleus

This file defines the nucleus of [moens-steedman-1988]: a preparatory process, the culmination
it brings about, and the consequent state of the culmination. In a model, a nucleus is a path
from a preparation through `cause` to a culmination and through `become` to a state.

## Main definitions

* `EventStructure.Nucleus`: a preparation, a culmination and a consequent state of a model.
* `Nucleus.map`: a nucleus of a model is a nucleus of every model with more relations.

## Main results

* `Nucleus.exists_iff`: an event is the preparation of a nucleus with a `p`-state as its
  consequent state iff it causes a change into a `p`-state.
* `Template.denote_cause_achievement_iff`: a causative of a change of state denotes the
  preparations of the nuclei whose consequent state the root describes.

## Implementation notes

A `Nucleus` is one path in a model. The parts of the nucleus of [moens-steedman-1988] may
themselves be compound; here they are other eventualities of the same model.

## References

* [moens-steedman-1988]
* [rappaport-hovav-levin-1998]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

open ModalLogic
open scoped SetRel

universe u

/-- A nucleus of a model: a preparatory process, the culmination it causes and the consequent
state the culmination gives rise to. -/
structure Nucleus {State Event : Type u} (M : Model State Event) where
  /-- The preparatory process. -/
  preparation : Event
  /-- The culmination. -/
  culmination : Event
  /-- The consequent state. -/
  consequent : State
  /-- The preparation causes the culmination. -/
  cause : preparation ~[M.cause] culmination
  /-- The culmination gives rise to the consequent state. -/
  become : culmination ~[M.become] consequent

namespace Nucleus

variable {State Event : Type u} {M N : Model State Event}

/-- A nucleus of a model is a nucleus of every model with more relations. -/
def map (h : M ≤ N) (n : Nucleus M) : Nucleus N :=
  { n with cause := h.2.1 n.cause, become := h.1 n.become }

@[simp] theorem map_preparation (h : M ≤ N) (n : Nucleus M) :
    (n.map h).preparation = n.preparation := rfl

@[simp] theorem map_culmination (h : M ≤ N) (n : Nucleus M) :
    (n.map h).culmination = n.culmination := rfl

@[simp] theorem map_consequent (h : M ≤ N) (n : Nucleus M) :
    (n.map h).consequent = n.consequent := rfl

/-- An eventuality is the preparation of a nucleus with a `p`-state as its consequent state iff
it causes a change into a `p`-state. -/
theorem exists_iff {p : State → Prop} {v : Event} :
    (∃ n : Nucleus M, n.preparation = v ∧ p n.consequent) ↔ ◇[M.cause] (◇[M.become] p) v :=
  ⟨fun ⟨n, hv, hp⟩ ↦ hv ▸ ⟨_, n.cause, _, n.become, hp⟩,
    fun ⟨e, hc, s, hb, hp⟩ ↦ ⟨⟨v, e, s, hc, hb⟩, rfl, hp⟩⟩

end Nucleus

namespace Template

variable {Entity : Type*} {State Event : Type u} {M : Model State Event}
  {θ : Entity → Event → Prop} {P : Entity → State → Prop} {Q : Event → Prop} {y x : Entity}
  {v : Event}

/-- A causative of a change of state denotes the preparations of the nuclei whose consequent
state the root describes, of which its causing subevent holds. -/
theorem denote_cause_achievement_iff {c : Template .event} :
    (cause c achievement).denote M θ P Q y x v ↔
      c.denote M θ P Q y x v ∧ ∃ n : Nucleus M, n.preparation = v ∧ P x n.consequent :=
  and_congr_right fun _ ↦ Nucleus.exists_iff.symm

/-- Dropping the culmination of the accomplishment leaves its preparatory process. -/
@[simp] theorem causing_accomplishment : accomplishment.causing = some act := rfl

/-- Dropping the preparation of the accomplishment leaves its culmination. -/
@[simp] theorem caused_accomplishment : accomplishment.caused = some achievement := rfl

end Template

end ArgumentStructure.EventStructure
