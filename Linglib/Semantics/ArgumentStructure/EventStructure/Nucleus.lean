module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation

/-!
# The event nucleus

A nucleus is a preparatory process, the culmination it brings about and the consequent state
that ensues ([moens-steedman-1988]). In a model of the event-structure primitives it is a path
`v ~[cause] e ~[become] s`: `Nucleus M` bundles the three eventualities with the two steps.

An eventuality is the preparation of a nucleus whose consequent state satisfies `p` exactly when
it causes a change into a `p`-state, `◇[cause] (◇[become] p)` (`Nucleus.exists_iff`). A causative
of a change of state therefore denotes the preparations of the nuclei whose consequent state the
root describes, whatever its causing subevent (`Template.denote_cause_achievement_iff`), and the
accomplishment those that are actions of the root's manner. The two subterm maps of a causative
strip a part of the nucleus: `Template.causing` keeps the preparation and drops the culmination,
and `Template.caused` keeps the culmination and its consequent state and drops the preparation.

## Implementation notes

The source's nucleus is a piece of knowledge representation whose parts may each be compound. A
`Nucleus` here is one path of a model, and compound parts are other eventualities of the same
model. A state is the consequent state of no nucleus unless a change gives rise to it, so a
template with no `BECOME` describes no culmination.

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
