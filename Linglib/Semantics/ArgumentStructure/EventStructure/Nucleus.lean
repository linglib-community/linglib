module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation

/-!
# The event nucleus

This file defines the nucleus of [moens-steedman-1988]: a preparatory process, the culmination
that completes it, and the consequent state of the culmination. For a relation `C` between a
process and an event that completes it and a relation `B` between an event and a state it gives
rise to, a nucleus is a path through `C` and then `B`.

## Main definitions

* `EventStructure.Nucleus`: a preparation, a culmination and a consequent state, linked by a
  completion relation and a relation of giving rise to a state.
* `Nucleus.map`: a nucleus along two relations is a nucleus along any larger ones.

## Main results

* `Nucleus.exists_iff`: an event is the preparation of a nucleus with a `p`-state as its
  consequent state iff `◇[C] (◇[B] p)` holds of it.
* `Template.denote_cause_achievement_iff`: where completion is causation, a causative of a
  change of state denotes the preparations of the nuclei whose consequent state the root
  describes.

## Implementation notes

* The completion relation is a parameter and not the `cause` of a model. The preparation of the
  source's nucleus is the process by which the culmination is accomplished, a relation of
  contingency, and an analysis may or may not take it to be causation. The templates of
  [rappaport-hovav-levin-1998] do: their accomplishment is a causative.
* A `Nucleus` is one path. The parts of the source's nucleus may themselves be compound; here
  they are other eventualities of the same carrier.

## References

* [moens-steedman-1988]
* [rappaport-hovav-levin-1998]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

open ModalLogic
open scoped SetRel

universe u

/-- A nucleus along a completion relation `C` and a relation `B` of giving rise to a state: a
preparatory process, a culmination that completes it and the consequent state. -/
structure Nucleus {State Event : Type*} (C : SetRel Event Event) (B : SetRel Event State) where
  /-- The preparatory process. -/
  preparation : Event
  /-- The culmination. -/
  culmination : Event
  /-- The consequent state. -/
  consequent : State
  /-- The culmination completes the preparation. -/
  complete : preparation ~[C] culmination
  /-- The culmination gives rise to the consequent state. -/
  become : culmination ~[B] consequent

namespace Nucleus

variable {State Event : Type*} {C C' : SetRel Event Event} {B B' : SetRel Event State}

/-- A nucleus along two relations is a nucleus along any larger ones. -/
def map (hC : C ⊆ C') (hB : B ⊆ B') (n : Nucleus C B) : Nucleus C' B' :=
  { n with complete := hC n.complete, become := hB n.become }

@[simp] theorem map_preparation (hC : C ⊆ C') (hB : B ⊆ B') (n : Nucleus C B) :
    (n.map hC hB).preparation = n.preparation := rfl

@[simp] theorem map_culmination (hC : C ⊆ C') (hB : B ⊆ B') (n : Nucleus C B) :
    (n.map hC hB).culmination = n.culmination := rfl

@[simp] theorem map_consequent (hC : C ⊆ C') (hB : B ⊆ B') (n : Nucleus C B) :
    (n.map hC hB).consequent = n.consequent := rfl

/-- An event is the preparation of a nucleus with a `p`-state as its consequent state iff a
culmination that gives rise to a `p`-state completes it. -/
theorem exists_iff {p : State → Prop} {v : Event} :
    (∃ n : Nucleus C B, n.preparation = v ∧ p n.consequent) ↔ ◇[C] (◇[B] p) v :=
  ⟨fun ⟨n, hv, hp⟩ ↦ hv ▸ ⟨_, n.complete, _, n.become, hp⟩,
    fun ⟨e, hc, s, hb, hp⟩ ↦ ⟨⟨v, e, s, hc, hb⟩, rfl, hp⟩⟩

end Nucleus

namespace Template

variable {Entity : Type*} {State Event : Type u} {M : Model State Event}
  {θ : Entity → Event → Prop} {P : Entity → State → Prop} {Q : Event → Prop} {y x : Entity}
  {v : Event}

/-- With causation as the completion relation, a causative of a change of state denotes the
preparations of the nuclei whose consequent state the root describes, of which its causing
subevent holds. -/
theorem denote_cause_achievement_iff {c : Template .event} :
    (cause c achievement).denote M θ P Q y x v ↔
      c.denote M θ P Q y x v ∧
        ∃ n : Nucleus M.cause M.become, n.preparation = v ∧ P x n.consequent :=
  and_congr_right fun _ ↦ Nucleus.exists_iff.symm

@[simp] theorem causing_accomplishment : accomplishment.causing = some act := rfl

@[simp] theorem caused_accomplishment : accomplishment.caused = some achievement := rfl

end Template

end ArgumentStructure.EventStructure
