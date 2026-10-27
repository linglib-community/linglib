module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Modality.Necessity

/-!
# The progressive

The progressive is a modal operator. An event is in progress toward an event type when, in every
best world of a circumstantial modal base for the event under that description, ranked by an
ordering source of propositions that the event is not interrupted, some event of the type includes
it as a nonfinal part. The base holds the facts relevant to whether the event is completed as an
event of the type, so an event can be in progress toward a completion that never happens: *Mary
was drawing a circle* does not entail *Mary drew a circle*. As an interval property, the
progressive holds at the run times of the events in progress, and composes with the perfect and
the tenses like the other viewpoint operators.

The imperfective, which requires an actual event of the type, is the case of a totally realistic
modal base, where the actual world is the only best world: there the progressive [falls inside the
imperfective](##PROG_subset_IMPF), and the inference from progressive to perfective returns.

## Main definitions

* `Aspect.NonfinalPart`: an event includes another as a part whose run time is not final in its.
* `Aspect.InProgress`: an event is in progress toward an event type.
* `Aspect.PROG`: the progressive as an interval property.

## Implementation notes

* Events are ordered by part-of, the mereological order of the event domain. The collapse to the
  imperfective assumes that the temporal trace preserves parthood, a law the event semantics
  states as a hypothesis where it is needed.
* The modal base depends on the event and on its description, the ordering source on the event
  alone.

## References

* [portner-1998]
* [dowty-1979]
* [kratzer-1991]
-/

@[expose] public section

namespace Aspect

open Event (τ)
open Modality

variable {E W T : Type*} [PartialOrder E] [LinearOrder T] [Event.TemporalTrace E T]

/-- `e'` includes `e` as a nonfinal part: `e` is part of `e'`, and the run time of `e` is not a
final subinterval of that of `e'`. -/
def NonfinalPart (e e' : E) : Prop := e ≤ e' ∧ ¬ (τ e).FinalSubinterval (τ e')

/-- `e` is in progress toward the event type `P` at `w` when in every best world of the
circumstantial base `circ e P` under the ordering source `ni e`, the propositions that `e` is not
interrupted, some event of type `P` includes `e` as a nonfinal part. -/
def InProgress (circ : E → (W → E → Prop) → Background W) (ni : E → Background W) (e : E)
    (P : W → E → Prop) : W → Prop :=
  necessity (circ e P) (ni e) fun v ↦ ∃ e', NonfinalPart e e' ∧ P v e'

/-- The progressive of `P` holds at the run times of the events in progress toward `P`. -/
def PROG (circ : E → (W → E → Prop) → Background W) (ni : E → Background W)
    (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  fun w ↦ τ '' {e | InProgress circ ni e P w}

variable {circ : E → (W → E → Prop) → Background W} {ni : E → Background W} {e e' : E}
  {P : W → E → Prop} {w : W} {t : NonemptyInterval T}

theorem inProgress_iff :
    InProgress circ ni e P w ↔
      ∀ v ∈ bestWorlds (circ e P) (ni e) w, ∃ e', NonfinalPart e e' ∧ P v e' :=
  necessity_iff ..

theorem mem_PROG : t ∈ PROG circ ni P w ↔ ∃ e, InProgress circ ni e P w ∧ τ e = t := Iff.rfl

theorem NonfinalPart.lt (hτ : Monotone (τ : E → NonemptyInterval T)) (h : NonfinalPart e e') :
    τ e < τ e' :=
  (hτ h.1).lt_of_ne fun heq ↦ h.2 ⟨heq.le, congrArg (fun s ↦ s.snd) heq⟩

/-- Over a totally realistic modal base, an event in progress toward `P` is part of an actual
event of type `P`. -/
theorem InProgress.exists_of_isTotallyRealistic (hf : (circ e P).IsTotallyRealistic)
    (h : InProgress circ ni e P w) : ∃ e', NonfinalPart e e' ∧ P w e' :=
  hf.necessity_le_id (ni e) _ w h

/-- Over totally realistic modal bases the progressive falls inside the imperfective. -/
theorem PROG_subset_IMPF (hτ : Monotone (τ : E → NonemptyInterval T))
    (hf : ∀ e, (circ e P).IsTotallyRealistic) : PROG circ ni P w ⊆ IMPF P w := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨e', he', hP⟩ := he.exists_of_isTotallyRealistic (hf e)
  exact ⟨e', he'.lt hτ, hP⟩

end Aspect
