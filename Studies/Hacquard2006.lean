module

public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Modality.EventRelativity
public import Studies.Condoravdi2002
public import Linglib.Fragments.Romance.Italian.Modals
public import Linglib.Data.Examples.Hacquard2006

/-!
# Hacquard (2006): Aspects of Modality

This file formalizes [hacquard-2006]'s derivation of actuality entailments and its
event-relative semantics for modal auxiliaries. Perfective aspect is a quantifier over events
anchored to a world (72a), `perfective`; when tense sits above a root modal, aspect moves above
the modal, so its event is bound in the actual world while the modal binds only the world in
which the event is described (75). With the principle of Event Identification across Worlds
(76), `IdentifiesAcrossWorlds`, the actual event is then a `Q`-event in the actual world:
`actuality_of_rootPossibility` and `actuality_of_rootNecessity` are [bhatt-1999]'s actuality
entailment for the possibility and necessity modals (86), (87), and the goal that restricts a
goal-oriented modal need not hold in the actual world (88). A modal above aspect binds the
world in which the event occurs, so no actuality follows, `epistemicPossibility_not_actual`;
and the imperfective's `GEN` (130) binds the event variable itself and needs no verifying
instance, `gen_not_actual`, which is why root modals under imperfective are not implicative
(100). Chapter 3 relativizes the accessibility relation to an event bound by the closest
binder, aspect, the speech event, or an attitude (200), (309), so a modal is keyed to that
event's participants and time (201), `positionPerspective`; an epistemic relation needs an
event with content (310a), so an aspect-bound modal is epistemic only under a contentful
complement, `not_aspectBoundEpistemic_of_eq_none`, and its reading (248) is an epistemic
necessity for the attitude holder, `aspectBoundEpistemic_iff`. The starting point of the
account is that one modal verb has root and epistemic readings alike, as Italian *potere* and
*dovere* do, `italian_modals_one_entry`, so the contrast in actuality entailments cannot be
lexical. The dissertation's examples are the rows of `Data.Examples.Hacquard2006`.

## Implementation notes

Events, worlds, and times are arbitrary types with an occurrence relation and a running time;
event descriptions are predicates of an event and a world, and a description is assumed to hold
of an event only where it occurs. Modal bases are functions from events to sets of worlds, the
content of an event is partial, and the epistemic readings are
`Semantics/Modality/EventRelativity.lean`'s quantifiers over it. The binding conditions (200)
and (309) are syntactic and enter only through which event a modal is anchored to; the
progressive (124) and the counterfactual modal of chapter 2, Italian *volere* (chapter 4), and
the interaction with negation (84) are not formalized.

## References

* [hacquard-2006]
* [bhatt-1999]
* [condoravdi-2002]
-/

@[expose] public section

namespace Hacquard2006

open Modality

variable {W E T : Type*}

/-! ### One entry per modal, chapter 1 -/

theorem italian_modals_one_entry :
    ∀ m ∈ Italian.modals,
      m.VariesFlavor ∧ ¬ m.VariesForce ∧ ¬ m.Epistemic ∧ ¬ m.Circumstantial := by
  decide

/-! ### Aspect as a world-anchored quantifier over events, chapter 1 -/

/-- Perfective aspect (72a) holds when an event of the world whose running time lies within the
reference time satisfies the predicate. -/
def perfective (occurs : E → W → Prop) (τ : E → Set T) (w : W) (t : Set T) (P : E → Prop) :
    Prop :=
  ∃ e, occurs e w ∧ τ e ⊆ t ∧ P e

/-- A root modal below aspect (75) takes the event aspect quantifies over as its event variable
and binds the world in which that event is described. -/
def rootPossibility (f : E → Set W) (Q : E → W → Prop) (e : E) : Prop := ∃ w' ∈ f e, Q e w'

/-- The necessity modal below aspect (87). -/
def rootNecessity (f : E → Set W) (Q : E → W → Prop) (e : E) : Prop := ∀ w' ∈ f e, Q e w'

/-- Event Identification across Worlds (76) says that an event that occurs in two worlds and is
a `Q`-event in one is a `Q`-event in the other. -/
def IdentifiesAcrossWorlds (occurs : E → W → Prop) (Q : E → W → Prop) : Prop :=
  ∀ e w₁ w₂, occurs e w₁ → occurs e w₂ → Q e w₁ → Q e w₂

/-- A description holds of an event only in worlds where the event occurs. -/
def DescribesOccurrence (occurs : E → W → Prop) (Q : E → W → Prop) : Prop :=
  ∀ e w, Q e w → occurs e w

variable {occurs : E → W → Prop} {τ : E → Set T} {f : E → Set W} {Q : E → W → Prop} {w : W}
  {t : Set T}

/-- A root possibility modal under perfective aspect entails the unmodalized perfective sentence
((75), (86), (89a)). -/
theorem actuality_of_rootPossibility (hid : IdentifiesAcrossWorlds occurs Q)
    (hocc : DescribesOccurrence occurs Q) (h : perfective occurs τ w t (rootPossibility f Q)) :
    perfective occurs τ w t (Q · w) := by
  obtain ⟨e, hew, ht, w', -, hq⟩ := h
  exact ⟨e, hew, ht, hid e w' w (hocc e w' hq) hew hq⟩

/-- The necessity modal (87) has the same entailment, given an accessible world. -/
theorem actuality_of_rootNecessity (hid : IdentifiesAcrossWorlds occurs Q)
    (hocc : DescribesOccurrence occurs Q) (hne : ∀ e, (f e).Nonempty)
    (h : perfective occurs τ w t (rootNecessity f Q)) : perfective occurs τ w t (Q · w) := by
  obtain ⟨e, hew, ht, hall⟩ := h
  obtain ⟨w', hw'⟩ := hne e
  exact ⟨e, hew, ht, hid e w' w (hocc e w' (hall w' hw')) hew (hall w' hw')⟩

/-- Root necessity entails root possibility (89), so the desirability inference of (89b) is a scalar
implicature from not asserting (89c). -/
theorem rootPossibility_of_rootNecessity {e : E} (hne : (f e).Nonempty)
    (h : rootNecessity f Q e) : rootPossibility f Q e :=
  let ⟨w', hw'⟩ := hne
  ⟨w', hw', h w' hw'⟩

/-- A modal above aspect (chapter 3) binds the world of aspect's restriction, so the event
occurs in an accessible world. -/
def epistemicPossibility (occurs : E → W → Prop) (τ : E → Set T) (acc : Set W) (t : Set T)
    (Q : E → W → Prop) : Prop :=
  ∃ w' ∈ acc, perfective occurs τ w' t (Q · w')

/-- An epistemic possibility modal above aspect has no actuality entailment, as in (1b). -/
theorem epistemicPossibility_not_actual {acc : Set W} {w' : W} (hw' : w' ∈ acc) {e : E}
    (he : occurs e w') (ht : τ e ⊆ t) (hq : Q e w') (hno : ∀ e, ¬ occurs e w) :
    epistemicPossibility occurs τ acc t Q ∧ ¬ perfective occurs τ w t (Q · w) :=
  ⟨⟨w', hw', e, he, ht, hq⟩, fun ⟨e, he, _, _⟩ ↦ hno e he⟩

/-! ### The imperfective, chapter 2 -/

/-- `GEN` (130) is the generic operator under a selection function of the normal or ideal events
from the perspective of `w` at `t`: it holds when every ideal event meeting the contextual
restriction satisfies the predicate. It binds the event variable itself, so it requires no
verifying instance. -/
def gen (ideal : W → Set T → Set E) (restr : E → Prop) (w : W) (t : Set T) (P : E → Prop) :
    Prop :=
  (w, t) ∈ (Genericity.Normality.ofAccess fun i : W × Set T ↦ ideal i.1 i.2).gen {e | restr e}
    {e | P e}

/-- A root modal under `GEN` has no actuality entailment ((93), (100)). -/
theorem gen_not_actual {ideal : W → Set T → Set E} {restr : E → Prop} (hideal : ideal w t = ∅)
    (hno : ∀ e, ¬ occurs e w) :
    gen ideal restr w t (rootPossibility f Q) ∧ ¬ perfective occurs τ w t (Q · w) :=
  ⟨fun e he ↦ (Set.notMem_empty e (hideal ▸ he.1)).elim, fun ⟨e, he, _, _⟩ ↦ hno e he⟩

/-! ### Event-relative modality, chapters 3 and 4 -/

/-- Perspective of the anchoring event in a past-tense clause (200), (309): the speech event
sits at the utterance time, an attitude or the event quantified by aspect at the time tense
provides. -/
def binderPerspective : EventBinder → TemporalPerspective
  | .speechAct => .present
  | _ => .past

/-- The perspective a modal's position determines in a matrix clause (201), through the event
its closest binder supplies. -/
def positionPerspective (pos : ModalPosition) : TemporalPerspective :=
  binderPerspective pos.matrixBinder

-- the two readings of (201) are [condoravdi-2002]'s two scopes of the modal and the perfect
open Condoravdi2002 (Scope) in
example :
    positionPerspective .aboveAsp = Scope.modalPerf.perspective ∧
    positionPerspective .belowAsp = Scope.perfModal.perspective :=
  ⟨rfl, rfl⟩

/-- The same modal gets different temporal perspectives from different positions (201). -/
theorem position_determines_perspective :
    positionPerspective .aboveAsp ≠ positionPerspective .belowAsp := nofun

theorem embedding_shifts_perspective :
    binderPerspective ModalPosition.aboveAsp.embeddedBinder ≠
      binderPerspective ModalPosition.aboveAsp.matrixBinder := nofun

/-- The aspect-bound epistemic reading of a modal over an attitude complement (248c), (248d).
There was an attitude state of the subject within the reference time, and some world
compatible with its content is such that all worlds compatible with it are `Q`-worlds. -/
def aspectBoundEpistemic (occurs : E → W → Prop) (τ : E → Set T) (con : E → Option (Set W))
    (think : E → Prop) (w : W) (t : Set T) (Q : W → Prop) : Prop :=
  perfective occurs τ w t fun s ↦
    think s ∧ contentPossibility con (fun _ ↦ contentNecessity con Q s) s

variable {con : E → Option (Set W)} {think : E → Prop} {P : W → Prop}

/-- The reading (248) is an epistemic necessity for the attitude holder, a past belief state
with consistent content that entails `Q`. -/
theorem aspectBoundEpistemic_iff :
    aspectBoundEpistemic occurs τ con think w t P ↔
      perfective occurs τ w t fun s ↦ think s ∧ ∃ C ∈ con s, C.Nonempty ∧ ∀ w'' ∈ C, P w'' :=
  exists_congr fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    contentPossibility_contentNecessity

/-- An aspect-bound modal has no epistemic reading where actual events lack content, as with the
train-taking of (246), since the reading needs a contentful event (310a). -/
theorem not_aspectBoundEpistemic_of_eq_none (h : ∀ e, occurs e w → con e = none) :
    ¬ aspectBoundEpistemic occurs τ con think w t P :=
  fun ⟨e, he, _, _, hp⟩ ↦ not_contentPossibility_of_eq_none (h e he) hp

end Hacquard2006
