module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Modality.Basic
public import Linglib.Semantics.Modality.EventRelativity
public import Linglib.Syntax.Cartography
public import Linglib.Data.Examples.Hacquard2010

/-!
# Hacquard (2010): On the Event Relativity of Modal Auxiliaries

This file formalizes [hacquard-2010]'s event-relative semantics for modal auxiliaries. A modal's
modal base is a function of an event rather than a world (29), `must` and `can`, and its event
variable is bound by the closest binder (37), (38): the speech event for a high modal in a matrix
clause, the attitude event for a high modal in a complement, and the VP event for a low modal
(48), `Modality.ModalPosition.binder`. Speech and attitude events carry propositional content
and embed a proposition under universal quantification over it (41), (44), `attitude`; the
epistemic modal base is the content of the event the modal is anchored to (51), the relation
`Modality.contentAccessible`, so it is undefined where a low modal is anchored to a contentless VP
event (49e), (59), and defined again when the complement is itself an attitude (60). Anchored to
the event that embeds it, an epistemic modal quantifies over the same worlds as that event, so the
outer layer of quantification is vacuous, (53) to (57), `attitude_can_iff` and
`attitude_must_iff`, the possibility case once the information state is consistent; and Yalcin's
supposition (58) is incoherent because the modal quantifies over the supposition's own content,
`not_attitude_suppose`. Cinque's puzzle (section 3) is that
[cinque-1999]'s hierarchy fixes the epistemic head above tense and the root head below aspect
(`tPast_lt_iff_eq_modEpistemic`), where a single flavor-neutral entry should suffice; the paper
derives the same matrix correlation from the content of the binding event, `epistemic_high_iff`. The paper's
examples are the rows of `Data.Examples.Hacquard2010`.

## Implementation notes

The content of an event is its set of compatible worlds, `⋂CON(e)`, an `Option` undefined for
contentless events; the descriptive part of an attitude or asserting event, `Exp(e, x)` and
`belief'(e, w)` or `Assert'(e₀, w)`, is an abstract predicate. Ordering sources are omitted, as
in the paper's derivations, and the circumstantial modal base (61), whose event dependence the
paper leaves open, is not defined. The individual and time a modal is keyed to (section 4) enter
only through the binding event; the Italian restructuring evidence belongs to [hacquard-2006].

(10) says that root modals are below aspect. The hierarchy places one root modal head, the
volitional, below habitual aspect but above perfect and progressive aspect, and leaves the
obligation and ability heads of the root modals the paper discusses unplaced. (10) agrees with
Cinque's first approximation of the hierarchy, which puts a root head among the lowest aspects.

## References

* [hacquard-2010]
* [cinque-1999]
* [yalcin-2007]
-/

@[expose] public section

namespace Hacquard2010

open Modality ModalLogic

variable {E W : Type*}

/-! ### Event-relative modals, section 5 -/

/-- A necessity modal (29) quantifies over the worlds its event-relative modal base returns:
necessity along the relation from each event to those worlds. -/
def must (f : E → Set W) : (W → Prop) → E → Prop := □[SetRel.ofSuccessors f]

/-- A possibility modal (29) quantifies existentially over the same worlds. -/
def can (f : E → Set W) : (W → Prop) → E → Prop := ◇[SetRel.ofSuccessors f]

/-- A contentful event, an attitude or the speech event, embeds a proposition under universal
quantification over its content (41), (44); `holds e w` is the event's descriptive part. -/
def attitude (con : E → Option (Set W)) (holds : E → W → Prop) (e : E) (p : W → Prop)
    (w : W) : Prop :=
  holds e w ∧ □[contentAccessible con] p e

variable {con : E → Option (Set W)} {holds : E → W → Prop} {f : E → Set W} {e : E}
  {q : W → Prop} {w : W}

-- (51)
theorem must_iff_box (h : con e = some (f e)) : must f q e ↔ □[contentAccessible con] q e :=
  (box_contentAccessible_iff h).symm

theorem can_iff_diamond (h : con e = some (f e)) : can f q e ↔ ◇[contentAccessible con] q e :=
  (diamond_contentAccessible_iff h).symm

/-! ### Content licensing, section 6.1 -/

/-- A possibility modal anchored to its embedding event quantifies over that event's worlds, so
for consistent content the outer universal is vacuous (53), (54), (57). -/
theorem attitude_can_iff (hC : e ∈ (contentAccessible con).dom) :
    attitude con holds e (fun _ ↦ ◇[contentAccessible con] q e) w ↔
      holds e w ∧ ◇[contentAccessible con] q e := by
  rw [attitude, box_const, forall_prop_of_true hC]

/-- An embedded epistemic necessity is necessity over the embedding event's content, the outer
layer again vacuous (55), (57). -/
theorem attitude_must_iff :
    attitude con holds e (fun _ ↦ □[contentAccessible con] q e) w ↔
      holds e w ∧ □[contentAccessible con] q e :=
  and_congr_right' <| box_const.trans ⟨fun h v hv ↦ h ⟨v, hv⟩ v hv, fun h _ ↦ h⟩

/-- Supposing that it is raining and that it might not be is incoherent, which is [yalcin-2007]'s
puzzle (58). -/
theorem not_attitude_suppose {rain : W → Prop} (hC : e ∈ (contentAccessible con).dom) :
    ¬ attitude con holds e
      (fun w' ↦ rain w' ∧ ◇[contentAccessible con] (fun w'' ↦ ¬ rain w'') e) w := by
  rintro ⟨-, h⟩
  obtain ⟨w₀, hw₀⟩ := hC
  obtain ⟨w₁, hw₁, hnr⟩ := (h w₀ hw₀).2
  exact hnr (h w₁ hw₁).1

/-! ### Cinque's puzzle, section 3

The paper's (10) is the part of [cinque-1999]'s hierarchy, `Cartography.Head`, that the puzzle
turns on. -/

/-- Of the modal heads of the hierarchy, the epistemic one alone is above tense, so the hierarchy
fixes the flavor of a modal by its position. -/
theorem tPast_lt_iff_eq_modEpistemic {h : Cartography.Head} (hm : h.family = .modality) :
    .tPast < h ↔ h = .modEpistemic := by
  revert h
  decide

theorem modVolitional_lt_aspHabitual : Cartography.Head.modVolitional < .aspHabitual := by
  decide

/-- One flavor-neutral entry gives an epistemic modal base exactly in the position above tense,
since the VP event of (59) lacks content (section 6.3). -/
theorem epistemic_high_iff {con : E → Option (Set W)} {ev : EventBinder → E}
    (hs : (con (ev .speechAct)).isSome) (hv : con (ev .vpEvent) = none) (pos : ModalPosition) :
    (con (ev (pos.binder .speechAct))).isSome ↔ pos = .high := by
  cases pos <;> simp [ModalPosition.binder, hs, hv]

end Hacquard2010
