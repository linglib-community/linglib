module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Semantics.Modality.EventRelativity
public import Linglib.Data.Examples.Hacquard2010

/-!
# Hacquard (2010): On the Event Relativity of Modal Auxiliaries

This file formalizes [hacquard-2010]'s event-relative semantics for modal auxiliaries. A modal's
modal base is a function of an event rather than a world (29), `must` and `can`, and its event
variable is bound by the closest binder (37), (38): the speech event for a high modal in a matrix
clause, the attitude event for a high modal in a complement, and the VP event for a low modal
(48), the binders of `Modality.ModalPosition`. Speech and attitude events carry propositional
content and embed a proposition under universal quantification over it (41), (44), `attitude`;
the epistemic modal base is the content of the event the modal is anchored to (51),
`Modality.contentNecessity` and `Modality.contentPossibility`, so it is undefined where a low
modal is anchored to a contentless VP event (49e), (59),
`Modality.not_contentPossibility_of_eq_none`, and defined again when the complement is itself an
attitude (60). Anchored to the event that embeds it, an epistemic modal quantifies over the same
worlds as that event, so the outer layer of quantification is vacuous, (53) to (57),
`attitude_can_iff` and `attitude_must_iff`, the possibility case once the information state is
consistent; and Yalcin's supposition (58) is incoherent because the modal quantifies over the
supposition's own content, `not_attitude_suppose`. Cinque's puzzle (section 3) is that
[cinque-1999]'s hierarchy fixes the epistemic head above tense and the root head below aspect,
`CinqueHead`, where a single flavor-neutral entry should suffice; the paper derives the same
matrix correlation from the content of the binding event, `epistemic_high_iff`. The paper's
examples are the rows of `Data.Examples.Hacquard2010`.

## Implementation notes

The content of an event is its set of compatible worlds, `⋂CON(e)`, an `Option` undefined for
contentless events; the descriptive part of an attitude or asserting event, `Exp(e, x)` and
`belief'(e, w)` or `Assert'(e₀, w)`, is an abstract predicate. Ordering sources are omitted, as
in the paper's derivations, and the circumstantial modal base (61), whose event dependence the
paper leaves open, is not defined. The individual and time a modal is keyed to (section 4) enter
only through the binding event; the Italian restructuring evidence belongs to [hacquard-2006].

## References

* [hacquard-2010]
* [cinque-1999]
* [yalcin-2007]
-/

@[expose] public section

namespace Hacquard2010

open Modality

variable {E W : Type*}

/-! ### Event-relative modals, section 5 -/

/-- A necessity modal (29) quantifies over the worlds its event-relative modal base returns. -/
def must (f : E → Set W) (q : W → Prop) (e : E) : Prop := ∀ w' ∈ f e, q w'

/-- A possibility modal (29) quantifies existentially over the same worlds. -/
def can (f : E → Set W) (q : W → Prop) (e : E) : Prop := ∃ w' ∈ f e, q w'

/-- A contentful event, an attitude or the speech event, embeds a proposition under universal
quantification over its content (41), (44); `holds e w` is the event's descriptive part. -/
def attitude (con : E → Option (Set W)) (holds : E → W → Prop) (e : E) (p : W → Prop)
    (w : W) : Prop :=
  holds e w ∧ contentNecessity con p e

variable {con : E → Option (Set W)} {holds : E → W → Prop} {f : E → Set W} {e : E}
  {q : W → Prop} {w : W} {C : Set W}

/-- The epistemic modal base is the content of the event the modal is anchored to (51). -/
theorem must_iff_contentNecessity (h : con e = some (f e)) :
    must f q e ↔ contentNecessity con q e :=
  (contentNecessity_iff_of_eq_some h).symm

theorem can_iff_contentPossibility (h : con e = some (f e)) :
    can f q e ↔ contentPossibility con q e :=
  (contentPossibility_iff_of_eq_some h).symm

/-! ### Content licensing, section 6.1 -/

/-- A possibility modal anchored to its embedding event quantifies over that event's worlds, so the
outer universal is vacuous for consistent content (53), (57). -/
theorem attitude_can_iff (hC : con e = some C) :
    attitude con holds e (fun _ ↦ contentPossibility con q e) w ↔
      holds e w ∧ (C.Nonempty → ∃ w' ∈ C, q w') := by
  rw [attitude, contentNecessity_const hC, contentPossibility_iff_of_eq_some hC]

/-- With consistent content, an embedded epistemic possibility says that `q` is compatible with the
embedding event's content (54). -/
theorem attitude_can_iff_of_nonempty (hC : con e = some C) (hne : C.Nonempty) :
    attitude con holds e (fun _ ↦ contentPossibility con q e) w ↔
      holds e w ∧ ∃ w' ∈ C, q w' := by
  rw [attitude_can_iff hC, forall_prop_of_true hne]

/-- An embedded epistemic necessity is necessity over the embedding event's content, the outer
layer again vacuous (55), (57). -/
theorem attitude_must_iff :
    attitude con holds e (fun _ ↦ contentNecessity con q e) w ↔
      holds e w ∧ contentNecessity con q e :=
  and_congr_right' contentNecessity_contentNecessity

/-- Supposing that it is raining and that it might not be is incoherent, which is [yalcin-2007]'s
puzzle (58). -/
theorem not_attitude_suppose {rain : W → Prop} (hC : con e = some C) (hne : C.Nonempty) :
    ¬ attitude con holds e
      (fun w' ↦ rain w' ∧ contentPossibility con (fun w'' ↦ ¬ rain w'') e) w := by
  rintro ⟨-, h⟩
  rw [contentNecessity_iff_of_eq_some hC] at h
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨w₁, hw₁, hnr⟩ := (contentPossibility_iff_of_eq_some hC).1 (h w₀ hw₀).2
  exact hnr (h w₁ hw₁).1

/-! ### Cinque's puzzle, section 3 -/

/-- [cinque-1999]'s hierarchy at the granularity the paper uses: an epistemic head above tense,
a root head below aspect. -/
inductive CinqueHead
  | modEpistemic
  | tense
  | aspect
  | modRoot
  deriving DecidableEq

namespace CinqueHead

/-- Height in the hierarchy, the topmost head highest. -/
def height : CinqueHead → ℕ
  | .modEpistemic => 3
  | .tense => 2
  | .aspect => 1
  | .modRoot => 0

/-- `h` sits above `h'` in the hierarchy. -/
def Above (h h' : CinqueHead) : Prop := h'.height < h.height

instance : DecidableRel Above := fun h h' ↦ inferInstanceAs (Decidable (h'.height < h.height))

/-- A high head sits above tense. -/
def IsHigh (h : CinqueHead) : Prop := h.Above .tense

instance : DecidablePred IsHigh := fun h ↦ inferInstanceAs (Decidable (h.Above .tense))

/-- The flavor the hierarchy stipulates for each modal head. -/
def flavor : CinqueHead → Option ModalFlavor
  | .modEpistemic => some .epistemic
  | .modRoot => some .circumstantial
  | _ => none

theorem isHigh_iff (h : CinqueHead) : h.IsHigh ↔ h.flavor = some .epistemic := by
  cases h <;> decide

theorem aspect_above_modRoot : CinqueHead.aspect.Above .modRoot := by decide

end CinqueHead

/-- One flavor-neutral entry gives an epistemic modal base exactly in the position above tense,
since the VP event of (59) lacks content (section 6.3). -/
theorem epistemic_high_iff {con : E → Option (Set W)} {ev : EventBinder → E}
    (hs : (con (ev .speechAct)).isSome) (hv : con (ev .vpEvent) = none) (pos : ModalPosition) :
    (con (ev pos.matrixBinder)).isSome ↔ pos = .aboveAsp := by
  cases pos <;> simp [ModalPosition.matrixBinder, hs, hv]

end Hacquard2010
