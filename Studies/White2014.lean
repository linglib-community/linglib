module

public import Mathlib.Order.SupClosed
public import Linglib.Semantics.Events.Closure
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Data.Examples.White2014

/-!
# White (2014): Factive-Implicatives and Modalized Complements

This file formalizes [white-2014]'s account of the factive-implicatives *remember* and
*forget*, factive with a finite complement and implicative with a control infinitive (1). The
verb is one item and always factive: the infinitival complement is headed by a modal
complementizer that contributes the presuppositional modality (`Modalized`), so
*remembered to take the trash out* presupposes that Bo had to, as *remembered that he had
to* does (7). The attitude is a Hintikkan quantifier over the worlds a memory event gives
access to (19), and the modal complementizer, unlike *that*, returns a property of events
(26). The Rule of Semantic Restructuring puts the two together, applying the attitude to the
property at the embedded event and summing that event with the attitude's into one compound
event (27) (`restructure`), which matrix aspect binds in the actual world (30). Implicative
entailments are then actuality entailments: a part of an actual compound event is actual, so
the remembered VP-event occurred (`actuality`), and with negation above aspect no actual
event is a remembering-to-VP (`negated_actuality`). A finite complement closes its own event
below the complementizer (23), (24), so the finite variant leaves the event's actuality open
(`exists_finite_not_actual`).

## Implementation notes

The attitude's memory relation and the modal's best worlds are accessibility relations with
event arguments ([kratzer-1996], [hacquard-2009]); the compound event is the join of its
parts, and actual events are closed under parts and joins. The step from an actual event
described as a VP-event in the accessible worlds to its being a VP-event in the actual world
is the hypothesis `EventDescriptionPreserved`, with events persisting into accessible worlds.
The *again* modification facts of the restructuring test and the coordination data are
recorded as examples only.

## References

* [white-2014]
* [bhatt-1999]
* [hacquard-2009]
* [karttunen-1971]
* [kratzer-1996]
* [wurmbrand-2014]
-/

@[expose] public section

namespace White2014

/-! ### The modal complementizer -/

/-- Which complements are headed by the modal complementizer: the nonfinite ones. -/
def Modalized (fr : ArgumentFrame) : Prop := ¬ fr.HasFinite

instance : DecidablePred Modalized := fun _ ↦ inferInstanceAs (Decidable (¬ _))

-- (1b), (1a)
theorem modalized_infinitival_not_finite :
    Modalized .infinitival ∧ ¬ Modalized .finiteClause := by
  decide

/-! ### Attitude, modal complementizer, and restructuring -/

section Semantics

variable {W E : Type*}

/-- The attitude (19): the proposition holds in every world the memory event gives access
to. -/
def attitude (mem : E → W → Set W) (p : W → Prop) (w : W) (e : E) : Prop :=
  ∀ w' ∈ mem e w, p w'

/-- The modal complementizer (26): a property of events holding of the event in every best
world. -/
def cMod (best : W → Set W) (f : W → E → Prop) (w : W) (e : E) : Prop :=
  ∀ w' ∈ best w, f w' e

variable [SemilatticeSup E]

/-- The Rule of Semantic Restructuring (27): the attitude applied to the property at the
embedded event, the two events summed into one compound event. -/
def restructure (att : (W → Prop) → W → E → Prop) (f : W → E → Prop) (w : W) (e₀ : E) :
    Prop :=
  ∃ e₁ e₂, e₀ = e₁ ⊔ e₂ ∧ att (f · e₂) w e₁

-- (28)
theorem restructure_attitude_cMod (mem : E → W → Set W) (best : W → Set W)
    (vp : W → E → Prop) (w : W) (e₀ : E) :
    restructure (attitude mem) (cMod best vp) w e₀ ↔
      ∃ e₁ e₂, e₀ = e₁ ⊔ e₂ ∧
        ∀ w' ∈ mem e₁ w, ∀ w'' ∈ best w', vp w'' e₂ :=
  Iff.rfl

variable (occurs : W → E → Prop)

/-- (30): *Bo remembered to VP*, with matrix aspect binding the compound event in the
evaluation world. -/
def rememberedTo (mem : E → W → Set W) (best : W → Set W) (vp : W → E → Prop) (w : W) :
    Prop :=
  ∃ e₀, occurs w e₀ ∧ restructure (attitude mem) (cMod best vp) w e₀

/-- (24): *Bo remembered that he VPed*, whose complement closes its own event. -/
def rememberedThat (mem : E → W → Set W) (vp : W → E → Prop) (w : W) (e : E) : Prop :=
  attitude mem (Event.closure vp) w e

/-- Preservation of event description: an event occurring in two worlds is described by the
same predicate in both. -/
def EventDescriptionPreserved (vp : W → E → Prop) : Prop :=
  ∀ e w w', occurs w e → occurs w' e → vp w e → vp w' e

/-- Events persist into the accessible worlds. -/
def Persists (acc : W → Set W) : Prop := ∀ e w w', occurs w e → w' ∈ acc w → occurs w' e

variable {occurs} {mem : E → W → Set W} {best : W → Set W} {vp : W → E → Prop}

theorem actuality (hpart : ∀ w, IsLowerSet {e | occurs w e})
    (hped : EventDescriptionPreserved occurs vp)
    (hmem : Persists occurs fun w ↦ ⋃ e, mem e w) (hbest : Persists occurs best)
    (hne : ∀ e w, ∃ w' ∈ mem e w, (best w').Nonempty) {w : W}
    (h : rememberedTo occurs mem best vp w) : ∃ e, occurs w e ∧ vp w e := by
  obtain ⟨e₀, he₀, e₁, e₂, rfl, hatt⟩ := h
  obtain ⟨w', hw', w'', hw''⟩ := hne e₁ w
  have he₂ : occurs w e₂ := hpart w le_sup_right he₀
  have hocc' : occurs w' e₂ := hmem e₂ w w' he₂ (Set.mem_iUnion.mpr ⟨e₁, hw'⟩)
  exact ⟨e₂, he₂, hped e₂ w'' w (hbest e₂ w' w'' hocc' hw'') he₂ (hatt w' hw' w'' hw'')⟩

/-- With negation above aspect, an actual VP-event is excluded given an actual memory event (31). -/
theorem negated_actuality (hjoin : ∀ w, SupClosed {e | occurs w e})
    (hped : EventDescriptionPreserved occurs vp)
    (hmem : Persists occurs fun w ↦ ⋃ e, mem e w) (hbest : Persists occurs best) {w : W}
    {e₁ : E} (he₁ : occurs w e₁) (h : ¬ rememberedTo occurs mem best vp w) :
    ¬ ∃ e, occurs w e ∧ vp w e := by
  rintro ⟨e₂, he₂, hvp⟩
  exact h ⟨e₁ ⊔ e₂, hjoin w he₁ he₂, e₁, e₂, rfl, fun w' hw' w'' hw'' ↦
    hped e₂ w w'' he₂
      (hbest e₂ w' w'' (hmem e₂ w w' he₂ (Set.mem_iUnion.mpr ⟨e₁, hw'⟩)) hw'') hvp⟩

/-- No actuality entailment with a finite complement (32): the remembered content can hold
while no VP-event is actual. -/
theorem exists_finite_not_actual :
    ∃ (mem : Unit → Bool → Set Bool) (vp : Bool → Unit → Prop)
      (occurs : Bool → Unit → Prop),
      rememberedThat mem vp true () ∧ ¬ ∃ e, occurs true e ∧ vp true e :=
  ⟨fun _ _ ↦ {false}, fun w _ ↦ w = false, fun w _ ↦ w = false,
    fun _ hw' ↦ ⟨(), hw'⟩, fun ⟨_, he, _⟩ ↦ Bool.noConfusion he⟩

end Semantics

end White2014
