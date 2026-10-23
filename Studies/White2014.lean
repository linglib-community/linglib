module

public import Mathlib.Order.Lattice
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

/-- The control infinitive of (1b) is modalized, the finite clause of (1a) not. -/
theorem modalized_infinitival_not_finite :
    Modalized .infinitival ∧ ¬ Modalized .finiteClause := by
  decide

/-! ### Attitude, modal complementizer, and restructuring -/

section Semantics

variable {W E : Type*}

/-- The attitude (19): the proposition holds in every world the memory event gives access
to. -/
def attitude (mem : E → W → Set W) (p : W → Prop) (e : E) (w : W) : Prop :=
  ∀ w' ∈ mem e w, p w'

/-- The modal complementizer (26): a property of events holding of the event in every best
world. -/
def cMod (best : W → Set W) (f : E → W → Prop) (e : E) (w : W) : Prop :=
  ∀ w' ∈ best w, f e w'

variable [SemilatticeSup E]

/-- The Rule of Semantic Restructuring (27): the attitude applied to the property at the
embedded event, the two events summed into one compound event. -/
def restructure (att : (W → Prop) → E → W → Prop) (f : E → W → Prop) (e₀ : E)
    (w : W) : Prop :=
  ∃ e₁ e₂, e₀ = e₁ ⊔ e₂ ∧ att (f e₂) e₁ w

/-- (28): *remember* restructured with the modalized complement. -/
theorem restructure_attitude_cMod (mem : E → W → Set W) (best : W → Set W)
    (vp : E → W → Prop) (e₀ : E) (w : W) :
    restructure (attitude mem) (cMod best vp) e₀ w ↔
      ∃ e₁ e₂, e₀ = e₁ ⊔ e₂ ∧
        ∀ w' ∈ mem e₁ w, ∀ w'' ∈ best w', vp e₂ w'' :=
  Iff.rfl

variable (occurs : E → W → Prop)

/-- (30): *Bo remembered to VP*, with matrix aspect binding the compound event in the
evaluation world. -/
def rememberedTo (mem : E → W → Set W) (best : W → Set W) (vp : E → W → Prop) (w : W) :
    Prop :=
  ∃ e₀, occurs e₀ w ∧ restructure (attitude mem) (cMod best vp) e₀ w

/-- (24): *Bo remembered that he VPed*, whose complement closes its own event. -/
def rememberedThat (mem : E → W → Set W) (vp : E → W → Prop) (e : E) (w : W) : Prop :=
  attitude mem (λ w' => ∃ e', vp e' w') e w

/-- Preservation of event description: an event occurring in two worlds is described by the
same predicate in both. -/
def EventDescriptionPreserved (vp : E → W → Prop) : Prop :=
  ∀ e w w', occurs e w → occurs e w' → vp e w → vp e w'

/-- Events persist into the accessible worlds. -/
def Persists (acc : W → Set W) : Prop := ∀ e w w', occurs e w → w' ∈ acc w → occurs e w'

/-- The actual events are closed under parts. -/
def PartsOccur : Prop := ∀ e e' w, e ≤ e' → occurs e' w → occurs e w

/-- The actual events are closed under joins. -/
def JoinsOccur : Prop := ∀ e e' w, occurs e w → occurs e' w → occurs (e ⊔ e') w

variable {occurs} {mem : E → W → Set W} {best : W → Set W} {vp : E → W → Prop}

theorem actuality (hpart : PartsOccur occurs) (hped : EventDescriptionPreserved occurs vp)
    (hmem : Persists occurs (λ w => ⋃ e, mem e w)) (hbest : Persists occurs best)
    (hne : ∀ e w, ∃ w' ∈ mem e w, (best w').Nonempty) {w : W}
    (h : rememberedTo occurs mem best vp w) : ∃ e, occurs e w ∧ vp e w := by
  obtain ⟨e₀, he₀, e₁, e₂, rfl, hatt⟩ := h
  obtain ⟨w', hw', w'', hw''⟩ := hne e₁ w
  have he₂ : occurs e₂ w := hpart e₂ (e₁ ⊔ e₂) w le_sup_right he₀
  have hocc' : occurs e₂ w' := hmem e₂ w w' he₂ (Set.mem_iUnion.mpr ⟨e₁, hw'⟩)
  exact ⟨e₂, he₂,
    hped e₂ w'' w (hbest e₂ w' w'' hocc' hw'') he₂ (hatt w' hw' w'' hw'')⟩

/-- With negation above aspect, an actual VP-event is excluded given an actual memory event (31). -/
theorem negated_actuality (hjoin : JoinsOccur occurs)
    (hped : EventDescriptionPreserved occurs vp)
    (hmem : Persists occurs (λ w => ⋃ e, mem e w)) (hbest : Persists occurs best) {w : W}
    {e₁ : E} (he₁ : occurs e₁ w) (h : ¬ rememberedTo occurs mem best vp w) :
    ¬ ∃ e, occurs e w ∧ vp e w := by
  rintro ⟨e₂, he₂, hvp⟩
  exact h ⟨e₁ ⊔ e₂, hjoin e₁ e₂ w he₁ he₂, e₁, e₂, rfl, λ w' hw' w'' hw'' =>
    hped e₂ w w'' he₂
      (hbest e₂ w' w'' (hmem e₂ w w' he₂ (Set.mem_iUnion.mpr ⟨e₁, hw'⟩)) hw'') hvp⟩

/-- No actuality entailment with a finite complement (32): the remembered content can hold
while no VP-event is actual. -/
theorem exists_finite_not_actual :
    ∃ (mem : Unit → Bool → Set Bool) (vp : Unit → Bool → Prop)
      (occurs : Unit → Bool → Prop),
      rememberedThat mem vp () true ∧ ¬ ∃ e, occurs e true ∧ vp e true :=
  ⟨λ _ _ => {false}, λ _ w => w = false, λ _ w => w = false,
    λ _ hw' => ⟨(), hw'⟩, λ ⟨_, he, _⟩ => Bool.noConfusion he⟩

end Semantics

end White2014
