module

public import Linglib.Semantics.ArgumentStructure.EnergySource
public import Linglib.Semantics.ArgumentStructure.EventStructure.Basic
public import Linglib.Data.Examples.RappaportHovavLevin2024

/-!
# Rappaport Hovav and Levin (2024): Variable agentivity: polysemy or underspecification?

This file formalizes the paper's account of the English verb *sweep*, whose subject may or may
not be an agent. The verb has two senses. In the basic sense its event structure says only
that an entity moves across a surface while imparting a force to it through contact; either
predicate may determine argument realization, general principles then yield the simple
transitive, transitive+PP and unaccusative+PP frames, and agentivity is left to pragmatic
inference. In the broom sense the moving entity is lexically saturated by a broom, an
instrument: since only an agent manipulates an instrument the sense is obligatorily agentive,
since the saturated variable cannot head a small clause the motion predicate cannot determine
argument realization, and since sweeping with a broom is a routine activity the surface may go
unexpressed.

Participants are classified by the source of their energy, `EnergySource`: a moving entity
that draws its energy from a user needs an expressed agent, which excludes *the brush swept
through her hair* while admitting *fire swept through their home*. `Licensed` derives from
the realization principles the surface frames an event admits, and
`acceptable_iff_licensed` checks the paper's judgments, those for *rub* and *scrape* included,
against it. A non-agentive subject in the simple transitive frame comes with no small clause,
against the resultative restriction. The event structures are templates: the transitive+PP
frame is the causative (50) of the activity (42), with no result state for *again* to scope
over (57).

## Implementation notes

The cause of the causativized event structure and the agent whose instrument or body part sits
in a *with* phrase are one participant, the causer. In the template of (42) both predicates are
the manner of one `ACT`, and which of them determines argument realization is `Predicate`.
Interpretive properties the paper derives from the conceptual content of *broom* (a floor-like
surface, the removal of unwanted material, the *with* phrase naming a broom), the resultatives,
the *again* readings other than the causative's lack of a result state, and the relaxation under
which a contextually recoverable agent goes unexpressed are outside the model, and their rows
are omitted.

## References

* [M. Rappaport Hovav, B. Levin, *Variable agentivity: polysemy or underspecification?*
  (2024)][rappaport-hovav-levin-2024]
* [M. Rappaport Hovav, B. Levin, *Building verb meanings* (1998)][rappaport-hovav-levin-1998]
* [M. Rappaport Hovav, *Lexical content and context: the causative alternation in English
  revisited* (2014)][rappaport-hovav-2014]
* [R. D. Van Valin, D. P. Wilkins, *The case for "effector": case roles, agents, and agency
  revisited* (1996)][van-valin-wilkins-1996]
* [D. A. Cruse, *Some thoughts on agentivity* (1973)][cruse-1973]
* [F. Schäfer, *Two types of external argument licensing: the case of causers*
  (2012)][schaefer-2012]
* [R. Folli, H. Harley, *Teleology and animacy in external arguments* (2008)][folli-harley-2008]
* [P. Kiparsky, *Remarks on denominal verbs* (1997)][kiparsky-1997]
* [B. Levin, *English verb classes and alternations* (1993)][levin-1993]
-/

@[expose] public section

namespace RappaportHovavLevin2024

open ArgumentStructure
open scoped SetRel

/-! ### Participants and senses -/

/-- The ontological kinds of participant the paper distinguishes. -/
inductive Kind where
  /-- An animate entity, an agent when it acts intentionally. -/
  | animate
  /-- A machine operating under its own power, which patterns with agents. -/
  | machine
  /-- Wind, fire, water, a storm. -/
  | naturalPhenomenon
  /-- A physical object imbued with kinetic energy: debris, ash, a truck carried off by water. -/
  | projectile
  /-- An artifact manipulated for its design purpose. -/
  | instrument
  /-- A body part of an agent. -/
  | bodyPart
  /-- A physical object that moves only while an agent is continuously involved: the coins
  swept off a counter. -/
  | displaced
  deriving DecidableEq

/-- The source of a participant's energy. -/
def Kind.energy : Kind → EnergySource
  | .animate | .machine | .naturalPhenomenon => .internal
  | .projectile => .imparted
  | .instrument | .bodyPart | .displaced => .instrumental

/-- Whether a participant manipulates instruments: an agent, or a machine designed to carry out
an agent's activity autonomously. -/
def Kind.Manipulates : Kind → Prop
  | .animate | .machine => True
  | _ => False

instance : DecidablePred Kind.Manipulates := λ k => by
  cases k <;> unfold Kind.Manipulates <;> infer_instance

/-- A sense of a verb of motion and sustained contact: whether the moving entity of its event
structure is lexically saturated by an instrument, and whether the sense names a culturally
recognized routine activity, which licenses the unspecified object frame. -/
structure Sense where
  saturated : Bool
  routine : Bool
  deriving DecidableEq

/-- Basic-*sweep*: an entity moves across a surface while imparting a force to it through
contact. -/
def basicSweep : Sense := ⟨false, false⟩

/-- Broom-*sweep*: the moving entity is a broom, and sweeping with one is a routine activity. -/
def broomSweep : Sense := ⟨true, true⟩

/-- An event described by a sense: the kind of the moving entity and the kind of the causer,
when there is one. -/
structure Event where
  sense : Sense
  mover : Kind
  causer : Option Kind
  deriving DecidableEq

/-- A saturated sense fixes the moving entity to an instrument, and an entity that draws its
energy from a user moves only under the control of an agent, who must be expressed. -/
def Event.WellFormed (i : Event) : Prop :=
  (i.sense.saturated = true → i.mover = .instrument) ∧
    (i.mover.energy = .instrumental → ∃ c ∈ i.causer, c.Manipulates)

instance : DecidablePred Event.WellFormed := λ _ => by
  unfold Event.WellFormed; infer_instance

/-- A sense is agentive when every well-formed event it describes has a causer that manipulates
instruments. -/
def Sense.Agentive (s : Sense) : Prop :=
  ∀ i : Event, i.sense = s → i.WellFormed → ∃ c ∈ i.causer, c.Manipulates

theorem agentive_of_saturated {s : Sense} (h : s.saturated = true) : s.Agentive :=
  λ _ hi ⟨h₁, h₂⟩ => h₂ (by rw [h₁ (hi ▸ h)]; rfl)

theorem not_agentive_of_free {s : Sense} (h : s.saturated = false) : ¬ s.Agentive := λ ha => by
  simpa using ha ⟨s, .naturalPhenomenon, none⟩ rfl ⟨by simp [h], by simp [Kind.energy]⟩

/-- Unspecified objects are licensed by senses naming culturally recognized routine activities
of agents, so a routine sense is agentive. -/
def Sense.Licit (s : Sense) : Prop := s.routine = true → s.Agentive

theorem Sense.Licit.saturated_of_routine {s : Sense} (h : s.Licit) (hr : s.routine = true) :
    s.saturated = true :=
  by_contra λ hs => not_agentive_of_free (Bool.eq_false_iff.mpr hs) (h hr)

/-! ### The argument realization principles -/

/-- The grammatically relevant predicates of the event structure, one of which determines
argument realization. -/
inductive Predicate where
  /-- The moving entity moves along a path across the surface. -/
  | motion
  /-- The moving entity, a force bearer, imparts a force to the surface, a force recipient. -/
  | contact
  deriving DecidableEq, Fintype

/-- The syntactic positions the principles assign. -/
inductive Position where
  | external
  | object
  | smallClauseSubject
  | smallClausePredicate
  | pathObject
  | oblique
  deriving DecidableEq

/-- What the principles require of a participant's expression. -/
inductive Requirement where
  | obligatory (p : Position)
  | optional (p : Position)
  | absent
  deriving DecidableEq

/-- The requirements on the moving entity, the path, the surface and the causer. -/
structure Realization where
  mover : Requirement
  path : Requirement
  surface : Requirement
  causer : Requirement
  deriving DecidableEq

/-- An effector is an external argument: the causer, when the event has one. -/
def Event.external (i : Event) : Requirement :=
  i.causer.elim .absent λ _ => .obligatory .external

/-- The realization principles applied to an event with respect to the determining
predicate. Simple motion along a path is expressed via a small clause whose subject is the
moving entity and whose predicate is the path, the surface being the object of the path's
preposition if expressed; a saturated moving entity is unavailable for syntactic expression,
so the motion predicate cannot determine realization. A force recipient is an internal
argument, omissible only for a routine activity. A self-energetic force bearer is an effector
and hence external; one that draws its energy from the causer sits in a *with* phrase,
optionally when the sense lexicalizes it. -/
def realize (i : Event) : Predicate → Option Realization
  | .motion =>
    if i.sense.saturated then none
    else some { mover := .obligatory .smallClauseSubject, path := .obligatory .smallClausePredicate,
                surface := .optional .pathObject, causer := i.external }
  | .contact =>
    some { mover := match i.causer with
             | none => if i.mover.energy.IsSelfEnergetic then .obligatory .external else .absent
             | some _ => if i.sense.saturated then .optional .oblique else .obligatory .oblique
           path := .absent
           surface := if i.sense.routine then .optional .object else .obligatory .object
           causer := i.external }

/-! ### Surface frames -/

/-- The positions in which a participant surfaces. -/
inductive Slot where
  | subject
  | object
  /-- The object of the preposition heading a directional PP. -/
  | pathObject
  /-- The object of *with*. -/
  | withObject
  /-- The directional PP itself, for the path. -/
  | directionalPP
  | unexpressed
  deriving DecidableEq

/-- Where a position surfaces: the subject of a small clause is the object of a transitive
clause and the subject of an unaccusative one. -/
def Position.slot (external : Bool) : Position → Slot
  | .external => .subject
  | .object => .object
  | .smallClauseSubject => if external then .object else .subject
  | .smallClausePredicate => .directionalPP
  | .pathObject => .pathObject
  | .oblique => .withObject

/-- A requirement met by a surface slot. -/
def Requirement.Satisfied (external : Bool) : Requirement → Slot → Prop
  | .obligatory p, s => s = p.slot external
  | .optional p, s => s = p.slot external ∨ s = .unexpressed
  | .absent, s => s = .unexpressed

instance (external : Bool) : DecidableRel (Requirement.Satisfied external) := λ r _ => by
  cases r <;> unfold Requirement.Satisfied <;> infer_instance

/-- The slots of the moving entity, the surface, the causer and the path in a sentence. -/
structure Slots where
  mover : Slot
  surface : Slot
  causer : Slot
  path : Slot
  deriving DecidableEq

/-- Whether the sentence has an external argument, the causer as subject. -/
def Slots.external (σ : Slots) : Bool := σ.causer = .subject

/-- A realization met by a sentence's slots. -/
def Realization.Satisfied (r : Realization) (σ : Slots) : Prop :=
  r.mover.Satisfied σ.external σ.mover ∧ r.path.Satisfied σ.external σ.path ∧
    r.surface.Satisfied σ.external σ.surface ∧ r.causer.Satisfied σ.external σ.causer

instance : DecidableRel Realization.Satisfied := λ _ _ => by
  unfold Realization.Satisfied; infer_instance

/-- The sentences describing an event when the given predicate determines realization. -/
def Licensed (i : Event) (p : Predicate) (σ : Slots) : Prop :=
  i.WellFormed ∧ ∃ r ∈ realize i p, r.Satisfied σ

instance (i : Event) (p : Predicate) (σ : Slots) : Decidable (Licensed i p σ) := by
  unfold Licensed; infer_instance

/-- *The north wind swept the open tundra*: the moving entity as subject and the surface as
object. -/
def simpleTransitive : Slots := ⟨.subject, .object, .unexpressed, .unexpressed⟩

/-- *The harpist swept the strings with a bow*: the causer as subject, the surface as object
and the moving entity in a *with* phrase. -/
def withFrame : Slots := ⟨.withObject, .object, .subject, .unexpressed⟩

/-- *I swept the terrace*: the causer as subject and the surface as object, the moving entity
unexpressed. -/
def instrumentTransitive : Slots := ⟨.unexpressed, .object, .subject, .unexpressed⟩

/-- *Yesterday, I swept in the morning*: the causer alone. -/
def unspecifiedObject : Slots := ⟨.unexpressed, .unexpressed, .subject, .unexpressed⟩

/-- *The wind swept the fires through the top growth*: the causer as subject, the moving
entity as object and the surface in a directional PP. -/
def transitivePP : Slots := ⟨.object, .pathObject, .subject, .directionalPP⟩

/-- *Fire swept through their home*: the moving entity as subject and the surface in a
directional PP. -/
def unaccusativePP : Slots := ⟨.subject, .pathObject, .unexpressed, .directionalPP⟩

/-! ### Basic-*sweep* -/

theorem basicSweep_simpleTransitive_iff (k : Kind) :
    Licensed ⟨basicSweep, k, none⟩ .contact simpleTransitive ↔ k.energy.IsSelfEnergetic := by
  cases k <;> decide

theorem basicSweep_withFrame_iff (k c : Kind) :
    Licensed ⟨basicSweep, k, some c⟩ .contact withFrame ↔
      (k.energy = .instrumental → c.Manipulates) := by
  cases k <;> cases c <;> decide

theorem basicSweep_not_instrumentTransitive (k c : Kind) :
    ¬ Licensed ⟨basicSweep, k, some c⟩ .contact instrumentTransitive := by
  cases k <;> cases c <;> decide

theorem basicSweep_unaccusativePP_iff (k : Kind) :
    Licensed ⟨basicSweep, k, none⟩ .motion unaccusativePP ↔ k.energy.IsSelfEnergetic := by
  cases k <;> decide

theorem basicSweep_transitivePP_iff (k c : Kind) :
    Licensed ⟨basicSweep, k, some c⟩ .motion transitivePP ↔
      (k.energy = .instrumental → c.Manipulates) := by
  cases k <;> cases c <;> decide

theorem motion_smallClause {i : Event} {σ : Slots} (h : Licensed i .motion σ) :
    σ.mover ≠ .unexpressed ∧ σ.path = .directionalPP := by
  obtain ⟨-, r, hr, hm, hp, -⟩ := h
  simp only [realize] at hr
  split at hr
  · exact absurd hr (Option.not_mem_none _)
  · obtain rfl := Option.mem_some_iff.mp hr
    refine ⟨λ h => ?_, hp⟩
    rw [h] at hm
    simp only [Requirement.Satisfied, Position.slot] at hm
    split at hm <;> simp at hm

theorem basicSweep_not_unspecifiedObject (i : Event) (h : i.sense = basicSweep) (p : Predicate) :
    ¬ Licensed i p unspecifiedObject := by
  obtain ⟨s, k, c⟩ := i
  simp only at h
  subst h
  rcases c with _ | c <;> cases p <;> (try cases c) <;> cases k <;> decide

/-! ### Broom-*sweep* -/

theorem not_licensed_motion_of_saturated {i : Event} (h : i.sense.saturated = true)
    (σ : Slots) : ¬ Licensed i .motion σ := by
  simp [Licensed, realize, h]

theorem broomSweep_instrumentTransitive_iff (c : Kind) :
    Licensed ⟨broomSweep, .instrument, some c⟩ .contact instrumentTransitive ↔
      c.Manipulates := by
  cases c <;> decide

theorem broomSweep_withFrame_iff (c : Kind) :
    Licensed ⟨broomSweep, .instrument, some c⟩ .contact withFrame ↔ c.Manipulates := by
  cases c <;> decide

theorem broomSweep_unspecifiedObject_iff (c : Kind) :
    Licensed ⟨broomSweep, .instrument, some c⟩ .contact unspecifiedObject ↔
      c.Manipulates := by
  cases c <;> decide

theorem broomSweep_not_uncaused (p : Predicate) (σ : Slots) :
    ¬ Licensed ⟨broomSweep, .instrument, none⟩ p σ :=
  λ ⟨⟨_, h⟩, _⟩ => by simpa using h rfl

/-! ### The event structures and *again*

The event structure (42) is an activity, one eventuality in which the moving entity moves across
the surface while imparting a force to it through contact. The broom sense keeps it (76),
restricting the moving entity to a broom. The transitive+PP frame is its causativized
counterpart (50), in which a cause brings the activity about. A narrow scope reading of *again*
emerges when a causative includes a result state or location for *again* to scope over, and
(50) has none, so *she swept the brush through Megan's shiny hair again* (57) has only the
reading on which the whole event is repeated. -/

section EventStructure

open EventStructure Template

/-- The event structure (42) of basic-*sweep*, which broom-*sweep* keeps (76). -/
def eventStructure : Template .event := .act

/-- The causativized event structure (50) of the transitive+PP frame, in which a cause brings
about the activity (42). -/
def causativeEventStructure : Template .event := .cause .effector eventStructure

/-- (50) is causative. -/
theorem causativeEventStructure_hasCause : causativeEventStructure.HasCause := by decide

/-- (50) has no result state or location: the state is no subterm of it, so *again* has no
restitutive attachment (57). -/
theorem not_isSubterm_state : ¬ state.IsSubterm causativeEventStructure :=
  fun h ↦ absurd (h.kinds_subset (Finset.mem_singleton_self _)) (by decide)

/-- Nor does (50) entail a change: in some interpretation a cause brings about the activity
with nothing giving rise to a state. -/
theorem not_forall_exists_become :
    ¬ ∀ (M : Interpretation Unit Unit Unit) P Q y x v,
      causativeEventStructure.denote M P Q y x v → ∃ s e, s ~[M.become] e :=
  fun h ↦ absurd (hasResultState_iff.2 h) (by decide)

end EventStructure

/-! ### The resultative restriction -/

/-- The resultative restriction: a subject that is not an agent selects a small clause, which
here can only be the path. -/
def ResultativeRestriction : Prop :=
  ∀ i p σ, Licensed i p σ → i.causer = none → ¬ i.mover.Manipulates →
    σ.mover = .subject → σ.path = .directionalPP

theorem not_resultativeRestriction : ¬ ResultativeRestriction := λ h =>
  absurd (h ⟨basicSweep, .naturalPhenomenon, none⟩ .contact simpleTransitive (by decide) rfl
    (by decide) rfl) (by decide)

/-! ### The paper's judgments -/

/-- The verbs of the paper's examples. -/
inductive Verb where
  | sweep
  | rub
  | scrape
  | funnel
  | mop
  deriving DecidableEq

/-- The verbs by their `paperFeatures` labels. -/
def Verb.labels : List (String × Verb) :=
  [("sweep", .sweep), ("rub", .rub), ("scrape", .scrape), ("funnel", .funnel), ("mop", .mop)]

/-- The senses by their `paperFeatures` labels: a free moving entity, an instrument
lexicalized as the moving entity, and such an instrument in a routine activity. -/
def Sense.labels : List (String × Sense) :=
  [("basic", basicSweep), ("instrument", ⟨true, false⟩), ("routine", broomSweep)]

/-- The kinds by their `paperFeatures` labels. -/
def Kind.labels : List (String × Kind) :=
  [("animate", .animate), ("machine", .machine), ("natural phenomenon", .naturalPhenomenon),
   ("projectile", .projectile), ("instrument", .instrument), ("body part", .bodyPart),
   ("displaced", .displaced)]

/-- The slots by their `paperFeatures` labels. -/
def Slot.labels : List (String × Slot) :=
  [("subject", .subject), ("object", .object), ("path object", .pathObject),
   ("with", .withObject), ("pp", .directionalPP)]

/-- A participant's slot, unexpressed when the row names none. -/
def slot? (e : Datum) (key : String) : Option Slot :=
  match e.feature? key with
  | none => some .unexpressed
  | some v => Slot.labels.lookup v

/-- The causer's kind, none when the row names none. -/
def causer? (e : Datum) : Option (Option Kind) :=
  match e.feature? "causer" with
  | none => some none
  | some v => (Kind.labels.lookup v).map some

/-- An example of the paper: its verb, the event it describes, the slots of the participants,
and the judgment. -/
structure Row where
  verb : Verb
  event : Event
  slots : Slots
  judgment : Judgment

/-- A datum read into its row. -/
def Row.ofDatum (e : Datum) : Option Row := do
  pure { verb := ← e.parse? "verb" Verb.labels
         event := { sense := ← e.parse? "sense" Sense.labels
                    mover := ← e.parse? "mover" Kind.labels
                    causer := ← causer? e }
         slots := { mover := ← slot? e "moverSlot", surface := ← slot? e "surfaceSlot",
                    causer := ← slot? e "causerSlot", path := ← slot? e "path" }
         judgment := e.judgment }

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by decide

/-- The paper's examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem acceptable_iff_licensed :
    ∀ d ∈ data, (d.judgment = .acceptable ↔ ∃ p, Licensed d.event p d.slots) := by
  decide

theorem frames_shared :
    ∀ v ∈ [Verb.sweep, .rub, .scrape],
      ∀ σ ∈ [simpleTransitive, transitivePP, unaccusativePP],
        ∃ d ∈ data, d.verb = v ∧ d.slots = σ ∧ d.judgment = .acceptable := by
  decide

end RappaportHovavLevin2024
