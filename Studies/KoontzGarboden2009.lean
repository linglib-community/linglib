module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Position
public import Linglib.Fragments.Romance.Spanish.Verbs

/-!
# Koontz-Garboden (2009): Anticausativization

Koontz-Garboden analyzes anticausativization, the derivation of an inchoative from its
causative as in Spanish *romper* 'break (tr.)' ~ *romperse* 'break (intr.)', as reflexivization.
The reflexive clitic denotes Chierchia's operator `λℜλx[ℜ(x,x)]`, so a derived inchoative is its
causative restricted to the diagonal and keeps the CAUSE operator: its single argument causes its
own change. A verb whose causer must be an agent, like *asesinar* 'assassinate', therefore
reflexivizes only to a reflexive reading, while a verb with Van Valin and Wilkins's underspecified
EFFECTOR, like *romper*, also has the anticausative reading. *Por sí solo* 'by itself' is licensed
by derived inchoatives but not by passives or by the CAUSE-less representation of internally
caused verbs. Unlike Grimshaw's inchoativization rule, which strips CAUSE, reflexivization
respects the Monotonicity Hypothesis that word formation never removes operators.

## Main definitions

* `anticausative`: the derived inchoative, the causative on its diagonal.
* `AnticausativeReading`: the anticausative reading of a reflexivized verb.
* `LicensesBySelf`: the licensing condition of *por sí solo*.
* `MonotonicityHypothesis`: the Monotonicity Hypothesis on event templates.
* `inchoative`, `boundInchoative`: the inchoatives of the deletion and least common denominator
  analyses, which have no CAUSE, and of the existential binding analysis, which has a causing
  eventuality with no participant.

## Implementation notes

The paper's representations take the change-of-state event as the verb's event argument and
existentially close the causing event. `causative` is therefore the causative template at its
caused position, `Template.denoteAt`, and `exists_causative_iff` is the agreement of the
positions of a template under existential closure.
The underspecified effector and the agent are
relations between individuals and events beside the `EventStructure.Model`.
A Spanish verb's causer specification is derived from the proto-role subject profile the
fragment states for it, after Dowty: a causer that must be an agent entails volition. The
reflexive/anticausative syncretism in Haspelmath's survey, which the paper tabulates, is a
typological argument left in prose.

## References

* [koontz-garboden-2009]
* [chierchia-2004b]
* [van-valin-wilkins-1996]
* [grimshaw-1982]
* [reinhart-siloni-2005]
* [levin-hovav-1995]
* [rappaport-hovav-levin-1998]
* [dowty-1991]
* [haspelmath-1990]
-/

@[expose] public section

universe u

namespace KoontzGarboden2009

open ArgumentStructure ArgumentStructure.EventStructure Spanish.Verbs
open scoped SetRel ModalLogic

/-- The reflexivization operator restricts a two-place relation to its diagonal. It is the
denotation of the reflexive clitic *se*. -/
def reflexivize {α β : Type*} (R : α → α → β) : α → β := fun x ↦ R x x

section Model

variable {Entity : Type*} {State E : Type u}
  (M : ArgumentStructure.EventStructure.Model State E)
  (effector θ agent : Entity → E → Prop) (P : Entity → State → Prop)

/-- A causative change-of-state verb, ((10b), (17), (29)), holds of an event `e` in which `x` comes
to be in the root's state, caused by an event whose participant `y` bears the causer relation `θ`,
the underspecified `effector` for *romper* and an agent relation for *asesinar*. -/
def causative (y x : Entity) (e : E) : Prop :=
  Template.denoteAt M θ P ⊤ (.caused (c := .effector) (.here .achievement)) y x e

theorem causative_iff {y x : Entity} {e : E} :
    causative M θ P y x e ↔ ∃ w, θ y w ∧ w ~[M.cause] e ∧ ◇[M.become] (P x) e :=
  Template.denoteAt_caused_here

theorem exists_causative_iff (y x : Entity) :
    (∃ e, causative M θ P y x e) ↔ ∃ w, θ y w ∧ ◇[M.cause] (◇[M.become] (P x)) w :=
  Template.exists_denoteAt_iff (M := M) (θ := θ) (P := P) (Q := ⊤) (y := y) (x := x)
    (.caused (c := .effector) (.here .achievement))

/-- Anticausativization is reflexivization. The derived inchoative is the causative on its
diagonal, so the undergoer is also the participant in the causing event. -/
def anticausative : Entity → E → Prop := reflexivize (causative M θ P)

theorem anticausative_iff (x : Entity) (e : E) :
    anticausative M θ P x e ↔ ∃ w, θ x w ∧ w ~[M.cause] e ∧ ◇[M.become] (P x) e :=
  causative_iff M θ P

/-- A reflexivized verb has the anticausative reading when it has an instance whose single
argument is not an agent of the event causing its change, as in *el vaso se rompió* 'the cup
broke'. -/
def AnticausativeReading (P : Entity → E → Prop) : Prop :=
  ∃ x e, P x e ∧ ∀ w, w ~[M.cause] e → ¬ agent x w

/-- *Por sí solo* 'by itself' ((54)) is licensed on a predicate that entails a causing subevent
with the subject as its effector; the modifier then adds that the subject is its sole
effector (§3.4, §4.1). -/
def LicensesBySelf (P : Entity → E → Prop) : Prop :=
  ∀ x e, P x e → ∃ w, w ~[M.cause] e ∧ effector x w

/-- In the passive of a causative verb the causer is existentially closed rather than
identified with the subject. -/
def passive (x : Entity) (e : E) : Prop := ∃ y, causative M effector P y x e

/-- (99a): an inchoative with no CAUSE holds of an event in which `x` comes to be in the root's
state. It is what a deletion analysis derives and what a least common denominator analysis
takes the root to denote. -/
def inchoative (x : Entity) (e : E) : Prop := ◇[M.become] (P x) e

/-- (99b): an inchoative whose causing eventuality is existentially bound. -/
def boundInchoative (x : Entity) (e : E) : Prop := ∃ w, w ~[M.cause] e ∧ inchoative M P x e

variable {M effector θ agent P}

-- §3.5
theorem causative_self_of_anticausative {x : Entity} {e : E}
    (h : anticausative M θ P x e) : causative M θ P x x e := h

/-- A derived inchoative retains a causing subevent whose causer is its subject, so CAUSE
survives reflexivization. -/
theorem exists_cause_of_anticausative {x : Entity} {e : E}
    (h : anticausative M θ P x e) : ∃ w, θ x w ∧ w ~[M.cause] e :=
  let ⟨w, hθ, hc, _⟩ := (anticausative_iff M θ P x e).1 h; ⟨w, hθ, hc⟩

theorem exists_nonagent_of_anticausativeReading
    (h : AnticausativeReading M agent (anticausative M θ P)) : ∃ x w, θ x w ∧ ¬ agent x w :=
  let ⟨x, e, ha, hna⟩ := h
  let ⟨w, hθ, hc, _⟩ := (anticausative_iff M θ P x e).1 ha
  ⟨x, w, hθ, hna w hc⟩

/-- A verb whose causer must be an agent ((29), *asesinar*) reflexivizes to the reflexive-type
reading only ((27)–(28), (31)). -/
theorem not_anticausativeReading (hθ : ∀ x w, θ x w → agent x w) :
    ¬ AnticausativeReading M agent (anticausative M θ P) := fun h ↦
  let ⟨x, w, h₁, h₂⟩ := exists_nonagent_of_anticausativeReading h; h₂ (hθ x w h₁)

/-- Derived inchoatives license *por sí solo* ((68)). -/
theorem licensesBySelf_anticausative :
    LicensesBySelf M effector (anticausative M effector P) :=
  fun _ _ h ↦ let ⟨w, hθ, hc⟩ := exists_cause_of_anticausative h; ⟨w, hc, hθ⟩

/-! ### Comparison with previous approaches -/

-- §5.3: on a least common denominator analysis the causative is the root with a causer added
theorem causative_iff_inchoative {y x : Entity} {e : E} :
    causative M θ P y x e ↔ (∃ w, θ y w ∧ w ~[M.cause] e) ∧ inchoative M P x e :=
  (causative_iff M θ P).trans
    ⟨fun ⟨w, hθ, hc, hi⟩ ↦ ⟨⟨w, hθ, hc⟩, hi⟩, fun ⟨⟨w, hθ, hc⟩, hi⟩ ↦ ⟨w, hθ, hc, hi⟩⟩

-- §5.4: existential binding applies to a causative whatever its causer relation
theorem boundInchoative_of_causative {y x : Entity} {e : E} (h : causative M θ P y x e) :
    boundInchoative M P x e :=
  let ⟨w, _, hc, hi⟩ := (causative_iff M θ P).1 h; ⟨w, hc, hi⟩

theorem boundInchoative_of_anticausative {x : Entity} {e : E}
    (h : anticausative M θ P x e) : boundInchoative M P x e :=
  boundInchoative_of_causative h

theorem boundInchoative_of_passive {x : Entity} {e : E} (h : passive M effector P x e) :
    boundInchoative M P x e :=
  let ⟨_, hy⟩ := h; boundInchoative_of_causative hy

-- §5.2: the inchoative of a deletion analysis is entailed by the others and has no CAUSE
theorem inchoative_of_boundInchoative {x : Entity} {e : E} (h : boundInchoative M P x e) :
    inchoative M P x e :=
  let ⟨_, _, hi⟩ := h; hi

end Model

/-! ### Juan and the glass

The model of (56)–(57) and (60) has Juan break the glass. Whether the glass counts as an
effector of the causing event is a parameter; the denial in (56) has it that it does not,
the discourse in (60) that both the glass and Juan do. -/

/-- A `Participant` is one of the participants of the models. -/
inductive Participant
  | juan
  | vaso
  deriving DecidableEq

/-- In the model where Juan breaks the glass, the one event causes itself and gives rise to the
glass's broken state. -/
def breaking : ArgumentStructure.EventStructure.Model Unit Unit where
  become := ⊤
  cause := ⊤

/-- The broken state holds of the glass. -/
def broken (x : Participant) (_ : Unit) : Prop := x = .vaso

/-- Juan alone is an agent. -/
def juanAgent (y : Participant) (_ : Unit) : Prop := y = .juan

/-- On the first construal Juan, not the glass, is the effector. -/
def byJuan (y : Participant) (_ : Unit) : Prop := y = .juan

/-- On the second construal the glass and Juan are both effectors. -/
def byBoth (_ : Participant) (_ : Unit) : Prop := True

/-- `e₀` is the one event of the models. -/
def e₀ : Unit := ()

theorem not_anticausative_of_causative :
    causative breaking byJuan broken .juan .vaso e₀ ∧
      ¬ anticausative breaking byJuan broken .vaso e₀ :=
  ⟨(causative_iff _ _ _).2 ⟨e₀, rfl, trivial, (), trivial, rfl⟩,
    fun h ↦ let ⟨_, h, _⟩ := (anticausative_iff _ _ _ _ _).1 h; Participant.noConfusion h⟩

theorem anticausativeReading_romper :
    AnticausativeReading breaking juanAgent (anticausative breaking byBoth broken) :=
  ⟨.vaso, e₀, (anticausative_iff _ _ _ _ _).2 ⟨e₀, trivial, trivial, (), trivial, rfl⟩,
    fun _ _ h ↦ Participant.noConfusion h⟩

theorem not_licensesBySelf_passive :
    ¬ LicensesBySelf breaking byJuan (passive breaking byJuan broken) := fun h ↦
  let ⟨_, _, hw⟩ := h .vaso e₀ ⟨.juan, (causative_iff _ _ _).2 ⟨e₀, rfl, trivial, (), trivial, rfl⟩⟩
  Participant.noConfusion hw

-- (65), (67)
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf breaking byJuan (inchoative breaking broken) := fun h ↦
  let ⟨_, _, hw⟩ := h .vaso e₀ ⟨(), trivial, rfl⟩
  Participant.noConfusion hw

/-! ### The Monotonicity Hypothesis -/

/-- The Monotonicity Hypothesis (8) holds of a word formation operation on event templates when
the output keeps every kind of operator the input has. -/
def MonotonicityHypothesis (f : Template .event → Option (Template .event)) : Prop :=
  ∀ t t', f t = some t' → t.kinds ⊆ t'.kinds

/-- The inchoativization rule of [grimshaw-1982] ((95)) keeps the caused subevent, stripping
CAUSE and the causing subevent from an accomplishment; it violates the hypothesis. -/
theorem not_monotonicityHypothesis_caused : ¬ MonotonicityHypothesis Template.caused :=
  fun h ↦ absurd (h .accomplishment .achievement rfl) (by decide)

-- §5.3: deriving the causative from the root adds operators and removes none
theorem monotonicityHypothesis_cause_effector :
    MonotonicityHypothesis fun t ↦ some (.cause .effector t) := by
  rintro t _ ⟨rfl⟩
  simp

/-- Reflexivization on templates identifies the causer with the undergoer, so it applies
exactly to templates with CAUSE and changes no operator. -/
def reflexivizeTemplate (t : Template .event) : Option (Template .event) :=
  if .cause ∈ t.kinds then some t else none

/-- Anticausativization as reflexivization satisfies the hypothesis. -/
theorem monotonicityHypothesis_reflexivizeTemplate :
    MonotonicityHypothesis reflexivizeTemplate := by
  intro t t' h
  unfold reflexivizeTemplate at h
  split_ifs at h
  cases h
  exact Finset.Subset.refl _

/-! ### Spanish verbs -/

/-- The thematic specification of a verb's causer is an underspecified EFFECTOR or an AGENT. -/
inductive Causer
  | effector
  | agent
  deriving DecidableEq, Repr

/-- A verb's causer specification is derived from its stated proto-role subject profile. A
causer that must be an agent entails volition, one that need only cause the change is an
EFFECTOR, and a subject that causes nothing is no causer. -/
def causer (v : Verb) : Option Causer :=
  (v.slotProfile? .external).bind fun p ↦
    if .volition ∈ p then some .agent else if .causation ∈ p then some .effector else none

-- §3.1, §3.2
theorem alternates_iff_effector :
    ∀ v ∈ allVerbs, ∀ c ∈ causer v, (v.Alternates Voice.anticausative ↔ c = .effector) := by
  decide

end KoontzGarboden2009
