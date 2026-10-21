module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Basic
public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
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

## Main results

* `exists_cause_of_anticausative`: CAUSE survives reflexivization.
* `not_anticausativeReading`: an agent-causer verb has no anticausative reading.
* `licensesBySelf_anticausative`: derived inchoatives license *por sí solo*.
* `not_monotonicityHypothesis_caused`: inchoativization violates the hypothesis.
* `monotonicityHypothesis_reflexivizeTemplate`: reflexivization satisfies it.

## Implementation notes

The paper's representations take the change-of-state event as the verb's event argument and
existentially close the causing event; `causative` follows that convention, and
`exists_causative_iff` shows that its existential closure agrees with the library's causative
head `vCause`, whose event argument is the causing event. Agent entailments are an explicit
relation on the model, since `EventStructure.Interpretation` has only the underspecified `effector`.
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

namespace KoontzGarboden2009

open ArgumentStructure ArgumentStructure.EventStructure Spanish.Verbs

/-- The reflexivization operator restricts a two-place relation to its diagonal. It is the
denotation of the reflexive clitic *se*. -/
def reflexivize {α β : Type*} (R : α → α → β) : α → β := fun x ↦ R x x

section Model

variable {Entity State E : Type*}
  (M : ArgumentStructure.EventStructure.Interpretation Entity State E)
  (θ agent : Entity → E → Prop) (P : Entity → State → Prop)

/-- A causative change-of-state verb, ((10b), (17), (29)), holds of an event `e` in which `x` comes
to be in the root's state, caused by an event whose participant `y` bears the causer relation `θ`,
the underspecified `M.effector` for *romper* and an agent relation for *asesinar*. -/
def causative (y x : Entity) (e : E) : Prop :=
  ∃ w, θ y w ∧ M.cause w e ∧ M.vBecome P x e

/-- Over the underspecified causer, `causative` and an event of `y` under the head `vCause` over
`vBecome` have the same existential closure; they differ only in which event is the verb's
argument. -/
theorem exists_causative_iff (y x : Entity) :
    (∃ e, causative M M.effector P y x e) ↔ ∃ w, M.effector y w ∧ M.vCause (M.vBecome P x) w :=
  ⟨fun ⟨e, w, hθ, hc, hi⟩ ↦ ⟨w, hθ, e, hc, hi⟩, fun ⟨w, hθ, e, hc, hi⟩ ↦ ⟨e, w, hθ, hc, hi⟩⟩

/-- Anticausativization is reflexivization. The derived inchoative is the causative on its
diagonal, so the undergoer is also the participant in the causing event. -/
def anticausative : Entity → E → Prop := reflexivize (causative M θ P)

theorem anticausative_iff (x : Entity) (e : E) :
    anticausative M θ P x e ↔ ∃ w, θ x w ∧ M.cause w e ∧ M.vBecome P x e := Iff.rfl

/-- A reflexivized verb has the anticausative reading when it has an instance whose single
argument is not an agent of the event causing its change, as in *el vaso se rompió* 'the cup
broke'. -/
def AnticausativeReading (P : Entity → E → Prop) : Prop :=
  ∃ x e, P x e ∧ ∀ w, M.cause w e → ¬ agent x w

/-- *Por sí solo* 'by itself' ((54)) is licensed on a predicate that entails a causing subevent
with the subject as its effector; the modifier then adds that the subject is its sole
effector (§3.4, §4.1). -/
def LicensesBySelf (P : Entity → E → Prop) : Prop :=
  ∀ x e, P x e → ∃ w, M.cause w e ∧ M.effector x w

/-- In the passive of a causative verb the causer is existentially closed rather than
identified with the subject. -/
def passive (x : Entity) (e : E) : Prop := ∃ y, causative M M.effector P y x e

variable {M θ agent P}

/-- A derived inchoative entails the causative with its subject as its own causer, the special
kind of causative that §3.5 finds the inchoative to entail. -/
theorem causative_self_of_anticausative {x : Entity} {e : E}
    (h : anticausative M θ P x e) : causative M θ P x x e := h

/-- A derived inchoative retains a causing subevent whose causer is its subject, so CAUSE
survives reflexivization. -/
theorem exists_cause_of_anticausative {x : Entity} {e : E}
    (h : anticausative M θ P x e) : ∃ w, θ x w ∧ M.cause w e :=
  let ⟨w, hθ, hc, _⟩ := h; ⟨w, hθ, hc⟩

/-- Only verbs with a thematically underspecified causer anticausativize, since an
anticausative reading needs a causer relation satisfied by a non-agent. -/
theorem exists_nonagent_of_anticausativeReading
    (h : AnticausativeReading M agent (anticausative M θ P)) : ∃ x w, θ x w ∧ ¬ agent x w :=
  let ⟨x, _, ⟨w, hθ, hc, _⟩, hna⟩ := h; ⟨x, w, hθ, hna w hc⟩

/-- A verb whose causer must be an agent ((29), *asesinar*) reflexivizes to the reflexive-type
reading only ((27)–(28), (31)). -/
theorem not_anticausativeReading (hθ : ∀ x w, θ x w → agent x w) :
    ¬ AnticausativeReading M agent (anticausative M θ P) := fun h ↦
  let ⟨x, w, h₁, h₂⟩ := exists_nonagent_of_anticausativeReading h; h₂ (hθ x w h₁)

/-- Derived inchoatives license *por sí solo* ((68)). -/
theorem licensesBySelf_anticausative : LicensesBySelf M (anticausative M M.effector P) :=
  fun _ _ h ↦ let ⟨w, hθ, hc⟩ := exists_cause_of_anticausative h; ⟨w, hc, hθ⟩

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

/-- In the model where Juan breaks the glass, `eff` says who counts as an effector of the
causing event, and every event gives rise to the glass's broken state. -/
def breaking (eff : Participant → Prop) :
    ArgumentStructure.EventStructure.Interpretation Participant Unit Unit where
  become _ _ := True
  cause _ _ := True
  effector y _ := eff y

/-- The broken state holds of the glass. -/
def broken (x : Participant) (_ : Unit) : Prop := x = .vaso

/-- Juan alone is an agent. -/
def juanAgent (y : Participant) (_ : Unit) : Prop := y = .juan

/-- In the first model Juan, not the glass, is the effector. -/
def breakingByJuan : ArgumentStructure.EventStructure.Interpretation Participant Unit Unit :=
  breaking (· = .juan)

/-- In the second model the glass and Juan are both effectors. -/
def breakingByBoth : ArgumentStructure.EventStructure.Interpretation Participant Unit Unit :=
  breaking fun _ ↦ True

/-- `e₀` is the one event of the models. -/
def e₀ : Unit := ()

/-- The causative does not entail the derived inchoative. With Juan the only effector, *Juan
rompió el vaso* holds and *el vaso se rompió* fails. -/
theorem not_anticausative_of_causative :
    causative breakingByJuan breakingByJuan.effector broken .juan .vaso e₀ ∧
      ¬ anticausative breakingByJuan breakingByJuan.effector broken .vaso e₀ :=
  ⟨⟨e₀, rfl, trivial, (), trivial, rfl⟩, fun ⟨_, h, _⟩ ↦ Participant.noConfusion h⟩

/-- *El vaso se rompió* has the anticausative reading, the glass being a non-agentive effector
of its own breaking. -/
theorem anticausativeReading_romper :
    AnticausativeReading breakingByBoth juanAgent
      (anticausative breakingByBoth breakingByBoth.effector broken) :=
  ⟨.vaso, e₀, ⟨e₀, trivial, trivial, (), trivial, rfl⟩, fun _ _ h ↦ Participant.noConfusion h⟩

/-- A passive does not license *por sí solo*, since its subject need not be an effector of the
causing subevent. -/
theorem not_licensesBySelf_passive :
    ¬ LicensesBySelf breakingByJuan (passive breakingByJuan broken) := fun h ↦
  let ⟨_, _, hw⟩ := h .vaso e₀ ⟨.juan, e₀, rfl, trivial, (), trivial, rfl⟩
  Participant.noConfusion hw

/-- The CAUSE-less representation of an internally caused verb ((65), (67)), the head
`vBecome` alone, does not license *por sí solo*. -/
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf breakingByJuan (breakingByJuan.vBecome broken) := fun h ↦
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

/-- Reflexivization on templates identifies the causer with the undergoer, so it applies
exactly to templates with CAUSE and changes no operator. -/
def reflexivizeTemplate (t : Template .event) : Option (Template .event) :=
  if t.HasCause then some t else none

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

/-- Only causative verbs with underspecified causers have derived inchoatives (§3.1–§3.2), so
among the fragment's verbs that have a causer, the alternating ones are the EFFECTOR verbs. -/
theorem alternates_iff_effector :
    ∀ v ∈ allVerbs, ∀ c ∈ causer v.toVerb, (v.Alternates ↔ c = .effector) := by
  decide

end KoontzGarboden2009
