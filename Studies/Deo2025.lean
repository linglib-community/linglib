module

public import Linglib.Discourse.Commitment.Preferential
public import Linglib.Discourse.Role
public import Linglib.Data.Examples.Deo2025

/-!
# Deo (2025): Take on this commitment: the particle *bərə* in Marathi

This file formalizes [deo-2025-bara]'s analysis of the Marathi utterance-final particle *bərə*
in declaratives and imperatives. The particle turns a declarative into a warning, a piece of
advice or a reminder and an imperative into a command, a warning or a strong recommendation,
(1) to (8) and (12) to (15), and is out in a commissive and in the response to one, (9) and
(16), and in the imperatives of requests, pleas, offers, permissions, concessions and curses,
(10) and (11). The analysis is set in a commitment-based theory of sentential force
([gunlogson-2001], [farkas-bruce-2010], [condoravdi-lauer-2012]): the discourse commitments of
a participant are doxastic or preferential, (17a), the common ground and the joint preferences
are their intersections across participants, (17b) and (17c), and a declarative or an
imperative commits the speaker to its content under the one attitude or the other, (18).
[gunlogson-2008]'s distinction between the participant who is the source of a commitment and
one who is a dependent, taking it on from the other party's testimony or expressed preference,
is extended to preferential commitments, §3.2. *Bərə* adds a commitment of its own, (20): the
speaker's preferential commitment to the addressee's dependent uptake of the content. Its
felicity condition, (21), is that the speaker takes the uptake to be a precondition for an
addressee-benefiting goal among the speaker's effective preferences and, §3.3, that nothing
shows the addressee's action choices already aligned with the goal. The profile follows, §3.4:
when the addressee is manifestly a source for the content, the uptake is unrealizable and the
*bərə* commitment cannot be sincere, which excludes permissions, concessions, commissives and
their responses, and the revealed preference of (15); an offer or invitation leaves the choice
to the addressee, against the preference for dependent uptake; a request, a plea or a curse
serves no addressee-benefiting goal; and the warning of (5a) meets the felicity condition where
(5b), whose content is one way among many to the goal, does not.

## Implementation notes

The commitment state is indexed by worlds, as in `CondoravdiLauer2012.imp`, so that the uptake
of a content is a proposition, the worlds at which the addressee is a dependent for it. Being a
source for a content, the paper's `DC_x^ind`, is having a commitment of one's own to it under
either attitude, and being a dependent is having a commitment to it on the other party's word
and none of one's own; `Commitment.Source` supplies the coordinate. The paper's effective
preferences `EP(s, w)` are `Desire.Preferential.Want` and the sincerity of the *bərə*
commitment is `Commitment.Sincere`, so that its infelicity under a manifest addressee
commitment is the unrealizability of the uptake, `PreferenceStructure.Consistent.realistic`,
relative to the speaker's information state `B` as in `Studies/CondoravdiLauer2012.lean`. Whom
a goal benefits is a primitive of the context, as in the paper, and the salient goal is a
parameter of the felicity condition. An offer or invitation is rendered as the speaker's
effective preference that any commitment of the addressee to the content be the addressee's
own, the paper's one-line derivation. The speaker's authority over the addressee, §2.2, does no
work in the paper's derivations and is not modeled; the wh-interrogative use, (3), and the
compound *bərə ka*, §4, are outside the paper's analysis.

## TODO

* The threat commissives of fn. 14 allow *bərə*; the paper leaves them unexplained.

## References

* [deo-2025-bara]
* [condoravdi-lauer-2012]
* [gunlogson-2001]
* [gunlogson-2008]
* [farkas-bruce-2010]
* [rudin-2018]
-/

@[expose] public section

namespace Deo2025

open Commitment Desire.Preferential Discourse

variable {W : Type*}

/-! ### Sources and dependents, (17) and §3.2 -/

/-- `x` is a source for `p` in `K`: a commitment of `x`'s own to `p` under either attitude,
`p ∈ DC_x^ind`. -/
def IsSource (K : State Role W) (x : Role) (p : Set W) : Prop :=
  ∃ f, commit x p f .selfGenerated ∈ K

/-- `x` is a dependent for `p` under the attitude `f` in `K`: a commitment to `p` on the other
party's testimony or expressed preference, and none of `x`'s own, `p ∈ DC_x^dep`. -/
def IsDependent (K : State Role W) (x : Role) (p : Set W) (f : Force) : Prop :=
  commit x p f .otherGenerated ∈ K ∧ ¬ IsSource K x p

/-- The contents every participant is committed to under `f`: the common ground for `.doxastic`
and the joint preferences for `.preferential`, (17b) and (17c), [rudin-2018]'s teleological
common ground. -/
def joint (K : State Role W) (f : Force) : Set (Set W) :=
  ⋂ x, contents (ofForce (ofCommitter K x) f)

/-! ### The conventions, (18) and (20) -/

variable (P : Role → W → PreferenceStructure W) (K : W → State Role W) (B : Set W)
  (benefits : Set W → Role → Prop) (g p : Set W) (f : Force) (w : W)

/-- The uptake of `p` under `f`: the worlds at which `p` is among the addressee's dependent
commitments, what the speaker prefers in (20). -/
def uptake : Set W := {v | IsDependent (K v) .addressee p f}

/-- Uttering `p` in a clause of force `f` at `w`, (18): a declarative commits the speaker to `p`
doxastically and an imperative preferentially. -/
def utter : State Role W := insert (commit .speaker p f) (K w)

/-- Uttering `p` in a clause of force `f` with *bərə* at `w`: the clause-type commitment and,
over and above it, the speaker's preferential commitment to the uptake of `p`, (20). -/
def bara : State Role W := insert (commit .speaker (uptake K p f) .preferential) (utter K p f w)

/-- *Bərə* augments the force rather than modifying it, §4: whatever the plain utterance
entails, the *bərə*-utterance entails. -/
theorem slate_bara_le : slate (bara K p f w) ≤ slate (utter K p f w) :=
  slate_mono (Set.subset_insert _ _)

/-- *Bərə*'s own effect: the preferential context set narrows by the uptake and the doxastic one
stays. -/
theorem bara_contextSets :
    contextSet (ofForce (bara K p f w) .preferential) =
        uptake K p f ∩ contextSet (ofForce (utter K p f w) .preferential) ∧
      contextSet (ofForce (bara K p f w) .doxastic) =
        contextSet (ofForce (utter K p f w) .doxastic) :=
  ⟨contextSet_ofForce_insert_of_eq_of_commit rfl rfl, contextSet_ofForce_insert_of_ne nofun⟩

/-- A *bərə*-declarative, (22): the speaker believes the content and prefers its uptake. -/
theorem declarative_contextSets :
    contextSet (ofForce (bara K p .doxastic w) .doxastic) =
        p ∩ contextSet (ofForce (K w) .doxastic) ∧
      contextSet (ofForce (bara K p .doxastic w) .preferential) =
        uptake K p .doxastic ∩ contextSet (ofForce (K w) .preferential) :=
  ⟨(bara_contextSets K p .doxastic w).2.trans (contextSet_ofForce_insert_of_eq_of_commit rfl rfl),
    (bara_contextSets K p .doxastic w).1.trans
      (congrArg _ (contextSet_ofForce_insert_of_ne nofun))⟩

/-- A *bərə*-imperative, (23): the speaker prefers the content and its uptake and believes
nothing new. -/
theorem imperative_contextSets :
    contextSet (ofForce (bara K p .preferential w) .preferential) =
        uptake K p .preferential ∩ (p ∩ contextSet (ofForce (K w) .preferential)) ∧
      contextSet (ofForce (bara K p .preferential w) .doxastic) =
        contextSet (ofForce (K w) .doxastic) :=
  ⟨(bara_contextSets K p .preferential w).1.trans
      (congrArg _ (contextSet_ofForce_insert_of_eq_of_commit rfl rfl)),
    (bara_contextSets K p .preferential w).2.trans (contextSet_ofForce_insert_of_ne nofun)⟩

/-- Once the addressee takes up the content of a *bərə*-utterance, dependently or not, it joins
the joint commitments under its attitude, §4: the implicit preference that *bərə* makes
explicit. -/
theorem mem_joint_insert (s : Commitment.Source) :
    p ∈ joint (insert (commit .addressee p f s) (bara K p f w)) f :=
  Set.mem_iInter.2 λ x => match x with
    | .speaker => ⟨commit .speaker p f, ⟨⟨⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩, rfl⟩, rfl⟩, rfl⟩
    | .addressee => ⟨commit .addressee p f s, ⟨⟨⟨Or.inl rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-! ### Felicity, (21) and §3.3 -/

/-- The felicity condition on *bərə*, (21) with the contextual condition of §3.3, at `w` in a
context with the speaker's information state `B`, the salient goal `g` and the primitive
`benefits`: the speaker's preferential commitments are sincere; `g` is an effective preference
of the speaker's that benefits the addressee and, by the speaker's information, is fulfilled
only if the addressee takes up `p`; and the speaker's information does not already have the
addressee taking up `p`. A content the addressee is taken to have taken up already, (7) in its
first context, fails the last clause. -/
def Felicitous : Prop :=
  Sincere P (bara K p f w) w ∧ Want P .speaker g w ∧ benefits g .addressee ∧
    B ∩ g ⊆ uptake K p f ∧ ¬ B ⊆ uptake K p f

/-- An offer or invitation leaves the choice to the addressee: the speaker effectively prefers
that any commitment of the addressee to `p` be the addressee's own, the complement of the
uptake. -/
def Defers : Prop := Want P .speaker (uptake K p f)ᶜ w

variable {P K B benefits g p f w}

/-- A sincere *bərə*-utterance is an effective preference for the uptake. -/
theorem want_uptake_of_sincere (h : Sincere P (bara K p f w) w) :
    Want P .speaker (uptake K p f) w :=
  h.want (Set.mem_insert _ _)

/-- The *bərə*-utterance is sincere when the speaker effectively prefers the uptake, prefers the
content if the clause is an imperative, and was sincere before. -/
theorem sincere_bara_iff :
    Sincere P (bara K p f w) w ↔ Want P .speaker (uptake K p f) w ∧
      (f = .preferential → Want P .speaker p w) ∧ Sincere P (K w) w := by
  refine ⟨λ h => ⟨want_uptake_of_sincere h, λ hf => h _ (Or.inr (Or.inl rfl)) hf rfl,
    h.mono ((Set.subset_insert _ _).trans (Set.subset_insert _ _))⟩, λ ⟨hu, hp, hK⟩ => ?_⟩
  rintro c (rfl | rfl | hc) hf hpol
  · exact hu
  · exact hp hf
  · exact hK c hc hf hpol

theorem inter_uptake_eq_empty (h : ∀ v ∈ B, IsSource (K v) .addressee p) :
    B ∩ uptake K p f = ∅ :=
  Set.eq_empty_of_forall_notMem λ v hv => hv.2.2 (h v hv.1)

/-- A manifest commitment of the addressee, §3.4: with the addressee already a source for `p` by
the speaker's information, a sincere *bərə* commitment would be an effective preference for the
unrealizable, against the consistency of the speaker's effective preferences, so *bərə* is out:
a permission or concession, (11b) and (11c), the revealed preference of (15), a commissive, (9),
and the response to one, (16). -/
theorem not_felicitous_of_isSource (benefits : Set W → Role → Prop) (g : Set W) (f : Force)
    (hC : (P .speaker w).Consistent B) (h : ∀ v ∈ B, IsSource (K v) .addressee p) :
    ¬ Felicitous P K B benefits g p f w :=
  λ hf => hC.realistic _ (want_uptake_of_sincere hf.1).1
    (by rw [Set.inter_comm]; exact inter_uptake_eq_empty h)

/-- Deference, §3.4: the preference for dependent uptake and the preference that leaves the
choice to the addressee are not jointly realizable, so *bərə* is out in an offer or invitation,
(11a). -/
theorem not_felicitous_of_defers (benefits : Set W → Role → Prop) (g : Set W)
    (hC : (P .speaker w).Consistent B) (h : Defers P K p f w) :
    ¬ Felicitous P K B benefits g p f w :=
  λ hf => (hC.inter_inter_nonempty_of_mem_maxElts (want_uptake_of_sincere hf.1) h).ne_empty
    (by rw [Set.inter_compl_self, Set.inter_empty])

/-- A goal that does not benefit the addressee, §3.4: a request or plea serves the speaker
alone, (10), and a curse harms the addressee, (11d). -/
theorem not_felicitous_of_not_benefits (P : Role → W → PreferenceStructure W)
    (K : W → State Role W) (B p : Set W) (f : Force) (w : W) (h : ¬ benefits g .addressee) :
    ¬ Felicitous P K B benefits g p f w :=
  λ hf => h hf.2.2.1

/-! ### The warning of (5): a precondition against a way among many -/

/-- A world of the scenario of (5): whether it rains today, whether tomorrow is sunny, whether
Anu drives today, and whether she has taken up, on Bilal's word, each of the two weather
facts. -/
structure Weather where
  /-- It rains today. -/
  rain : Bool
  /-- Tomorrow is sunny. -/
  sunny : Bool
  /-- Anu drives today. -/
  drives : Bool
  /-- Anu has taken up on Bilal's word that it rains today. -/
  upRain : Bool
  /-- Anu has taken up on Bilal's word that tomorrow is sunny. -/
  upSunny : Bool
  deriving DecidableEq

namespace Weather

/-- The content of (5a): it rains today. -/
def raining : Set Weather := {v | v.rain}

/-- The content of (5b): tomorrow is sunny. -/
def sunnyTomorrow : Set Weather := {v | v.sunny}

/-- Bilal's goal: Anu stays safe, not driving today. -/
def safe : Set Weather := {v | ¬ v.drives}

/-- The addressee's dependent doxastic commitments at a world: to whichever weather facts she has
taken up. -/
def state (v : Weather) : State Role Weather :=
  {c | c.committer = .addressee ∧ c.stance = .commit ∧ c.force = .doxastic ∧
    c.source = .otherGenerated ∧
    ((c.content = raining ∧ v.upRain) ∨ (c.content = sunnyTomorrow ∧ v.upSunny))}

/-- Bilal's information: the weather facts, and that Anu stays home only if she takes his word on
the rain. -/
def info : Set Weather := {v | v.rain ∧ v.sunny ∧ (¬ v.drives → v.upRain)}

/-- Bilal effectively prefers that Anu take up the rain and that she be safe; Anu's preferences
play no part. -/
def prefs : Role → Weather → PreferenceStructure Weather
  | .speaker, _ => .discrete {uptake state raining .doxastic, safe}
  | .addressee, _ => .discrete ∅

/-- Staying safe is what benefits anyone here. -/
def benefit (q : Set Weather) (_ : Role) : Prop := q = safe

/-- The world of utterance: it rains, tomorrow is sunny, Anu is set to drive and has taken up
neither fact. -/
def w₀ : Weather := ⟨true, true, true, false, false⟩

theorem raining_ne_sunnyTomorrow : raining ≠ sunnyTomorrow := λ h => by
  simpa [raining, sunnyTomorrow] using Set.ext_iff.1 h ⟨true, false, false, false, false⟩

theorem not_isSource (v : Weather) (q : Set Weather) : ¬ IsSource (state v) .addressee q :=
  λ ⟨_, h⟩ => by simp [state] at h

theorem mem_state_raining {v : Weather} :
    commit .addressee raining .doxastic .otherGenerated ∈ state v ↔ v.upRain := by
  simp [state, raining_ne_sunnyTomorrow]

theorem mem_state_sunnyTomorrow {v : Weather} :
    commit .addressee sunnyTomorrow .doxastic .otherGenerated ∈ state v ↔ v.upSunny := by
  simp [state, raining_ne_sunnyTomorrow.symm]

theorem mem_uptake_raining {v : Weather} : v ∈ uptake state raining .doxastic ↔ v.upRain := by
  simp [uptake, IsDependent, mem_state_raining, not_isSource]

theorem mem_uptake_sunnyTomorrow {v : Weather} :
    v ∈ uptake state sunnyTomorrow .doxastic ↔ v.upSunny := by
  simp [uptake, IsDependent, mem_state_sunnyTomorrow, not_isSource]

/-- The warning of (5a) is felicitous: by Bilal's information Anu stays safe only if she takes his
word on the rain, and she may yet drive without doing so. -/
theorem felicitous_raining : Felicitous prefs state info benefit safe raining .doxastic w₀ := by
  refine ⟨sincere_bara_iff.2 ⟨⟨Or.inl rfl, λ _ _ h => h⟩, nofun, λ c hc hf _ =>
    absurd (hc.2.2.1.symm.trans hf) nofun⟩, ⟨Or.inr rfl, λ _ _ h => h⟩, rfl, ?_, ?_⟩
  · rintro v ⟨⟨-, -, hv⟩, hs⟩
    exact mem_uptake_raining.2 (hv hs)
  · intro h
    simpa [w₀] using mem_uptake_raining.1 (h (show w₀ ∈ info from ⟨rfl, rfl, λ h => (h rfl).elim⟩))

/-- (5b) is not: Anu can stay safe without taking Bilal's word on tomorrow's weather. -/
theorem not_felicitous_sunnyTomorrow :
    ¬ Felicitous prefs state info benefit safe sunnyTomorrow .doxastic w₀ := λ h => by
  have hv : (⟨true, true, false, true, false⟩ : Weather) ∈ info ∩ safe :=
    ⟨⟨rfl, rfl, λ _ => rfl⟩, Bool.false_ne_true⟩
  simpa [mem_uptake_sunnyTomorrow] using h.2.2.2.1 hv

end Weather

/-! ### The recommendation of (15): a latent against a revealed preference -/

/-- A world of the scenario of (15): whether Bilal takes the car and whether he has taken up
doing so on Anu's proposal. -/
structure Car where
  /-- Bilal takes the car. -/
  takes : Bool
  /-- Bilal has taken up taking the car on Anu's proposal. -/
  up : Bool
  deriving DecidableEq

namespace Car

/-- The content of (15): Bilal takes the car today. -/
def taking : Set Car := {v | v.takes}

/-- The first context: Bilal's only commitment to taking the car, when he has one, is dependent
on Anu's proposal. -/
def latent (v : Car) : State Role Car :=
  {c | c.committer = .addressee ∧ c.stance = .commit ∧ c.force = .preferential ∧
    c.source = .otherGenerated ∧ c.content = taking ∧ v.up}

/-- The second context: Bilal has revealed his preference for taking the car. -/
def revealed (v : Car) : State Role Car :=
  insert (commit .addressee taking .preferential) (latent v)

/-- Anu's information: Bilal takes the car only on her proposal. -/
def info : Set Car := {v | v.takes → v.up}

/-- Anu effectively prefers that Bilal take the car and take it up from her; Bilal prefers to
take the car, a preference he has not revealed. -/
def prefs : Role → Car → PreferenceStructure Car
  | .speaker, _ => .discrete {uptake latent taking .preferential, taking}
  | .addressee, _ => .single taking

/-- Making the meeting is what benefits anyone here. -/
def benefit (q : Set Car) (_ : Role) : Prop := q = taking

/-- The world of utterance: Bilal has neither taken the car nor taken up doing so. -/
def w₀ : Car := ⟨false, false⟩

theorem not_isSource (v : Car) (q : Set Car) : ¬ IsSource (latent v) .addressee q :=
  λ ⟨_, h⟩ => by simp [latent] at h

theorem mem_latent {v : Car} :
    commit .addressee taking .preferential .otherGenerated ∈ latent v ↔ v.up := by
  simp [latent]

theorem mem_uptake {v : Car} : v ∈ uptake latent taking .preferential ↔ v.up := by
  simp [uptake, IsDependent, mem_latent, not_isSource]

/-- The first context of (15): Bilal's preference for the car is latent, and the recommendation
with *bərə* is felicitous. -/
theorem felicitous_latent :
    Felicitous prefs latent info benefit taking taking .preferential w₀ ∧
      Want prefs .addressee taking w₀ := by
  refine ⟨⟨sincere_bara_iff.2 ⟨⟨Or.inl rfl, λ _ _ h => h⟩, λ _ => ⟨Or.inr rfl, λ _ _ h => h⟩,
    λ c hc _ _ => absurd hc.2.2.2.2.2 Bool.false_ne_true⟩, ⟨Or.inr rfl, λ _ _ h => h⟩, rfl,
    λ v hv => mem_uptake.2 (hv.1 hv.2), λ h => ?_⟩, ⟨rfl, λ _ _ h => h⟩⟩
  simpa [w₀] using mem_uptake.1 (h (show w₀ ∈ info from λ h => h))

/-- The second context of (15): Bilal has revealed his preference and is a source for the
content, so under any consistent effective preferences of Anu's *bərə* is out. -/
theorem not_felicitous_revealed (P : Role → Car → PreferenceStructure Car)
    (hC : (P .speaker w₀).Consistent info) :
    ¬ Felicitous P revealed info benefit taking taking .preferential w₀ :=
  not_felicitous_of_isSource _ _ _ hC λ _ _ => ⟨.preferential, Or.inl rfl⟩

end Car

end Deo2025
