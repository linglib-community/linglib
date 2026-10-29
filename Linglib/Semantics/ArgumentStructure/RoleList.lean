module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole

/-!
# Argument-structure templates

This file defines role lists, the argument-structure generalizations that whole verb classes
share. A role list gives the entailment profile of a subject and of an optional object, in
realization order, and the named templates are the consensus role lists of verb classes such as
manner contact, perception, motion and the psych verbs. A verb entry takes its participants'
profiles from these templates or records its own.

## Main definitions

* `RoleList`: the entailment profiles of a subject and an optional object.
* `RoleList.args`: the profiles of a role list, subject first.

## References

* [dowty-1991]
* [levin-1993]
* [levin-rappaport-hovav-2005]
* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
* [beavers-2011]
* [belletti-rizzi-1988]
-/

@[expose] public section

namespace ArgumentStructure

/-- A verb class's role list gives the entailment profile of its subject and then of its object,
`none` for an intransitive. -/
structure RoleList where
  subjectProfile : EntailmentProfile
  objectProfile : Option EntailmentProfile := none
  deriving DecidableEq

/-- `r.args` lists the profiles of the role list, subject first, as
[levin-rappaport-hovav-2005] (ch. 2) present role lists. -/
def RoleList.args (r : RoleList) : List EntailmentProfile :=
  r.subjectProfile :: r.objectProfile.toList

/-! ### Named templates

The consensus profiles of verb classes, which studies and fragments reference. -/

/-- The activity template's subject, with volition, sentience, movement and independent existence.
Transitive activities like *hit* add causation at the class level via root-contributed objects. -/
def activitySubjectProfile : EntailmentProfile :=
  {.volition, .sentience, .movement, .independentExistence}

/-- The achievement template's subject, which moves, exists independently and undergoes a change of
state. The movement entailment fits directed-motion achievements (*arrive*) but overgeneralizes to
non-motion achievements (*recognize*, *notice*), whose subjects are sentient rather than moving;
those pattern with the psych-state templates. -/
def achievementSubjectProfile : EntailmentProfile :=
  {.movement, .independentExistence, .changeOfState}

/-- The accomplishment template's subject is a full proto-agent, the whole agent cluster: volition,
sentience, causation, movement and independent existence. Dowty confirms it at the class level: the
primary transitive verbs of [dowty-1991] (35) (*build*, *write*, *murder*, *eat*, *wash*) have
subjects with "volition, sentience, causation, and movement" and no Proto-Patient entailments
(p. 577); independent existence is the parenthesized (27e). -/
def accomplishmentSubjectProfile : EntailmentProfile := ProtoRoleFeature.agentCluster

/-- The accomplishment template's object, a result patient that changes state and is causally
affected. Dowty confirms it at the class level: the (35) objects have "change, causally affected"
(p. 577); the remaining Proto-Patient entailments are hedged there as "(mostly) incremental theme,
stationary, dependent existence", so incremental themes (*eat*, *build*) add IT per class or per
verb — not all accomplishment objects measure the event. -/
def accomplishmentObjectProfile : EntailmentProfile :=
  {.changeOfState, .causallyAffected}

/-- An experiencer is sentient with respect to the event but neither volitional nor causal
([dowty-1991] (38)), and exists independently, by Dowty's generalization that every verb entailing
any of (27a–d) also entails the existence of its subject (p. 573). -/
def experiencerProfile : EntailmentProfile :=
  {.sentience, .independentExistence}

/-- A stimulus causes the experience without being sentient with respect to it
([dowty-1991] (38)). -/
def stimulusProfile : EntailmentProfile :=
  {.causation, .independentExistence}

/-- The object of the surface-contact classes is contacted but not changed, causally affected and
stationary without a change of state. [dowty-1991] attributes no change of state to the objects of
the hit class ((64 III)), and [beavers-2011] (60c) gives impact verbs only potential for change. -/
def contactObject : EntailmentProfile :=
  {.causallyAffected, .stationary}

/-- A created object changes state, is an incremental theme, is causally affected and does not
exist before the event ([dowty-1991] (30e)(i)). -/
def creationObject : EntailmentProfile :=
  {.changeOfState, .incrementalTheme, .causallyAffected, .dependentExistence}

/-- A consumed object is like a created one but exists before the event. -/
def consumptionObject : EntailmentProfile :=
  {.changeOfState, .incrementalTheme, .causallyAffected}

/-- In manner contact a full agent acts on an object it contacts without changing it. Manner verbs
lack result entailments ([beavers-koontz-garboden-2020]). -/
def mannerContact : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- In self-propelled motion the subject moves but causes no change in another participant, and
there is no object. -/
def selfMotion : RoleList where
  subjectProfile := activitySubjectProfile

/-- In perception the subject is a sentient, independently existing experiencer, neither volitional
nor causal. -/
def perception : RoleList where
  subjectProfile := experiencerProfile
  objectProfile  := some {.independentExistence}

/-- Stimulus-experiencer psych verbs (Levin 31.1, the amuse verbs; [belletti-rizzi-1988]) have a
causal stimulus as subject and an experiencer as object, the mirror image of `psychState`. -/
def psychCausal : RoleList where
  subjectProfile := stimulusProfile
  objectProfile  := some experiencerProfile

/-- Experiencer-subject psych verbs (Levin 31.2, the admire verbs *admire, like, love, fear, envy*)
have a sentient experiencer as subject and a causing stimulus as object ([dowty-1991] (38)). They
are the mirror image of `psychCausal`, the tie in argument selection behind the *like*/*please*
doublets (§8.3). Unlike the want verbs of `desire`, their subjects are entailed to be sentient. -/
def psychState : RoleList where
  subjectProfile := experiencerProfile
  objectProfile  := some stimulusProfile

/-- Desire verbs (Levin 32.1, *covet, crave, desire, need, want*) entail only the independent
existence of their subject. [dowty-1991] (29e) *John needs a new car* is among the "verbs that
entail subject existence but have none of (a)–(d)" (p. 573), so there is no entailment of
sentience, unlike the admire class (*this situation needs a solution*). The object is de dicto or
nonspecific, and so exists dependently ((30e)). -/
def desire : RoleList where
  subjectProfile := {.independentExistence}
  objectProfile  := some {.dependentExistence}

/-- Commercial transfer of possession (*buy*, *sell*) has a volitional agent as subject without
entailed movement, since "both buyer and seller must act agentively (voluntarily)"
([dowty-1991] §3.2). Buyer and seller have identical profiles, the tie behind the *buy*/*sell*
doublet (§8.3). There is no object profile, Dowty raising a "two Themes" worry about the goods
and the currency (§3.2) and attributing no entailments to the object. The template does not
extend to the verbs of obtaining at large: Dowty counts *get* and *receive*, whose subjects need
not act or even be sentient (*The play got a good review*), among the exceptions to argument
selection (§8.4). -/
def possessionTransfer : RoleList where
  subjectProfile := {.volition, .sentience, .causation, .independentExistence}

/-- The manner subclass of the wipe verbs (Levin 10.4.1, *wipe, scrub, sweep, rub, wash*) has a
subject that only moves and exists independently, underspecified for volition, so that agentivity
is resolved pragmatically ([rappaport-hovav-levin-1998] on *sweep*, which [dowty-1991] does not
discuss). The object is contacted without an entailed change. -/
def wipeManner : RoleList where
  subjectProfile := {.movement, .independentExistence}
  objectProfile  := some contactObject

/-- The instrument subclass of the wipe verbs (Levin 10.4.2, *brush, comb, mop, vacuum*)
lexicalizes an instrument, which forces an obligatory volitional agent as subject;
[rappaport-hovav-levin-1998]'s canonical realization rule pairs instrument constants such as
*brush, hammer, saw, shovel* with the activity template. -/
def wipeInstrument : RoleList where
  subjectProfile := accomplishmentSubjectProfile
  objectProfile  := some contactObject

/-- In unaccusative directed motion the subject moves and changes location. -/
def directedMotion : RoleList where
  subjectProfile := achievementSubjectProfile

/-- Disappearance verbs (Levin 48.2, *die, disappear, expire, perish, vanish*) have a sole argument
that changes state, is causally affected and exists dependently, since the effected argument
"will not exist after the event" ([dowty-1991] (30e)(i)). -/
def disappearance : RoleList where
  subjectProfile := {.changeOfState, .causallyAffected, .dependentExistence}

/-! ### Manner roots lack result entailments -/

theorem mannerContact_object_no_cos : ∀ o ∈ mannerContact.objectProfile, .changeOfState ∉ o := by
  simp [mannerContact, contactObject]

/-! ### Derived role labels -/

theorem hit_subject_role :
    mannerContact.subjectProfile.toRole = some .agent := by decide

theorem hit_object_role :
    contactObject.toRole = some .patient := by decide

theorem selfMotion_subject_role :
    selfMotion.subjectProfile.toRole = some .agent := by decide

theorem perception_subject_role :
    perception.subjectProfile.toRole = some .experiencer := by decide

theorem psychCausal_subject_role :
    psychCausal.subjectProfile.toRole = some .stimulus := by decide

theorem directedMotion_subject_role :
    directedMotion.subjectProfile.toRole = some .theme := by decide

/-- The admire class's stimulus object is exactly the amuse class's subject ([dowty-1991] (38)). -/
theorem psychState_mirrors_psychCausal :
    psychState.subjectProfile.toRole = some .experiencer ∧
    psychState.objectProfile = some psychCausal.subjectProfile ∧
    psychCausal.objectProfile = some psychState.subjectProfile := by decide

theorem disappearance_subject_role :
    disappearance.subjectProfile.toRole = some .patient := by decide

end ArgumentStructure
