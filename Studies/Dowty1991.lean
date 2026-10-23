module

public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Data.Examples.Dowty1991
public import Studies.Cruse1973

/-!
# Dowty (1991): Thematic proto-roles and argument selection

Dowty replaces thematic roles by two cluster concepts, the Proto-Agent and the Proto-Patient,
each a list of five entailments a predicate may impose on an argument, (27) and (28). The
Argument Selection Principle (31) lexicalizes as subject the argument with the most
Proto-Agent entailments and as direct object the one with the most Proto-Patient entailments.
Every argument profile here is read off a row of `Data/Examples/Dowty1991.json`, from the
single-entailment exemplars of (29) and (30) to the three verb classes of (64).

## Main results

* `cruse_volitive_is_volition_alone`: Dowty's exemplar of volition alone is Cruse's volitive
  doer.
* `alternates_iff`, `hierarchies`: Corollary 1 is the failure of (31) to select either way, and
  the role hierarchies of (36) follow from the principle.
* `primary_transitives`, `buy_sell`, `psych_doublet`: the primary transitive verbs of (35) are
  selected outright, while *buy* and *sell* and *like* and *please* tie.
* `directObjectOver_of_changeOfState`, `three_classes`: a change of state entailed for one
  nonsubject argument alone fixes it as direct object, so of the three classes of (64) only the
  break class does not alternate.
* `intransClass_unergative`, `intransClass_unaccusative`: the pure cells of Table 1.
* `primary_transitives_match_templates`: the substrate's class templates agree with the paper's
  attributions, save at two deliberate divergences.

## Implementation notes

A row attributes some entailments to its argument and denies others; the profiles agreeing with
it form the interval between the two, and the profile the principle compares is the bottom of that
interval, so counts are of stated entailments; the parenthesized (27e) and (28e) count like the
others. `Outranks` reads the Proto-Agent clause of (31) first and lets the
Proto-Patient clause decide ties, and "approximately equal" in the corollaries is read as equal.
The incremental theme homomorphism of §6 and the material of §11 are not represented.

## References

* [dowty-1991]
* [cruse-1973]
* [fillmore-1968]
-/

@[expose] public section

namespace Dowty1991

open ArgumentStructure
open scoped Finset

/-! ### What a row attributes -/

/-- The entailments by their `paperFeatures` labels. -/
def featureLabels : List (String × ProtoRoleFeature) :=
  [("volition", .volition), ("sentience", .sentience), ("causation", .causation),
   ("movement", .movement), ("independentExistence", .independentExistence),
   ("changeOfState", .changeOfState), ("incrementalTheme", .incrementalTheme),
   ("causallyAffected", .causallyAffected), ("stationary", .stationary),
   ("dependentExistence", .dependentExistence)]

/-- The entailments a row attributes to its argument. -/
def entailed (e : Datum) : EntailmentProfile :=
  ((e.features "entails").filterMap (List.lookup · featureLabels)).toFinset

/-- The entailments a row denies of its argument. -/
def denied (e : Datum) : EntailmentProfile :=
  ((e.features "denies").filterMap (List.lookup · featureLabels)).toFinset

theorem lookup_isSome : ∀ e ∈ Examples.all, ∀ s ∈ e.features "entails" ++ e.features "denies",
    (List.lookup s featureLabels).isSome := by
  decide

theorem disjoint_entailed_denied : ∀ e ∈ Examples.all, Disjoint (entailed e) (denied e) := by
  decide

/-- A profile agrees with a row when it imposes every entailment the row attributes and none it
denies, so that the profiles agreeing with a row form an interval; what the row leaves open is
unconstrained. -/
def Matches (e : Datum) (p : EntailmentProfile) : Prop := p ∈ Set.Icc (entailed e) (denied e)ᶜ

instance (e : Datum) (p : EntailmentProfile) : Decidable (Matches e p) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

theorem matches_entailed {e : Datum} (h : Disjoint (entailed e) (denied e)) :
    Matches e (entailed e) :=
  ⟨le_rfl, h.le_compl_right⟩

/-- Dowty's exemplar of volition alone (29a) is Cruse's (32), and the two analyses agree on it:
Dowty attributes volition alone to its subject, and Cruse the volitive alone. -/
theorem cruse_volitive_is_volition_alone :
    entailed Examples.notEatSubject = {.volition} ∧
      (Cruse1973.Row.ofDatum Cruse1973.Examples.ex_32).bind (·.profile) = some {.volitive} := by
  decide

/-! ### The selection principle and its corollaries, (31) to (34) -/

variable (p q : EntailmentProfile)

/-- By the selection principle (31), `p` is lexicalized as subject over `q` when it has strictly
more Proto-Agent entailments, or as many and strictly fewer Proto-Patient entailments. -/
def Outranks : Prop :=
  #q.protoAgent < #p.protoAgent ∨
    (#p.protoAgent = #q.protoAgent ∧ #p.protoPatient < #q.protoPatient)

/-- Two arguments with equal counts may be lexicalized either way, Corollary 1 (32). -/
def Alternates : Prop := #p.protoAgent = #q.protoAgent ∧ #p.protoPatient = #q.protoPatient

/-- Of two nonsubject arguments, the one with more Proto-Patient entailments is lexicalized as
direct object and the other as oblique, Corollary 2 (33). -/
def DirectObjectOver : Prop := #q.protoPatient < #p.protoPatient

/-- Two nonsubject arguments with equal Proto-Patient counts may either be direct object
(33). -/
def EitherObject : Prop := #p.protoPatient = #q.protoPatient

instance : Decidable (Outranks p q) := by unfold Outranks; infer_instance
instance : Decidable (Alternates p q) := by unfold Alternates; infer_instance
instance : Decidable (DirectObjectOver p q) := by unfold DirectObjectOver; infer_instance
instance : Decidable (EitherObject p q) := by unfold EitherObject; infer_instance

/-- Corollary 1 is exactly the failure of (31) to select either way. -/
theorem alternates_iff : Alternates p q ↔ ¬ Outranks p q ∧ ¬ Outranks q p := by
  unfold Alternates Outranks; omega

/-- The principle does not select uniquely (34): a profile ties with itself, so a relation
lexicalized twice with the arguments swapped is licensed. -/
theorem alternates_self : Alternates p p := ⟨rfl, rfl⟩

/-- One Proto-Agent entailment against none qualifies an argument for subject (§8.2). -/
theorem outranks_of_protoAgent_nonempty (hp : p.protoAgent.Nonempty) (hq : q.protoAgent = ∅) :
    Outranks p q :=
  .inl (by simpa [hq] using hp.card_pos)

/-- The hierarchies of (36) fall out of the principle over the canonical role profiles:
Agent over Instrument, Instrument and Experiencer over Patient, and Patient over Goal for
direct object. -/
theorem hierarchies :
    Outranks (ThetaRole.canonicalProfile .agent) (ThetaRole.canonicalProfile .instrument) ∧
      Outranks (ThetaRole.canonicalProfile .instrument) (ThetaRole.canonicalProfile .patient) ∧
      Outranks (ThetaRole.canonicalProfile .experiencer)
        (ThetaRole.canonicalProfile .patient) ∧
      DirectObjectOver (ThetaRole.canonicalProfile .patient)
        (ThetaRole.canonicalProfile .goal) := by
  decide

/-! ### The stable case and the ties, (35) and §8.3 -/

/-- In the primary transitive verbs of (35) a subject with four Proto-Agent entailments and no
Proto-Patient entailment faces an object with the reverse, and (31) selects outright. -/
theorem primary_transitives :
    Outranks (entailed Examples.buildSubject) (entailed Examples.buildObject) ∧
      Outranks (entailed Examples.writeSubject) (entailed Examples.writeObject) ∧
      Outranks (entailed Examples.murderSubject) (entailed Examples.murderObject) ∧
      Outranks (entailed Examples.eatSubject) (entailed Examples.eatObject) ∧
      Outranks (entailed Examples.washSubject) (entailed Examples.washObject) := by
  decide

/-- By Corollary 2, the theme of *put* and *remove*, changed and affected, outranks the
stationary goal or source for direct object (§8.2). -/
theorem put_remove :
    DirectObjectOver (entailed Examples.putTheme) (entailed Examples.putGoal) ∧
      DirectObjectOver (entailed Examples.removeTheme) (entailed Examples.removeSource) := by
  decide

/-- Buyer and seller are both volitional and otherwise alike, so *buy* and *sell* are licensed
as a doublet (§3.2, §8.3). -/
theorem buy_sell : Alternates (entailed Examples.buySubject) (entailed Examples.buySeller) ∧
    Alternates (entailed Examples.sellSubject) (entailed Examples.sellBuyer) := by
  decide

/-- The experiencer is sentient and the stimulus causal, one Proto-Agent entailment each, so
*like* and *please* tie (38). -/
theorem psych_doublet :
    Alternates (entailed Examples.likeSubject) (entailed Examples.likeObject) ∧
      Alternates (entailed Examples.pleaseObject) (entailed Examples.pleaseSubject) := by
  decide

/-- Under the inchoative interpretation the experiencer undergoes a change of state, the
Proto-Patient entailment that selects the stimulus as subject, which is Croft's generalization
that only stimulus-subject psych verbs take the inchoative reading (§9.2). -/
theorem inchoative_stimulus_subject :
    Outranks (entailed Examples.surpriseSubject) (entailed Examples.surpriseObjectInchoative) := by
  decide

/-! ### Partially symmetric interactive predicates, §9.1 -/

/-- The subject of *kiss*, entailed volitional. -/
def kissSubjectProfile : EntailmentProfile := entailed Examples.kissSubject

/-- The object of *kiss*, not entailed volitional. -/
def kissObjectProfile : EntailmentProfile := entailed Examples.kissObject

/-- Volition, entailed for the subject alone, selects it, (43); with symmetric volition the
collective subject of (42) is a tie. -/
theorem kiss_subject_outranks :
    Outranks kissSubjectProfile kissObjectProfile ∧
      Alternates kissSubjectProfile kissSubjectProfile := by
  decide

/-- The entailment distinguishing the subject of *collide* from its oblique is motion, not
volition (45). -/
theorem collide_subject_outranks :
    Outranks (entailed Examples.collideSubject) (entailed Examples.collideObject) := by
  decide

/-! ### Alternations in direct versus oblique objects, §9.3 and (64) -/

/-- Two nonsubject arguments agree on the change-of-state entailment. -/
def CosSymmetric : Prop := .changeOfState ∈ p ↔ .changeOfState ∈ q

instance : Decidable (CosSymmetric p q) := by unfold CosSymmetric; infer_instance

/-- A change of state entailed for one nonsubject argument but not the other, the remaining
Proto-Patient entailments being equal, fixes it as direct object (§9.3.3). -/
theorem directObjectOver_of_changeOfState (hp : .changeOfState ∈ p) (hq : .changeOfState ∉ q)
    (h : p.protoPatient.erase .changeOfState = q.protoPatient.erase .changeOfState) :
    DirectObjectOver p q := by
  have hp' : .changeOfState ∈ p.protoPatient := Finset.mem_inter.2 ⟨hp, by decide⟩
  have hq' : .changeOfState ∉ q.protoPatient := fun h ↦ hq (Finset.mem_inter.1 h).1
  unfold DirectObjectOver
  rw [← Finset.card_erase_add_one hp', h, Finset.erase_eq_of_notMem hq']
  omega

theorem eitherObject_of_cosSymmetric (h : CosSymmetric p q)
    (h' : p.protoPatient.erase .changeOfState = q.protoPatient.erase .changeOfState) :
    EitherObject p q := by
  have : p.protoPatient = q.protoPatient := by
    ext f
    by_cases hf : f = .changeOfState
    · subst hf
      simp only [EntailmentProfile.protoPatient, Finset.mem_inter]
      exact and_congr_left fun _ ↦ h
    · simpa [hf] using congrArg (f ∈ ·) h'
  unfold EitherObject; rw [this]

/-- The hay and the truck of (49), (64 I), which both change state. -/
def sprayLoadTheme : EntailmentProfile := entailed Examples.loadTheme

def sprayLoadLocation : EntailmentProfile := entailed Examples.loadLocation

/-- The fence and the stick of (63), (64 II), of which only the direct object changes state. -/
def breakDirectObject : EntailmentProfile := entailed Examples.breakObject

def breakInstrument : EntailmentProfile := entailed Examples.breakInstrument

/-- The fence and the stick of (62), (64 III), neither of which changes state or measures the
event. -/
def hitArg1 : EntailmentProfile := entailed Examples.hitObject

def hitArg2 : EntailmentProfile := entailed Examples.hitInstrument

/-- The spray/load class alternates, the break class fixes its direct object, and the hit class
alternates with complete synonymy (64). -/
theorem three_classes :
    EitherObject sprayLoadTheme sprayLoadLocation ∧
      DirectObjectOver breakDirectObject breakInstrument ∧
      EitherObject hitArg1 hitArg2 := by
  decide

/-- In the hit class puzzle the instrument moves, a Proto-Agent entailment the principle leaves
out of object selection (§9.3.3). -/
theorem hit_instrument_moves : #hitArg2.protoAgent = 1 ∧ #hitArg1.protoAgent = 0 := by
  decide

/-! ### The unaccusative hypothesis, §12 -/

/-- The three cases of Table 1, the two pure cells and the two mixed cells that vary across
languages. -/
inductive IntransClass
  | unergative
  | unaccusative
  | unstable
  deriving DecidableEq, Repr

/-- Table 1 crosses agentivity with telicity. -/
def table1 : Bool → Bool → IntransClass
  | true, false => .unergative
  | false, true => .unaccusative
  | _, _ => .unstable

/-- The most important Proto-Agent entailment for the contrast: volition. -/
def Agentive : Prop := .volition ∈ p

/-- The most important Proto-Patient property for the contrast: an incremental or holistic
theme, that is, telicity. -/
def Telic : Prop := .incrementalTheme ∈ p ∨ .changeOfState ∈ p

instance : DecidablePred Agentive := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

instance : DecidablePred Telic := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The class Table 1 assigns to an intransitive by its sole argument's profile. -/
def intransClass : IntransClass := table1 (decide (Agentive p)) (decide (Telic p))

theorem intransClass_unergative (h : Agentive p) (h' : ¬ Telic p) :
    intransClass p = .unergative := by
  simp only [intransClass, decide_eq_true h, decide_eq_false h', table1]

theorem intransClass_unaccusative (h : ¬ Agentive p) (h' : Telic p) :
    intransClass p = .unaccusative := by
  simp only [intransClass, decide_eq_false h, decide_eq_true h', table1]

theorem intransClass_examples :
    intransClass selfMotion.subjectProfile = .unergative ∧
      intransClass disappearance.subjectProfile = .unaccusative ∧
      intransClass directedMotion.subjectProfile = .unaccusative := by
  decide

/-! ### The substrate's templates against the paper's attributions -/

/-- The (35) attributions hold of the accomplishment templates and the creation and
consumption objects. -/
theorem primary_transitives_match_templates :
    Matches Examples.buildSubject accomplishmentSubjectProfile ∧
      Matches Examples.writeSubject accomplishmentSubjectProfile ∧
      Matches Examples.murderSubject accomplishmentSubjectProfile ∧
      Matches Examples.eatSubject accomplishmentSubjectProfile ∧
      Matches Examples.washSubject accomplishmentSubjectProfile ∧
      Matches Examples.murderObject accomplishmentObjectProfile ∧
      Matches Examples.washObject accomplishmentObjectProfile ∧
      Matches Examples.writeObject creationObject ∧
      Matches Examples.eatObject consumptionObject := by
  decide

theorem hit_class_matches_contact_object : Matches Examples.hitObject contactObject := by decide

/-- The single-entailment exemplars of (29) and (30) land in the perception and desire
templates. -/
theorem exemplars_match_templates :
    Matches Examples.seeSubject perception.subjectProfile ∧
      Matches Examples.needSubject desire.subjectProfile ∧
      desire.objectProfile.all (Matches Examples.needObject ·) ∧
      desire.objectProfile.all (Matches Examples.seekObject ·) := by
  decide

/-- The psych-state and desire templates split as the paper does: the *like* experiencer is
sentient, (38), and the *need* subject entails existence but none of (27a) to (27d). -/
theorem psych_desire_split :
    Matches Examples.likeSubject psychState.subjectProfile ∧
      Matches Examples.needSubject desire.subjectProfile ∧
      ¬ Matches Examples.needSubject psychState.subjectProfile := by
  decide

/-- The creation template omits (28d), which "all of 28" for the object of *build* includes:
the template follows the (35) hedge that creation objects are only mostly stationary. -/
theorem build_object_stationary_divergence :
    ¬ Matches Examples.buildObject creationObject ∧
      Matches Examples.buildObject (insert .stationary creationObject) := by
  decide

theorem break_object_it_divergence :
    ¬ Matches Examples.breakObject accomplishmentObjectProfile ∧
      Matches Examples.breakObject (insert .incrementalTheme accomplishmentObjectProfile) := by
  decide

/-- (30e) counts destruction as dependent existence, which the paper never states for the object
of *eat*: the row leaves it open, so the consumption template and its extension by dependent
existence both agree with it. -/
theorem eat_object_de_open :
    Matches Examples.eatObject consumptionObject ∧
      Matches Examples.eatObject (insert .dependentExistence consumptionObject) := by
  decide

end Dowty1991
