module

public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ArgumentSelection
public import Linglib.Fragments.English.Verbs.Basic
public import Linglib.Data.Examples.Dowty1991
public import Studies.Cruse1973
public import Linglib.Data.Examples.Readers

/-!
# Dowty (1991): Thematic proto-roles and argument selection

Dowty replaces thematic roles by two cluster concepts, the Proto-Agent and the Proto-Patient,
each a list of five entailments a predicate may impose on an argument, (27) and (28). The
Argument Selection Principle (31) lexicalizes as subject the argument with the most
Proto-Agent entailments and as direct object the one with the most Proto-Patient entailments.
The argument profiles the principle compares are read off rows of
`Data/Examples/Dowty1991.json`, from the single-entailment exemplars of (29) and (30) to the three
verb classes of (64).

## Implementation notes

A row attributes some entailments to its argument and denies others; the profiles agreeing with
it form the interval between the two, and the profile the principle compares is the bottom of that
interval, so counts are of stated entailments; the parenthesized (27e) and (28e) count like the
others. The incremental theme homomorphism of §6 and the material of §11 are not represented.

The telicity axis of Table 1 is the telicity of the predicate, not an entailment of the ten: a
change of state may be indefinite and atelic, as in *dim the lights* (p. 568), and a holistic
theme's definite change in stages (p. 569) has no entailment of its own, so a non-agentive
change of state falls in the unaccusative cell or the unstable one by its telicity. A verb entry
supplies it from its aspectual class.

## References

* [dowty-1991]
* [cruse-1973]
* [fillmore-1968]
-/

@[expose] public section

namespace Dowty1991

open ArgumentStructure ArgumentStructure.EntailmentProfile
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

/-- Dowty's exemplar of volition alone (29a) is Cruse's (32), and both analyses agree on it. -/
theorem cruse_volitive_is_volition_alone :
    entailed Examples.notEatSubject = {.volition} ∧
      (Cruse1973.Row.ofDatum Cruse1973.Examples.ex_32).bind (·.profile) = some {.volitive} := by
  decide

/-! ### The selection principle and its corollaries, (31) to (34) -/

variable (p q : EntailmentProfile)

/-- The hierarchies of (36) follow from the selection principle over the canonical role profiles. -/
theorem hierarchies :
    Outranks (ThetaRole.canonicalProfile .agent) (ThetaRole.canonicalProfile .instrument) ∧
      Outranks (ThetaRole.canonicalProfile .instrument) (ThetaRole.canonicalProfile .patient) ∧
      Outranks (ThetaRole.canonicalProfile .experiencer)
        (ThetaRole.canonicalProfile .patient) ∧
      DirectObjectOver (ThetaRole.canonicalProfile .patient)
        (ThetaRole.canonicalProfile .goal) := by
  decide

/-! ### The stable case and the ties, (35) and §8.3 -/

/-- In the primary transitive verbs of (35), the subject outranks the object under (31). -/
theorem primary_transitives :
    Outranks (entailed Examples.buildSubject) (entailed Examples.buildObject) ∧
      Outranks (entailed Examples.writeSubject) (entailed Examples.writeObject) ∧
      Outranks (entailed Examples.murderSubject) (entailed Examples.murderObject) ∧
      Outranks (entailed Examples.eatSubject) (entailed Examples.eatObject) ∧
      Outranks (entailed Examples.washSubject) (entailed Examples.washObject) := by
  decide

-- Corollary 2, §8.2
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

-- §9.2
theorem inchoative_stimulus_subject :
    Outranks (entailed Examples.surpriseSubject) (entailed Examples.surpriseObjectInchoative) := by
  decide

/-! ### Partially symmetric interactive predicates, §9.1 -/

/-- The subject of *kiss*, entailed volitional. -/
def kissSubjectProfile : EntailmentProfile := entailed Examples.kissSubject

/-- The object of *kiss*, not entailed volitional. -/
def kissObjectProfile : EntailmentProfile := entailed Examples.kissObject

-- (43), (42)
theorem kiss_subject_outranks :
    Outranks kissSubjectProfile kissObjectProfile ∧
      Alternates kissSubjectProfile kissSubjectProfile := by
  decide

-- (45)
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

-- §9.3.3
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

instance : DecidablePred Agentive := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The class Table 1 assigns to an intransitive predicate by the agentivity of its sole argument
and the predicate's telicity. -/
def intransClass (t : Aspect.Telicity) : IntransClass :=
  table1 (decide (Agentive p)) (decide (t = .telic))

/-- Predicates high in agentivity and low in patient properties are invariably
unergative. -/
theorem intransClass_unergative (h : Agentive p) : intransClass p .atelic = .unergative := by
  simp [intransClass, table1, h]

/-- Predicates low in agentivity and high in patient properties are invariably
unaccusative. -/
theorem intransClass_unaccusative (h : ¬ Agentive p) : intransClass p .telic = .unaccusative := by
  simp [intransClass, table1, h]

theorem intransClass_eq_unstable_iff {t : Aspect.Telicity} :
    intransClass p t = .unstable ↔ (Agentive p ↔ t = .telic) := by
  by_cases h : Agentive p <;> cases t <;> simp [intransClass, table1, h]

-- p. 568: change of state alone, which *dim the lights* entails without telicity
theorem intransClass_changeOfState :
    intransClass {.changeOfState} .atelic = .unstable ∧
      intransClass {.changeOfState} .telic = .unaccusative := by
  decide

/-- The class Table 1 assigns to an intransitive verb entry, by the profile the entry records for
its sole argument and the telicity of its aspectual class. -/
def verbClass (v : Verb) : Option IntransClass :=
  return intransClass (← v.slotProfile? .external) (← v.vendlerClass).telicity

theorem verbClass_run_arrive :
    verbClass English.Verbs.run.toVerb = some .unergative ∧
      verbClass English.Verbs.arrive.toVerb = some .unaccusative := by
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

-- (29), (30)
theorem exemplars_match_templates :
    Matches Examples.seeSubject perception.subjectProfile ∧
      Matches Examples.needSubject desire.subjectProfile ∧
      desire.objectProfile.all (Matches Examples.needObject ·) ∧
      desire.objectProfile.all (Matches Examples.seekObject ·) := by
  decide

-- (38), (27a), (27d)
theorem psych_desire_split :
    Matches Examples.likeSubject psychState.subjectProfile ∧
      Matches Examples.needSubject desire.subjectProfile ∧
      ¬ Matches Examples.needSubject psychState.subjectProfile := by
  decide

-- (28d), (35)
theorem build_object_stationary_divergence :
    ¬ Matches Examples.buildObject creationObject ∧
      Matches Examples.buildObject (insert .stationary creationObject) := by
  decide

theorem break_object_it_divergence :
    ¬ Matches Examples.breakObject accomplishmentObjectProfile ∧
      Matches Examples.breakObject (insert .incrementalTheme accomplishmentObjectProfile) := by
  decide

-- (30e)
theorem eat_object_de_open :
    Matches Examples.eatObject consumptionObject ∧
      Matches Examples.eatObject (insert .dependentExistence consumptionObject) := by
  decide

end Dowty1991
