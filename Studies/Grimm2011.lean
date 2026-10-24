module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Case
public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.OfEntailmentProfile
public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.OfLifespan
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Studies.Dowty1991

/-!
# Grimm (2011): Semantics of case

Grimm recasts Dowty's proto-role entailments as four privative agentivity properties and four
persistence properties, whose product orders participant types by semantic prominence, and
treats a case as a connected region of that lattice. This file supplies the paper's placements
on the lattice of `Semantics/ArgumentStructure/` and reads its predictions off the interval
characterizations of the case regions.

## Main results

* `canonical_verb_chain`: the canonical subjects of section 2.2 climb a chain from the
  positional verbs to *assassinate*.
* `kill_subject_range`, `transitive_region_eq_Ici`: agents are closed upward and patients
  downward, so natural forces kill and the object of *hit* must exist when the event begins.
* `pseudoCleft_presupposition`: the pseudo-cleft (5) presupposes that its object exists when the
  event begins, which a destroyed object does and a created one does not.
* `kiss_outranking_from_dominance`: the dominance criterion reproduces Dowty's choice for *kiss*.
* `build_object_admits_iff`: read literally, the correspondences between Dowty's Proto-Patient
  entailments and persistence exclude the creation level for the object of *build*.
* `transitivity_hierarchy`: along Tsunoda's hierarchy the agent keeps instigation and motion
  while the patient rises out of the transitivity region.
* `pole_alignment`, `recipient_dative`: the poles read out to the core cases of either alignment,
  and the dative uses of section 5.1 share one node.
* `genitive_accusative_alternation`: the Russian genitive of *ždat'* marks a non-referring object
  at the bottom node.

## Implementation notes

The paper's remarks on differential object marking, deferred to Grimm (2005), and on the size of
the nominative or ergative region in a given language are not formalized. Definiteness is the
paper's three-step hierarchy (14), the referring feature being the one that entails existence.

## References

* [grimm-2011]
* [dowty-1991]
* [tsunoda-1985]
* [grimm-2005]
* [fillmore-1968]
-/

@[expose] public section

namespace Grimm2011

open ArgumentStructure

/-! ### The canonical verb chain, section 2.2 -/

/-- The subject of the positional verbs *sit* and *stand*: no agentivity property. -/
def sitAgentivity : Agentivity := ⊥

/-- The subject of *know* and *see*: sentience. -/
def knowAgentivity : Agentivity := {.sentience}

/-- The subject of *discover*: sentience and instigation. -/
def discoverAgentivity : Agentivity := {.sentience, .instigation}

/-- The subject of *look at*: sentience, instigation, and motion. -/
def lookAtAgentivity : Agentivity := {.sentience, .instigation, .motion}

/-- The subject of *assassinate*: all four properties. -/
def assassinateAgentivity : Agentivity := ⊤

/-- Each verb adds one property to the last: a chain from the bottom to the top of the
agentivity lattice, the paper's illustration that height is degree of agentivity. -/
theorem canonical_verb_chain :
    sitAgentivity < knowAgentivity ∧ knowAgentivity < discoverAgentivity ∧
      discoverAgentivity < lookAtAgentivity ∧ lookAtAgentivity < assassinateAgentivity := by
  decide

theorem canonical_verbs_valid :
    sitAgentivity.Valid ∧ knowAgentivity.Valid ∧ discoverAgentivity.Valid ∧
      lookAtAgentivity.Valid ∧ assassinateAgentivity.Valid := by
  decide

theorem see_subject_agentivity :
    perception.subjectProfile.toAgentivity = knowAgentivity := by decide

/-! ### Dowty's Proto-Patient entailments and persistence, section 2.1

Grimm relates two of Dowty's Proto-Patient entailments to persistence (`EntailmentProfile.Admits`):
a change of state excludes qualitative persistence at the end, and dependent existence, which
conflates creation and destruction, excludes existential persistence at both ends. Dowty counts
coming into existence as a change of state (his (30a)) and attributes all of (28) to the object of
*build*, so read literally the correspondences exclude the creation level, existential persistence
(end), at which Grimm places the objects of verbs of creation. -/

/-- The object of *build*, with Dowty's entailments, admits only total non-persistence and
existential persistence (beginning), not the creation level Grimm assigns it. -/
theorem build_object_admits_iff (l : PersistenceLevel) :
    (Dowty1991.entailed Dowty1991.Examples.buildObject).Admits l ↔
      l = .totalNonPersistence ∨ l = .exPersBeginning := by
  revert l; decide

/-! ### Argument ranges and subject selection, section 2.3

The agent of *kill* need only instigate, so natural forces such as electricity and eventive
nominals such as the explosion are acceptable subjects, and so is every node above them: agents
are upward closed. The patient of *hit* canonically changes qualitatively, but the object of the
conative *hit at* is unaffected and an object may happen to be destroyed, while an entity that
does not exist when the event begins cannot be hit: patients are closed downward to the
existence of the entity. -/

/-- Everything above the minimal instigator is in the nominative or ergative region: the range of
the subject of *kill*, from the interval characterization of that region. -/
theorem kill_subject_range {n : ParticipantType} (h : minimalInstigator ≤ n) :
    n.toCaseRegion = .nomErg :=
  (ParticipantType.toCaseRegion_eq_nomErg_iff n).mpr h

theorem kill_subject_endpoints :
    minimalInstigator.toCaseRegion = .nomErg ∧ (⊤ : ParticipantType).toCaseRegion = .nomErg :=
  ⟨kill_subject_range le_rfl, kill_subject_range le_top⟩

/-- The persistence levels an entity that exists when the event begins can have are the up-set
of existential persistence (beginning): the range of the patient of *hit* and, in section 3, the
persistence axis of the transitivity region. -/
theorem transitive_region_eq_Ici (n : ParticipantType) :
    n.InTransitiveRegion ↔ PersistenceLevel.exPersBeginning ≤ n.2 := by
  revert n; decide

/-- The pseudo-cleft (5) presupposes that its object exists when the event begins: a destroyed
object meets the presupposition, *What John did to the table was ruin it*, and a created one does
not, *\*What John did to the table was build it*. -/
theorem pseudoCleft_presupposition {T Q : Type*} [LinearOrder T] [DecidableEq Q]
    {life run : NonemptyInterval T} {q : T → Q} :
    (PersistenceLevel.ofLifespan life run q = .exPersBeginning → run.fst ∈ life) ∧
      (PersistenceLevel.ofLifespan life run q = .exPersEnd → run.fst ∉ life) :=
  ⟨fun h ↦ (PersistenceLevel.ofLifespan_eq_exPersBeginning_iff.1 h).1,
    fun h ↦ (PersistenceLevel.ofLifespan_eq_exPersEnd_iff.1 h).1⟩

/-- The subject of *kiss* strictly dominates its object on the agentivity lattice, so the
dominance criterion selects it, [dowty-1991]'s result for (43) without counting entailments. -/
theorem kiss_outranking_from_dominance :
    OutranksForSubject Dowty1991.kissSubjectProfile Dowty1991.kissObjectProfile :=
  outranks_of_lattice_dominance (by decide) (by decide)

/-! ### The transitivity region and the effectiveness hierarchy, section 3

[tsunoda-1985]'s hierarchy, the paper's (8): resultative effective action verbs (*break*) above
contact verbs (*shoot*) above pursuit verbs (*search*). The agent of the first two classes
entails instigation and motion; the agent of pursuit adds sentience (Fig. 5). -/

/-- The agent of *search*, Fig. 5's IIIa: instigation, motion, and sentience at total
persistence. -/
def pursuitAgent : ParticipantType := ({.sentience, .instigation, .motion}, .totalPersistence)

/-- Along the hierarchy the patient moves away from the maximal patient: the patient of *break*
is the maximal patient, that of *shoot* lies above it inside the transitivity region, and that of
*search* outside it, while the agents stay in the nominative or ergative region. -/
theorem transitivity_hierarchy :
    TransitivityRank.resultativeEffective.patientType = maximalPatient ∧
      TransitivityRank.resultativeEffective.patientType ≤ TransitivityRank.contact.patientType ∧
      TransitivityRank.resultativeEffective.patientType ≠ TransitivityRank.contact.patientType ∧
      TransitivityRank.contact.patientType.InTransitiveRegion ∧
      ¬ TransitivityRank.pursuit.patientType.InTransitiveRegion ∧
      effectorAgent.toCaseRegion = .nomErg ∧ pursuitAgent.toCaseRegion = .nomErg := by
  decide

theorem transitivity_patient_regions :
    TransitivityRank.resultativeEffective.patientType.toCaseRegion = .accAbs ∧
      TransitivityRank.contact.patientType.toCaseRegion = .accAbs ∧
      TransitivityRank.pursuit.patientType.toCaseRegion ≠ .accAbs := by
  decide

/-! ### Core case marking systems, section 4 -/

/-- The maximal agent and patient map to the two core cases of either alignment (Fig. 6). -/
theorem pole_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
      maximalPatient.toCaseRegion.toAccusativeCase = .acc ∧
      maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
      maximalPatient.toCaseRegion.toErgativeCase = .abs := by
  decide

/-! ### Extensions of the dative, section 5.1

The recipient of *geben* (9) is consciously involved as a possessor and qualitatively changed in
its possessions; the dative experiencer of the Urdu *ghussa aana* 'get angry' (10) is sentient and
undergoes a psychological change; the second argument of *danken* and *gratulieren* undergoes
caused possession in the cognitive realm and that of *dienen* and *helfen* a change through the
benefit conferred. All three require sentience at qualitative persistence (beginning), the
substrate's `sentientNonInstigator`. -/

/-- The recipient of (9). -/
def recipient : ParticipantType := sentientNonInstigator

/-- The recipient's node lies in the dative region (Fig. 7). -/
theorem recipient_dative : recipient.toCaseRegion = .dative := by decide

/-! ### The genitive/accusative alternation in Russian, section 5.2

*Ivan ždët tramvaj* (accusative) 'Ivan is waiting for the/a certain tram' against *Ivan ždët
tramvaja* (genitive) 'Ivan is waiting for a tram', (12). The governed genitive marks the entity
whose existence is not entailed, the bottom node of the lattice; the accusative region contains
the node of existential persistence (beginning). An opacity-creating verb entails nothing for
its object, so the noun phrase decides: a referring one exists when the event begins. -/

/-- The definiteness hierarchy (14), on which a specific indefinite is referring, a definite
referring and given, and a non-specific indefinite neither. -/
inductive Definiteness where
  | nonSpecificIndefinite
  | specificIndefinite
  | definite
  deriving DecidableEq, Repr

/-- The referring feature of (14a). -/
def Definiteness.Referring (d : Definiteness) : Prop := d ≠ .nonSpecificIndefinite

instance (d : Definiteness) : Decidable d.Referring := inferInstanceAs (Decidable (_ ≠ _))

/-- The lowest node an object of an opacity-creating verb can occupy with a noun phrase of the
given definiteness: the maximal patient once existence is entailed, the bottom otherwise. -/
def opacityObject (d : Definiteness) : ParticipantType :=
  if d.Referring then maximalPatient else ⊥

/-- The object is in the accusative region iff the noun phrase refers, and otherwise at the bottom
node of the governed genitive (12). -/
theorem genitive_accusative_alternation (d : Definiteness) :
    ((opacityObject d).toCaseRegion = .accAbs ↔ d.Referring) ∧
      (opacityObject d = ⊥ ↔ ¬ d.Referring) := by
  cases d <;> decide

theorem genitive_outside_region (n : ParticipantType) (h : n.InTransitiveRegion) :
    n ≠ ⊥ :=
  fun hn ↦ absurd h (hn ▸ by decide)

end Grimm2011
