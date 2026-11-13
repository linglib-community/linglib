module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.OfEntailmentProfile
public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.OfLifespan
public import Linglib.Semantics.ArgumentStructure.RoleList
public import Linglib.Semantics.Reference.Definiteness
public import Mathlib.Order.Interval.Set.OrdConnected
public import Studies.Dowty1991
public import Linglib.Data.Examples.Readers

/-!
# Grimm (2011): Semantics of case

Grimm recasts Dowty's proto-role entailments as four privative agentivity properties and four
persistence properties, whose product orders participant types by semantic prominence, and
treats a case as a region of that lattice spreading outwards from the maximal agent or the maximal
patient. This file places the paper's verbs on the lattice of `Semantics/ArgumentStructure/` and
defines its case regions as order intervals, so that [each is connected](##ordConnected_regions).
The transitivity hierarchy is [a progression of the patient away from the maximal
patient](##transitivity_hierarchy), and the Russian object of an opacity-creating verb is
[in the accusative region exactly when its noun phrase refers](##genitive_accusative_alternation).
Dowty's Proto-Patient entailments, read through Grimm's correspondences, [place the object of
*build* strictly below qualitative persistence (beginning)](##build_object_admits_iff).

## Implementation notes

The case regions are those drawn in the paper's schematic figures: the nominative or ergative
region is the total persistence branch, the accusative or absolutive region the two nodes without
agentivity at existential and qualitative persistence (beginning), and the dative region the node
of sentience at qualitative persistence (beginning). The paper leaves the extent of a region to
the language, and its middle, oblique region is not delimited, so neither is formalized; nor are
the remarks on differential object marking, deferred to Grimm (2005). Definiteness is the
substrate scale, the paper's three-step hierarchy, and the referring feature, the one that
entails existence, is its cut at the specific indefinites. The entailments of a node, which
subject selection counts, are its agentivity and persistence features (`entailmentCount`).

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

theorem canonical_verbs_mem_entailmentClosed :
    sitAgentivity ∈ Agentivity.entailmentClosed ∧ knowAgentivity ∈ Agentivity.entailmentClosed ∧
      discoverAgentivity ∈ Agentivity.entailmentClosed ∧
      lookAtAgentivity ∈ Agentivity.entailmentClosed ∧
      assassinateAgentivity ∈ Agentivity.entailmentClosed := by
  decide

theorem see_subject_agentivity :
    perception.subjectProfile.toAgentivity = knowAgentivity := by decide

/-! ### Named participant types

The maximal agent, with every agentivity property at total persistence, is the top of the
lattice. -/

/-- The maximal patient: no agentivity property, existing when the event begins but not after it,
as the object of *break* or *destroy* does (Fig. 4). -/
def maximalPatient : ParticipantType := (∅, .existentialBeginning)

/-- Instigation alone at total persistence, the minimal acceptable agent of *kill*: a natural force
such as electricity, or the explosion. -/
def killAgent : ParticipantType := ({.instigation}, .total)

/-- The agent of *break* and of *shoot*, Fig. 5's Ia and IIa: instigation and motion at total
persistence. -/
def breakAgent : ParticipantType := ({.instigation, .motion}, .total)

/-- The agent of *search*, Fig. 5's IIIa: instigation, motion and sentience at total
persistence. -/
def searchAgent : ParticipantType := ({.sentience, .instigation, .motion}, .total)

/-- The recipient of *geben* (9): sentience at qualitative persistence (beginning), consciously
involved as a possessor and qualitatively changed in its possessions. -/
def recipient : ParticipantType := ({.sentience}, .qualitativeBeginning)

/-! ### Dowty's Proto-Patient entailments and persistence, section 2.1

Grimm relates two of Dowty's Proto-Patient entailments to persistence (`EntailmentProfile.Admits`):
a change of state excludes qualitative persistence at the end, and dependent existence, which
conflates creation and destruction, excludes existential persistence at both ends. Dowty counts
coming into existence as a change of state (his (30a)) and attributes all of (28) to the object of
*build*, so read literally the correspondences exclude the creation level, existential persistence
(end), at which Grimm places the objects of verbs of creation. -/

/-- The object of *build*, with Dowty's entailments, admits only the levels strictly below
qualitative persistence (beginning), total non-persistence and existential persistence
(beginning), not the creation level Grimm assigns it. -/
theorem build_object_admits_iff (l : Persistence) :
    (Dowty1991.entailed Dowty1991.Examples.buildObject).Admits l ↔ l < .qualitativeBeginning :=
  EntailmentProfile.admits_iff_lt (by decide) (by decide)

theorem build_object_not_admits_existentialEnd :
    ¬ (Dowty1991.entailed Dowty1991.Examples.buildObject).Admits .existentialEnd :=
  fun h ↦ absurd ((build_object_admits_iff _).1 h) (by decide)

/-! ### Subject selection, section 2.3

The argument whose node dominates the other's is selected as subject, which the paper equates
with having the greater number of entailments. -/

-- (5): a destroyed object exists when the event begins, *What John did to the table was ruin
-- it*, and a created one does not, *\*What John did to the table was build it*
theorem pseudoCleft_presupposition {T Q : Type*} [LinearOrder T] [DecidableEq Q]
    {life run : NonemptyInterval T} {q : T → Q} :
    (Persistence.ofLifespan life run q = .existentialBeginning → run.fst ∈ life) ∧
      (Persistence.ofLifespan life run q = .existentialEnd → run.fst ∉ life) :=
  ⟨fun h ↦ (Persistence.ofLifespan_eq_existentialBeginning_iff.1 h).1,
    fun h ↦ (Persistence.ofLifespan_eq_existentialEnd_iff.1 h).1⟩

/-- The number of entailments of a node, its agentivity and persistence features. -/
def entailmentCount (n : ParticipantType) : ℕ := n.1.card + n.2.features.card

-- p. 527
theorem entailmentCount_strictMono : StrictMono entailmentCount := fun n m h ↦ by
  unfold entailmentCount
  rcases Prod.lt_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have := Finset.card_lt_card h₁
    have := Finset.card_le_card (Persistence.le_iff_features_subset.1 h₂)
    omega
  · have := Finset.card_le_card h₁
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
      ⟨Persistence.le_iff_features_subset.1 h₂.le,
        fun h ↦ h₂.ne (Persistence.features_injective h)⟩)
    omega

-- p. 527
theorem exists_entailmentCount_lt_incomparable :
    ∃ n ∈ ParticipantType.agentivityLattice, ∃ m ∈ ParticipantType.agentivityLattice,
      entailmentCount n < entailmentCount m ∧ ¬ n ≤ m ∧ ¬ m ≤ n :=
  ⟨recipient, ParticipantType.mem_agentivityLattice.2 (by decide), killAgent,
    ParticipantType.mem_agentivityLattice.2 (by decide), by decide⟩

-- (43) of [dowty-1991]
theorem kiss_subject_dominates (l : Persistence) :
    ((Dowty1991.kissObjectProfile.toAgentivity, l) : ParticipantType) <
      (Dowty1991.kissSubjectProfile.toAgentivity, l) :=
  Prod.mk_lt_mk_iff_left.2 (by decide)

-- p. 527: dominance in agentivity selects the subject Dowty's count selects
theorem kiss_subject_outranks :
    Dowty1991.kissSubjectProfile.Outranks Dowty1991.kissObjectProfile :=
  EntailmentProfile.outranks_of_toAgentivity_ssubset (by decide) (by decide)

/-! ### The transitivity region and the effectiveness hierarchy, section 3

The canonical transitive situation has an agent acting and an object undergoing the effects of
the action, which it can only do if it exists when the event begins. The hierarchy (8), a part of
[tsunoda-1985]'s, ranks resultative effective action verbs (*break*) above contact verbs
(*shoot*) above pursuit verbs (*search*). -/

/-- The transitivity region (Fig. 4): the nodes of an argument that exists when the event
begins, the up-set of existential persistence (beginning) on the persistence axis. -/
def transitivityRegion : Set ParticipantType := Prod.snd ⁻¹' Set.Ici .existentialBeginning

instance : DecidablePred (· ∈ transitivityRegion) := fun n ↦
  inferInstanceAs (Decidable (Persistence.existentialBeginning ≤ n.2))

theorem mk_mem_transitivityRegion {a : Agentivity} {l : Persistence} :
    (a, l) ∈ transitivityRegion ↔ .existsAtBeginning ∈ l :=
  Persistence.existsAtBeginning_mem_iff_le.symm

-- pp. 529–530: the region excludes the nodes of existential persistence (end) and total
-- non-persistence
theorem mk_mem_transitivityRegion_iff_ne {a : Agentivity} {l : Persistence} :
    (a, l) ∈ transitivityRegion ↔ l ≠ .existentialEnd ∧ l ≠ .nonPersistence := by
  change Persistence.existentialBeginning ≤ l ↔ _
  revert l; decide

/-- The verb classes of the hierarchy (8). -/
inductive VerbClass where
  /-- Resultative effective action, *kill* and *break*: the object is destroyed. -/
  | resultativeEffective
  /-- Contact, *shoot* and *hit*: the object is affected but persists. -/
  | contact
  /-- Pursuit, *search* and *seek*: the object need not exist. -/
  | pursuit
  deriving DecidableEq, Repr

/-- The canonical patient of each class, Fig. 5's Ip, IIp and IIIp. -/
def VerbClass.patientType : VerbClass → ParticipantType
  | .resultativeEffective => (∅, .existentialBeginning)
  | .contact => (∅, .qualitativeBeginning)
  | .pursuit => (∅, .nonPersistence)

/-- Along the hierarchy the patient moves away from the maximal patient: the patient of *break*
is the maximal patient, that of *shoot* lies above it inside the transitivity region, and that of
*search* outside it. -/
theorem transitivity_hierarchy :
    VerbClass.resultativeEffective.patientType = maximalPatient ∧
      VerbClass.resultativeEffective.patientType ≤ VerbClass.contact.patientType ∧
      VerbClass.resultativeEffective.patientType ≠ VerbClass.contact.patientType ∧
      VerbClass.contact.patientType ∈ transitivityRegion ∧
      VerbClass.pursuit.patientType ∉ transitivityRegion := by
  decide

/-! ### Core case marking systems, section 4

The region of a core case marker includes the maximal agent or the maximal patient and spreads
outwards from it. Accusative systems mark the patient region and leave the agent region in the
default nominative; ergative systems mark the agent region and leave the patient region in the
default absolutive. -/

/-- The core agent region (Fig. 6), nominative in accusative systems and ergative in ergative
ones: the total persistence branch. -/
def agentRegion : Set ParticipantType := Set.Ici (⊥, .total)

/-- The core patient region (Fig. 6), accusative or absolutive: no agentivity property at
existential or qualitative persistence (beginning). -/
def patientRegion : Set ParticipantType := Set.Icc maximalPatient (∅, .qualitativeBeginning)

/-- The dative region (Fig. 7): the recipient's node. -/
def dativeRegion : Set ParticipantType := {recipient}

instance : DecidablePred (· ∈ agentRegion) := fun _ ↦ Set.decidableMemIci
instance : DecidablePred (· ∈ patientRegion) := fun _ ↦ Set.decidableMemIcc
instance : DecidablePred (· ∈ dativeRegion) := fun n ↦ inferInstanceAs (Decidable (n = recipient))

/-- Each case region is a connected region of the lattice, being an order interval. -/
theorem ordConnected_regions :
    agentRegion.OrdConnected ∧ patientRegion.OrdConnected ∧ dativeRegion.OrdConnected :=
  ⟨Set.ordConnected_Ici, Set.ordConnected_Icc, Set.ordConnected_singleton⟩

-- p. 532: the core regions contain the maximal agent and the maximal patient
theorem poles_mem : ⊤ ∈ agentRegion ∧ maximalPatient ∈ patientRegion := by decide

-- p. 535: the cases of a language occupy distinct regions
theorem disjoint_regions :
    Disjoint agentRegion patientRegion ∧ Disjoint agentRegion dativeRegion ∧
      Disjoint patientRegion dativeRegion := by
  simp only [Set.disjoint_left]; decide

theorem agentRegion_eq_preimage : agentRegion = Prod.snd ⁻¹' {.total} := by
  ext ⟨a, l⟩
  change (⊥, Persistence.total) ≤ (a, l) ↔ l = .total
  rw [Prod.mk_le_mk]
  exact ⟨fun h ↦ top_le_iff.1 h.2, fun h ↦ ⟨bot_le, h.ge⟩⟩

-- section 2.3: every node at or above the minimal agent of *kill* is an acceptable subject of it,
-- and all of them are in the nominative or ergative region
theorem kill_subject_range : Set.Ici killAgent ⊆ agentRegion :=
  Set.Ici_subset_Ici.2 (by decide)

-- Fig. 5 on Fig. 6: the agents of the three classes and the patients of the first two are in
-- the core regions, the patient of *search* in neither
theorem transitivity_case_regions :
    breakAgent ∈ agentRegion ∧ searchAgent ∈ agentRegion ∧
      VerbClass.resultativeEffective.patientType ∈ patientRegion ∧
      VerbClass.contact.patientType ∈ patientRegion ∧
      VerbClass.pursuit.patientType ∉ patientRegion := by
  decide

/-! ### Extensions of the dative, section 5.1

The dative experiencer of the Urdu *ghussa aana* 'get angry' (10) is sentient and undergoes a
psychological change; the second argument of *danken* and *gratulieren* undergoes caused
possession in the cognitive realm and that of *dienen* and *helfen* a change through the benefit
conferred. All require sentience at qualitative persistence (beginning), the node of the
`recipient`, so the extended uses of the dative fall in the region of its canonical use. -/

/-! ### The genitive/accusative alternation in Russian, section 5.2

*Ivan ždët tramvaj* (accusative) 'Ivan is waiting for the/a certain tram' against *Ivan ždët
tramvaja* (genitive) 'Ivan is waiting for a tram', (12). The governed genitive marks the entity
whose existence is not entailed, the bottom node of the lattice; the accusative region contains
the node of existential persistence (beginning). An opacity-creating verb entails nothing for
its object, so the noun phrase decides: a referring one exists when the event begins. -/

/-- The referring feature of the definiteness hierarchy (14a), on which a specific indefinite is
referring, a definite referring and given, and a non-specific indefinite neither: the cut of the
definiteness scale at the specific indefinites. -/
def Referring (d : Definiteness) : Prop := .specific ≤ d

instance (d : Definiteness) : Decidable (Referring d) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The lowest node an object of an opacity-creating verb can occupy with a noun phrase of the
given definiteness: the maximal patient once existence is entailed, the bottom otherwise. -/
def opacityObject (d : Definiteness) : ParticipantType :=
  if Referring d then maximalPatient else ⊥

/-- The object is in the accusative region iff the noun phrase refers, and otherwise at the bottom
node of the governed genitive (12). -/
theorem genitive_accusative_alternation (d : Definiteness) :
    (opacityObject d ∈ patientRegion ↔ Referring d) ∧ (opacityObject d = ⊥ ↔ ¬ Referring d) := by
  cases d <;> decide

theorem bot_notMem_transitivityRegion : ⊥ ∉ transitivityRegion := by decide

end Grimm2011
