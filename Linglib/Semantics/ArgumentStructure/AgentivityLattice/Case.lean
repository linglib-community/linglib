module

public import Linglib.Semantics.ArgumentStructure.AgentivityLattice.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Syntax.Case.Basic

/-!
# Case as a region of the agentivity lattice

Grimm's central claim is that a core case marker corresponds to a connected region of the
agentivity lattice, spreading outwards from the maximal agent and maximal patient nodes. Each
participant type is assigned a case region, and regions are mapped to morphological cases under
accusative and ergative alignment. Each core region is an order interval anchored at its pole, so
connectedness is mathlib's `Set.OrdConnected`, inherited from `Set.Ici` and `Set.Icc`; the
residual oblique region is not connected.

## Main definitions

* `CaseRegion`: the nominative or ergative, accusative or absolutive, dative and oblique regions.
* `ParticipantType.toCaseRegion`: the region of a participant type.

## Main results

* `ParticipantType.toCaseRegion_eq_nomErg_iff`: the nominative or ergative region is the up-set
  of the minimal instigator; the accusative and dative regions are intervals likewise.
* `ordConnected_nomErg`, `ordConnected_accAbs`, `ordConnected_dative`: the core regions are
  connected, and `not_ordConnected_oblique` the oblique region is not.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure

/-! ### Case regions -/

/-- The case regions of the agentivity lattice, three core regions, which are intervals anchored
at the poles, and the residual oblique region ([grimm-2011] pp.532–533). -/
inductive CaseRegion where
  /-- Nominative in accusative systems and ergative in ergative ones, the region spreading from
  the maximal agent, marking subjects. -/
  | nomErg
  /-- Accusative in accusative systems and absolutive in ergative ones, the region spreading from
  the maximal patient and existential persistence (beginning), marking objects. -/
  | accAbs
  /-- The dative, around sentience at qualitative persistence (beginning), marking recipients,
  experiencers and the second arguments of two-place communication and service verbs. -/
  | dative
  /-- The middle region between the core cases. -/
  | oblique
  deriving DecidableEq, Repr

/-- A participant type is in the nominative or ergative region with instigation at total
persistence, in the accusative or absolutive region with no agentivity at existential or
qualitative persistence (beginning), in the dative region with sentience but no instigation at
qualitative persistence (beginning), and otherwise in the oblique region. -/
def ParticipantType.toCaseRegion (n : ParticipantType) : CaseRegion :=
  if .instigation ∈ n.1 ∧ n.2 = .totalPersistence then .nomErg
  else if n.1 = ∅ ∧ (n.2 = .exPersBeginning ∨ n.2 = .quPersBeginning) then .accAbs
  else if .sentience ∈ n.1 ∧ .instigation ∉ n.1 ∧ n.2 = .quPersBeginning then .dative
  else .oblique

/-- The canonical case of a region under accusative alignment. -/
def CaseRegion.toAccusativeCase : CaseRegion → Case
  | .nomErg => .nom
  | .accAbs => .acc
  | .dative => .dat
  | .oblique => .inst

/-- The canonical case of a region under ergative alignment. -/
def CaseRegion.toErgativeCase : CaseRegion → Case
  | .nomErg => .erg
  | .accAbs => .abs
  | .dative => .dat
  | .oblique => .inst

/-! ### The core regions are intervals -/

/-- Instigation alone at total persistence is the bottom of the nominative or ergative region,
the minimal acceptable agent of *kill*, a natural force such as electricity or the explosion
([grimm-2011] §2.3). -/
def minimalInstigator : ParticipantType := ({.instigation}, ⊤)

theorem ParticipantType.toCaseRegion_eq_nomErg_iff (n : ParticipantType) :
    n.toCaseRegion = .nomErg ↔ minimalInstigator ≤ n := by
  revert n; decide

theorem ParticipantType.toCaseRegion_eq_accAbs_iff (n : ParticipantType) :
    n.toCaseRegion = .accAbs ↔
      maximalPatient ≤ n ∧ n ≤ TransitivityRank.contact.patientType := by
  revert n; decide

theorem ParticipantType.toCaseRegion_eq_dative_iff (n : ParticipantType) :
    n.toCaseRegion = .dative ↔
      sentientNonInstigator ≤ n ∧ n ≤ ({.volition, .sentience, .motion}, .quPersBeginning) := by
  revert n; decide

theorem setOf_nomErg_eq_Ici :
    {n : ParticipantType | n.toCaseRegion = .nomErg} = Set.Ici minimalInstigator :=
  Set.ext ParticipantType.toCaseRegion_eq_nomErg_iff

theorem setOf_accAbs_eq_Icc :
    {n : ParticipantType | n.toCaseRegion = .accAbs} =
      Set.Icc maximalPatient TransitivityRank.contact.patientType :=
  Set.ext ParticipantType.toCaseRegion_eq_accAbs_iff

theorem setOf_dative_eq_Icc :
    {n : ParticipantType | n.toCaseRegion = .dative} =
      Set.Icc sentientNonInstigator ({.volition, .sentience, .motion}, .quPersBeginning) :=
  Set.ext ParticipantType.toCaseRegion_eq_dative_iff

/-! ### Connectedness -/

theorem ordConnected_nomErg :
    {n : ParticipantType | n.toCaseRegion = .nomErg}.OrdConnected := by
  rw [setOf_nomErg_eq_Ici]; exact Set.ordConnected_Ici

theorem ordConnected_accAbs :
    {n : ParticipantType | n.toCaseRegion = .accAbs}.OrdConnected := by
  rw [setOf_accAbs_eq_Icc]; exact Set.ordConnected_Icc

theorem ordConnected_dative :
    {n : ParticipantType | n.toCaseRegion = .dative}.OrdConnected := by
  rw [setOf_dative_eq_Icc]; exact Set.ordConnected_Icc

theorem not_ordConnected_oblique :
    ¬ {n : ParticipantType | n.toCaseRegion = .oblique}.OrdConnected := fun h ↦ by
  have := h.out (x := ({.motion}, .quPersBeginning)) (by decide)
    (y := ({.sentience, .instigation, .motion}, .quPersBeginning)) (by decide)
    (show (({.sentience, .motion}, .quPersBeginning) : ParticipantType) ∈ Set.Icc _ _ from
      ⟨by decide, by decide⟩)
  exact absurd this (by decide)

end ArgumentStructure
