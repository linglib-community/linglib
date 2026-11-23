module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.OrdConnected

/-!
# Information sources

Following Aikhenvald, information source is carved into six semantic parameters, numbered I to
VI: visual, non-visual sensory, inference, assumption, hearsay and quotative. They form a chain
in that order. Willett divides evidence into direct and indirect, and into three types: attested
evidence, which is direct, and reported and inferring evidence, which are indirect. The types
group the six parameters in consecutive pairs, so the maps

`Parameter.evidenceType : Parameter → EvidenceType` and
`EvidenceType.directness : EvidenceType → Directness`

have intervals of the parameters as fibres (`Parameter.isContiguous_evidenceType`,
`Parameter.isContiguous_directness`). The block `t.block` of a type is its fibre.

## Implementation notes

The six parameters are Aikhenvald's recurrent terms and nothing finer: no spoken language has an
evidential for smell, taste or touch alone, and general knowledge is a meaning an assumed
evidential may carry, often cast in the visual, rather than a parameter. They do not exhaust
the sources a language may mark: the Kashaya performative, for the speaker's own act, marks a
source outside the six. Willett's own subdivisions are finer in places, attested evidence into
visual, auditory and other sensory, reported evidence into second-hand, third-hand and folklore;
the pairing of his types with the six parameters is Aikhenvald's.

The types of evidence carry no order. The parameters place inferring evidence between attested
and reported, Willett's scale of reliability places reported evidence between attested and
inferring, and the order in which a language prefers its evidentials is a third datum, so the
grouping is stated as a map with order-connected fibres and not as a monotone map.

## References

* [aikhenvald-2004]
* [willett-1988]
-/

@[expose] public section

namespace Evidential

/-- The six recurrent semantic parameters of information source. -/
inductive Parameter where
  /-- Information acquired through seeing. -/
  | visual
  /-- Information acquired through hearing, typically extended to smell and taste and
  sometimes to touch. -/
  | sensory
  /-- Inference from visible or tangible evidence or result. -/
  | inference
  /-- Assumption from evidence other than visible results, such as reasoning or general
  knowledge. -/
  | assumption
  /-- Reported information with no reference to its source. -/
  | hearsay
  /-- Reported information with overt reference to the quoted source. -/
  | quotative
  deriving DecidableEq, Repr, Fintype

/-- The parameters in Aikhenvald's order, from visual evidence to quotation. -/
instance : LinearOrder Parameter := LinearOrder.lift' Parameter.ctorIdx (by decide)

instance : LocallyFiniteOrder Parameter := Fintype.toLocallyFiniteOrder

/-- Willett's three types of evidence. -/
inductive EvidenceType where
  /-- Evidence attested by the speaker's own senses. -/
  | attested
  /-- Evidence reported to the speaker, at second or third hand or as folklore. -/
  | reported
  /-- Evidence inferred from results or by reasoning. -/
  | inferring
  deriving DecidableEq, Repr, Fintype

/-- Evidence is direct when the speaker perceived the event and indirect otherwise. -/
inductive Directness where
  | direct
  | indirect
  deriving DecidableEq, Repr, Fintype

/-- Each parameter falls under a type of evidence, Willett's types grouping the six parameters
in pairs. -/
def Parameter.evidenceType : Parameter → EvidenceType
  | .visual | .sensory => .attested
  | .inference | .assumption => .inferring
  | .hearsay | .quotative => .reported

/-- Attested evidence is direct; inferring and reported evidence are indirect. -/
def EvidenceType.directness : EvidenceType → Directness
  | .attested => .direct
  | .inferring | .reported => .indirect

/-- The directness of a parameter is that of its type of evidence. -/
abbrev Parameter.directness (p : Parameter) : Directness := p.evidenceType.directness

/-- The block of a type of evidence is the set of parameters falling under it. -/
def EvidenceType.block (t : EvidenceType) : Finset Parameter :=
  Finset.univ.filter (·.evidenceType = t)

@[simp] theorem EvidenceType.mem_block {p : Parameter} {t : EvidenceType} :
    p ∈ t.block ↔ p.evidenceType = t := by
  simp [EvidenceType.block]

theorem EvidenceType.coe_block (t : EvidenceType) :
    (t.block : Set Parameter) = Parameter.evidenceType ⁻¹' {t} := by
  ext; simp

@[simp] theorem EvidenceType.block_attested :
    EvidenceType.attested.block = {.visual, .sensory} := by decide

@[simp] theorem EvidenceType.block_inferring :
    EvidenceType.inferring.block = {.inference, .assumption} := by decide

@[simp] theorem EvidenceType.block_reported :
    EvidenceType.reported.block = {.hearsay, .quotative} := by decide

/-- The parameters of a type of evidence are consecutive. -/
theorem Parameter.isContiguous_evidenceType : IsContiguous Parameter.evidenceType := by decide

/-- The direct parameters are consecutive, and so are the indirect ones. -/
theorem Parameter.isContiguous_directness : IsContiguous Parameter.directness := by decide

theorem EvidenceType.ordConnected_block (t : EvidenceType) :
    (t.block : Set Parameter).OrdConnected :=
  t.coe_block ▸ (isContiguous_iff_ordConnected_preimage _).1 Parameter.isContiguous_evidenceType t

theorem Parameter.directness_eq_direct {p : Parameter} :
    p.directness = .direct ↔ p.evidenceType = .attested := by
  cases p <;> decide

end Evidential
