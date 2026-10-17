module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.Morph

/-!
# Evidentials

An evidential is an exponent together with the information sources it covers. Following
Aikhenvald, information source is carved into six semantic parameters, numbered I to VI: visual,
non-visual sensory, inference, assumption, hearsay and quotative. Willett's three types of
evidence, attested, inferring and reported, group them in pairs. A language's inventory is a
`List Evidential` in its Fragment, well formed when its terms are pairwise disjoint.

## Implementation notes

The six parameters are Aikhenvald's recurrent terms and nothing finer: no spoken language has an
evidential for smell, taste or touch alone, and general knowledge is a meaning an assumed
evidential may carry, often cast in the visual, rather than a parameter. A term whose source lies
outside the six, such as the Kashaya performative for the speaker's own act, covers none of
them. A term covers every parameter its source takes in, so a reported evidential with no
quotative beside it covers quotation as well as hearsay. Lexical and parenthetical means are
evidentiality strategies, not evidentials, and an inventory records none.

## Main definitions

* `Evidential.Parameter` — the six semantic parameters of information source, in order.
* `Evidential.EvidenceType`, `Parameter.evidenceType`, `EvidenceType.block` — Willett's
  three types of evidence, the type of a parameter and the parameters of a type.
* `Evidential` — the lexical entry; `Evidential.covers` its information sources.
* `Evidential.IsOfType`, `evidenceType?` — the type of evidence a term lies within, and
  `IsDirect`, `IsInferential`, `IsReportative`, the kinds of term within one type.
* `Evidential.WellFormed`, `Evidential.expressed` — a paradigm's disjointness and its span.

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
  deriving DecidableEq, Repr

/-- Each parameter falls under a type of evidence, Willett's types grouping the six parameters
in pairs. -/
def Parameter.evidenceType : Parameter → EvidenceType
  | .visual | .sensory => .attested
  | .inference | .assumption => .inferring
  | .hearsay | .quotative => .reported

/-- The block of a type of evidence is the set of parameters falling under it. -/
def EvidenceType.block (t : EvidenceType) : Finset Parameter :=
  Finset.univ.filter (·.evidenceType = t)

end Evidential

/-- An evidential is an exponent with the information sources it covers. -/
structure Evidential where
  /-- The exponent, in surface order. -/
  morphs : List Morphology.Morph
  /-- The semantic parameters the term covers; a term for a source outside the six covers
  none. -/
  covers : Finset Evidential.Parameter
  deriving DecidableEq

namespace Evidential

/-- A term is of a type of evidence when its coverage lies within that type's block. -/
def IsOfType (e : Evidential) (t : EvidenceType) : Prop := e.covers.Nonempty ∧ e.covers ⊆ t.block

instance (e : Evidential) (t : EvidenceType) : Decidable (e.IsOfType t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A direct evidential covers firsthand evidence only. -/
abbrev IsDirect (e : Evidential) : Prop := e.IsOfType .attested

/-- An inferential evidential covers inference or assumption only. -/
abbrev IsInferential (e : Evidential) : Prop := e.IsOfType .inferring

/-- A reportative evidential covers hearsay or quotation only. -/
abbrev IsReportative (e : Evidential) : Prop := e.IsOfType .reported

/-- The type of evidence of an evidential, when its coverage lies within one of Willett's
types; a non-firsthand term has none. -/
def evidenceType? (e : Evidential) : Option EvidenceType :=
  if e.IsDirect then some .attested
  else if e.IsInferential then some .inferring
  else if e.IsReportative then some .reported
  else none

/-- The parameters an inventory expresses. -/
def expressed (es : List Evidential) : Finset Parameter := (es.map covers).toFinset.sup id

/-- An inventory is well formed when its terms are pairwise disjoint, so that no parameter is
covered twice; two entries with the same nonempty coverage count as one term covered twice. -/
def WellFormed (es : List Evidential) : Prop := es.Pairwise fun a b ↦ Disjoint a.covers b.covers

instance : DecidablePred WellFormed := fun es ↦
  inferInstanceAs (Decidable (es.Pairwise fun a b ↦ Disjoint a.covers b.covers))

end Evidential
