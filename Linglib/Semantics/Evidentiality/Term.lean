module

public import Mathlib.Data.Finset.Image
public import Linglib.Morphology.Morph
public import Linglib.Semantics.Evidentiality.Source

/-!
# Evidentials

An evidential is an exponent together with the set of information sources it covers, a
`Finset` of the six parameters. A term `e` is of a type of evidence `t` when the image of
`e.covers` under `Parameter.evidenceType` is `{t}`: it covers some parameter, and every parameter
it covers falls under `t` (`Evidential.isOfType_iff`). A term is of at most one type
(`Evidential.IsOfType.eq`); one that covers parameters of two types, as a non-firsthand term
covers inference and report, is of none.

## Implementation notes

A term covers every parameter its source takes in, so a reported evidential with no quotative
beside it covers quotation as well as hearsay. A term whose source lies outside the six
parameters covers none of them.

A Fragment records evidentials proper, whose main meaning is information source. A form whose
main meaning is something else, such as a perfect, a conditional or a modal verb, may have an
evidential extension, which makes it an evidentiality strategy; a Fragment lists those apart, as
`strategies`, reading each from the entry that owns its main meaning where there is one, as a
modal verb's from its evidential extension. The line between evidentials and strategies is
Aikhenvald's, and grammars do not always draw it there. Lexical means, such as adverbs and
parentheticals, are neither, and a Fragment records none.

## References

* [aikhenvald-2004]
* [willett-1988]
-/

@[expose] public section

/-- An evidential is an exponent with the information sources it covers. -/
structure Evidential where
  /-- The exponent, in surface order. -/
  morphs : List Morphology.Morph
  /-- The semantic parameters the term covers; a term for a source outside the six covers
  none. -/
  covers : Finset Evidential.Parameter
  deriving DecidableEq

namespace Evidential

variable {e : Evidential} {t t' : EvidenceType}

/-- A term is of a type of evidence when it covers some parameter and every parameter it covers
falls under that type. -/
def IsOfType (e : Evidential) (t : EvidenceType) : Prop :=
  e.covers.image Parameter.evidenceType = {t}

instance (e : Evidential) (t : EvidenceType) : Decidable (e.IsOfType t) :=
  inferInstanceAs (Decidable (_ = _))

theorem isOfType_iff : e.IsOfType t ↔ e.covers.Nonempty ∧ e.covers ⊆ t.block := by
  simp [IsOfType, Finset.eq_singleton_iff_nonempty_unique_mem, Finset.subset_iff]

theorem IsOfType.nonempty (h : e.IsOfType t) : e.covers.Nonempty := (isOfType_iff.1 h).1

theorem IsOfType.subset (h : e.IsOfType t) : e.covers ⊆ t.block := (isOfType_iff.1 h).2

/-- A term is of at most one type of evidence. -/
theorem IsOfType.eq (h : e.IsOfType t) (h' : e.IsOfType t') : t = t' :=
  Finset.singleton_injective (h.symm.trans h')

/-- A direct evidential covers firsthand evidence only. -/
abbrev IsDirect (e : Evidential) : Prop := e.IsOfType .attested

/-- An inferential evidential covers inference or assumption only. -/
abbrev IsInferential (e : Evidential) : Prop := e.IsOfType .inferring

/-- A reportative evidential covers hearsay or quotation only. -/
abbrev IsReportative (e : Evidential) : Prop := e.IsOfType .reported

end Evidential
