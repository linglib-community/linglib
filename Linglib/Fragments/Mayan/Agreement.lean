module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Case.Alignment
public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Morphotactics.AffixTemplate
public import Linglib.Data.UD.Features

/-!
# Mayan person marking

Mayan languages cross-reference the arguments of the verb with two sets of person markers,
called Set A and Set B by Mayanists. Set A marks the transitive subject and, on a noun, the
possessor; Set B marks the intransitive subject and the transitive object. Both sets occupy
fixed positions in the verbal complex, the word built from an aspect marker, the person
markers, the verb stem and a status suffix, and the position of Set B divides the family: in
the highland languages of Guatemala (K'ichean, Mamean, Q'anjob'alan) Set B follows the aspect
marker and precedes the stem, while in the lowland languages (Cholan, Tseltalan, Yucatecan) it
follows the stem. Coon, Mateo Pedro and Preminger call the two settings high and low
absolutive, after Tada's observation that the high-absolutive languages ban the extraction of
transitive subjects. Third person singular Set B has no segmental exponent in most of the
family, a pattern Kaufman and Norman reconstruct for proto-Mayan. Many Mayan languages split
their alignment by aspect or clause type, Set A extending to every subject in the
non-perfective aspects or in clauses without an aspect marker; Aissen, England and Zavala
survey the splits, which arose independently in Cholan, Q'anjob'alan and Yucatecan.

## Main declarations

* `Mayan.MarkerSet`: Set A and Set B.
* `Mayan.ExponentTable`: a person-marker paradigm over the six person–number cells, with
  `Mayan.ExponentTable.IsThirdSgZero` for a null third person singular.
* `Mayan.ergativeMarking`, `Mayan.extendedErgativeMarking`: the two markings of the roles by
  marker set that recur across the family.
* `Mayan.VerbSlot`: the position classes of the verbal complex, and `Mayan.absPosition`, the
  `Mayan.ABSPosition` a verbal template determines.

## Implementation notes

A paradigm is an `Agreement.Paradigm` over `Agreement.Bundle.personNumberCells`, so a
controller's `HasPhi.phi` indexes it directly, as in Corbett's account of agreement; an exponent is
a list of `Morphology.Morph`, empty for zero exponence and of length two for a discontinuous
marker such as a person prefix with a separate plural word. A cell whose only marker is a
process also renders as `[]`. Tables with pre-consonantal and pre-vocalic shapes are
`Phonology.Segment.Class → ExponentTable` functions. Each language's fragment carries its own
tables, its verbal template and its marking of the roles by marker set under whatever splits it,
so the position of the absolutive is read off the template and the alignment off the marking
rather than recorded beside them. The case labels that analyses give the two sets, ergative or
genitive for Set A and absolutive for Set B, are the analyses' and live in their studies;
quantification over the family is a study's, in `Studies/CoonMateoPedroPreminger2014.lean`.

## References

* [aissen-england-zavala-2017]
* [coon-mateo-pedro-preminger-2014]
* [corbett-1998]
* [dixon-1994]
* [kaufman-norman-1984]
* [tada-1993]
-/

@[expose] public section

namespace Mayan

/-- The two sets of person markers. Set A cross-references the transitive subject and the
possessor, Set B the intransitive subject and the transitive object. -/
inductive MarkerSet where
  | setA
  | setB
  deriving DecidableEq, Repr, Fintype

/-- A person-marker paradigm: the exponent of each person–number cell, as a list of morphs. -/
abbrev ExponentTable := Agreement.Paradigm (List Morphology.Morph)

/-- The third person singular cell has no segmental exponent. -/
def ExponentTable.IsThirdSgZero (e : ExponentTable) : Prop :=
  e.realize (.personNumber .third .singular) = some []

instance (e : ExponentTable) : Decidable e.IsThirdSgZero := inferInstanceAs (Decidable (_ = _))

/-! ### The verbal complex -/

/-- A position class of the verbal complex, in the Mayanist categories, which keep Set A and
Set B apart. The stem is not a slot: a slot's side of a `Morphology.AffixTemplate` is its
position relative to the stem. -/
inductive VerbSlot where
  | aspect
  | setB
  | setA
  | status
  deriving DecidableEq, Repr, Fintype

/-- Set B sits high, between the aspect marker and the stem, or low, after the stem. -/
inductive ABSPosition where
  | high
  | low
  deriving DecidableEq, Repr, Fintype

/-- A verbal template sets the absolutive high when Set B is a prefix slot. -/
def absPosition (t : Morphology.AffixTemplate VerbSlot) : ABSPosition :=
  if .setB ∈ t.prefixSlots then .high else .low

theorem absPosition_eq_high_iff (t : Morphology.AffixTemplate VerbSlot) :
    absPosition t = .high ↔ .setB ∈ t.prefixSlots := by
  simp [absPosition]

/-! ### Markings

A marking of the argument roles by marker set is an `ArgumentRole → Option MarkerSet`, `none`
on a role the verb does not cross-reference, and the predicates of `Alignment` read its
alignment directly. R and T, which those predicates do not read, are `none` throughout. -/

/-- The ergative marking: Set A on the transitive subject, Set B on the intransitive subject and
the object. -/
def ergativeMarking : ArgumentRole → Option MarkerSet
  | .A => some .setA
  | .S | .P => some .setB
  | .R | .T => none

/-- The extended ergative marking, Dixon's term: Set A on every subject, Set B on the object. -/
def extendedErgativeMarking : ArgumentRole → Option MarkerSet
  | .S | .A => some .setA
  | .P => some .setB
  | .R | .T => none

theorem isErgative_ergativeMarking : Alignment.IsErgative ergativeMarking := ⟨rfl, nofun⟩

theorem isAccusative_extendedErgativeMarking :
    Alignment.IsAccusative extendedErgativeMarking := ⟨rfl, nofun⟩

end Mayan
