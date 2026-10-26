module

public import Mathlib.Order.Interval.Basic
public import Linglib.Morphology.Morph
public import Linglib.Semantics.Conditionals.Reading

/-!
# Conditional markers

Languages may lexicalize the readings of a conditional: Japanese *-ra* and German *falls* mark
only hypothetical conditionals, while *nara*, *wenn* and English *if* mark either. A conditional
marker is an exponent together with the readings it can mark.

## Main definitions

* `Conditional.Marker`: a conditional marker, its exponent with the readings it can mark.

## Implementation notes

The sources often attest a marker with one reading and say nothing about the other, so a
marker's readings are recorded as an interval of sets of readings: the readings it is attested
marking below, the readings it is not known to exclude above. A marker the sources describe
fully has a one-point interval.

## References

* [D. Lassiter, *Sorting Out Left-Nested Conditionals* (2025)][lassiter-2025]
-/

@[expose] public section

namespace Conditional

/-- A conditional marker is an exponent together with the readings it can mark. Japanese *-ra* and
German *falls* mark only hypothetical conditionals, and *nara*, *wenn* and English *if* mark either
([lassiter-2025]). -/
structure Marker where
  /-- The exponent, in surface order. -/
  morphs : List Morphology.Morph
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The set of readings the marker can mark lies in this interval: it contains the readings the
  sources attest, and is contained in the readings they do not exclude. -/
  readings : NonemptyInterval (Finset Reading)
  deriving DecidableEq

/-- The surface form is the morphs' forms with their boundary notation. -/
def Marker.form (m : Marker) : String := Morphology.Morph.surface m.morphs

end Conditional
