/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic

/-!
# Shawi

Shawi (Chayahuita; Kawapanan, Peru) inflects the verb for the person and number of both the
subject and the object, on a minimal/augmented number system with a clusivity contrast in the
first person, and marks some transitive subjects with the ergative suffix *-ri* while objects
stay unmarked. The agreement tables are those of [clem-deal-2026], compiled from [hart-1988],
[barraza-de-garcia-2005] and Ulloa's corpus work; the ergative data are [bourdeau-2015]'s.

## Main definitions

* `subjectMarker`: the indicative subject agreement suffix of a person–number cell.
* `objectMarker`: the object agreement suffix of a cell; third person has none.
* `ergativeMarker`: the ergative suffix.

## Implementation notes

Clusivity is a person value (`Person.firstInclusive`, `Person.firstExclusive`), and the
clusivity-neutral `Person.first` is not a cell of the paradigms. Number is `Number.minimal` and
`Number.augmented`, so first inclusive minimal is the speaker–addressee dyad. The glottal stop is
written `'`, and a segment in parentheses varies across the sources. A null exponent and an
absent cell are both `none`.

## References

* [clem-deal-2026]
* [hart-1988]
* [barraza-de-garcia-2005]
* [bourdeau-2015]
-/

@[expose] public section

namespace Kawapanan.Shawi

/-- Indicative subject agreement ([clem-deal-2026] Table 1). -/
def subjectMarker : Person → Number → Option String
  | .firstExclusive, .minimal => some "-(a)we"
  | .firstExclusive, .augmented => some "-ai"
  | .firstInclusive, .minimal => some "-e'"
  | .firstInclusive, .augmented => some "-ewa'"
  | .second, .minimal => some "-(a)n"
  | .second, .augmented => some "-(a)ma'"
  | .third, .minimal => some "-in"
  | .third, .augmented => some "-pi"
  | _, _ => none

/-- Object agreement ([clem-deal-2026] Table 2); third-person objects have no exponent. -/
def objectMarker : Person → Number → Option String
  | .firstExclusive, .minimal => some "-ku"
  | .firstExclusive, .augmented => some "-kui"
  | .firstInclusive, .minimal => some "-(n)pu'"
  | .firstInclusive, .augmented => some "-(n)pua'"
  | .second, .minimal => some "-(n)ken"
  | .second, .augmented => some "-((n)ke)ma'"
  | _, _ => none

/-- The ergative suffix of some transitive subjects ([clem-deal-2026] (4)); the nominative is
    unmarked. -/
def ergativeMarker : String := "-ri"

end Kawapanan.Shawi
