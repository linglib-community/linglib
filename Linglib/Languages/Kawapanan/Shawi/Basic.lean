/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Number.Basic
public import Linglib.Syntax.Feature.Person.Defs

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

The first person is inclusive or exclusive, and a first person with no clusivity is not a
cell of the paradigms. Number is `Number.minimal` and
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
def subjectMarker : Person → Option Clusivity → Number → Option String
  | .first, some .exclusive, .minimal => some "-(a)we"
  | .first, some .exclusive, .augmented => some "-ai"
  | .first, some .inclusive, .minimal => some "-e'"
  | .first, some .inclusive, .augmented => some "-ewa'"
  | .second, none, .minimal => some "-(a)n"
  | .second, none, .augmented => some "-(a)ma'"
  | .third, none, .minimal => some "-in"
  | .third, none, .augmented => some "-pi"
  | _, _, _ => none

/-- Object agreement ([clem-deal-2026] Table 2); third-person objects have no exponent. -/
def objectMarker : Person → Option Clusivity → Number → Option String
  | .first, some .exclusive, .minimal => some "-ku"
  | .first, some .exclusive, .augmented => some "-kui"
  | .first, some .inclusive, .minimal => some "-(n)pu'"
  | .first, some .inclusive, .augmented => some "-(n)pua'"
  | .second, none, .minimal => some "-(n)ken"
  | .second, none, .augmented => some "-((n)ke)ma'"
  | _, _, _ => none

/-- The ergative suffix of some transitive subjects ([clem-deal-2026] (4)); the nominative is
    unmarked. -/
def ergativeMarker : String := "-ri"

end Kawapanan.Shawi
