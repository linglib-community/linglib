module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Number.Basic

/-!
# Tagalog case markers

Tagalog marks the case of a noun phrase with a proclitic marker rather than on the noun: *ang*
for the subject, *ng* for possessors and for non-subject agents and objects, and *sa* for
obliques, the series Himmelmann labels specifier, possessive and locative and Kroeger
nominative, genitive and dative. Personal names take *si*, *ni* and *kay* instead, with the
plurals *sina*, *nina* and *kina*, which Schachter and Otanes analyse as the singular markers
with the suffix *-na*, *kay* changing its vowel. *Sina Santos* denotes Santos with associates,
where the common plural *ang mga Santos* denotes several people named Santos. Common nouns
pluralize with the proclitic *mga* after the case marker, which Schachter and Otanes describe as
optional where the context makes the plural clear, as absent with cardinal numerals, with which
it gives an approximative reading instead, and as restricted with mass nouns.

## Main definitions

* `Tagalog.Case` — the three case series, named for their common-noun markers
* `Tagalog.Case.label` — the comparative value of each series under Kroeger's labels
* `Tagalog.Case.personalMarker` — the personal-name marker of each series by number
* `Tagalog.plural` — the plural proclitic *mga* of common nouns

## References

* [himmelmann-2005-tagalog]
* [kroeger-1991-thesis]
* [schachter-otanes-1972]
-/

@[expose] public section

namespace Tagalog

/-- The three case series, named for their common-noun markers: *ang* for the subject, *ng* for
possessors and for non-subject agents and objects, and *sa* for obliques. -/
inductive Case where
  /-- The *ang* series. -/
  | ang
  /-- The *ng* series. -/
  | ng
  /-- The *sa* series. -/
  | sa
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value of a series under Kroeger's labels, the nominative, the genitive and
the dative. Himmelmann's labels, specifier, possessive and locative, would give the *sa* series
the locative. -/
def label : Case → _root_.Case
  | ang => .nom
  | ng => .gen
  | sa => .dat

/-- The personal-name marker of a series: singular *si*, *ni* and *kay*, plural *sina*, *nina* and
*kina*. -/
def personalMarker : Case → Number → Option String
  | ang, .singular => some "si"
  | ng, .singular => some "ni"
  | sa, .singular => some "kay"
  | ang, .plural => some "sina"
  | ng, .plural => some "nina"
  | sa, .plural => some "kina"
  | _, _ => none

end Case

/-- The plural proclitic *mga* of common nouns. -/
def plural : String := "mga"

end Tagalog
