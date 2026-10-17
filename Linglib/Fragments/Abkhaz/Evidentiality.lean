module

public import Linglib.Semantics.Evidential.Defs

/-!
# Abkhaz evidentiality

Abkhaz has a two-choice system of Aikhenvald's type A2: a dedicated non-firsthand affix,
neutral to tense (*-zaap'* with present, aorist, perfect and one future; *-zaarən* with
imperfect, past indefinite, pluperfect and one future conditional), covers inference from
visible results and verbal report and is restricted to declarative main clauses, while the
unmarked forms leave the source unspecified. Turkish's non-firsthand is broader, taking in
non-visual perception as well.

## References

* [aikhenvald-2004], §2.1
* [de-haan-2013]
-/

@[expose] public section

namespace Abkhaz.Evidentiality

open Evidential

/-- The non-firsthand *-zaap'* ~ *-zaarən* is one term with two tense-conditioned allomorphs,
cited by the first. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "zaap'"], covers := {.inference, .assumption, .hearsay, .quotative} } ]

end Abkhaz.Evidentiality
