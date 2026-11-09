module

public import Linglib.Semantics.Evidential.Defs

/-!
# Abkhaz evidentiality

Abkhaz has one evidential, a dedicated non-firsthand affix,
neutral to tense (*-zaap'* with present, aorist, perfect and one future; *-zaarən* with
imperfect, past indefinite, pluperfect and one future conditional), covers inference from
visible results and verbal report and is restricted to declarative main clauses, while the
unmarked forms leave the source unspecified. Turkish's non-firsthand is broader, taking in
non-visual perception as well.

## References

* [aikhenvald-2004], §2.1
-/

@[expose] public section

namespace Abkhaz.Evidentiality

open Evidential

/-- The non-firsthand *-zaap'* ~ *-zaarən*, one term with two tense-conditioned allomorphs, cited
by the first. -/
def nonFirsthand : Evidential :=
  { morphs := [.suff "zaap'"], covers := {.inference, .assumption, .hearsay, .quotative} }

/-- The evidentials, the non-firsthand alone. -/
def evidentials : List Evidential := [nonFirsthand]

end Abkhaz.Evidentiality
