module

public import Linglib.Semantics.Evidential.Defs

/-!
# Bulgarian evidentiality

Bulgarian marks non-firsthand information with the *l*-form, fused with tense and aspect,
which covers inference and report and carries epistemic overtones of distance; the aorist is
the unmarked counterpart. Aikhenvald classes the system as possibly A2, while noting that
Balkan Slavic has been drifting toward an A1 system in which the unmarked form comes to signal
firsthand information. Koev's and Cumming's tense-evidential paradigm of the *l*-form is in
`Studies/Cumming2026.lean`.

## References

* [aikhenvald-2004], §2.1, §4.8
* [de-haan-2013]
* [koev-2017]
* [cumming-2026]
-/

@[expose] public section

namespace Bulgarian.Evidentiality

open Evidential

/-- The non-firsthand *l*-form, cited by its suffix; the aorist is its unmarked counterpart. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "l"], covers := {.inference, .assumption, .hearsay, .quotative} } ]

end Bulgarian.Evidentiality
