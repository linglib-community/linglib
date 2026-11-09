module

public import Linglib.Semantics.Evidential.Defs

/-!
# Bulgarian evidentiality

Bulgarian marks non-firsthand information with the *l*-form, fused with tense and aspect,
which covers inference and report and carries epistemic overtones of distance; the aorist is
the unmarked counterpart. Balkan Slavic has been drifting toward a system in which the unmarked
form comes to signal firsthand information.

## References

* [aikhenvald-2004], §2.1, §4.8
* [koev-2017]
-/

@[expose] public section

namespace Bulgarian.Evidentiality

open Evidential

/-- The non-firsthand *l*-form, cited by its suffix; the aorist is its unmarked counterpart. -/
def lForm : Evidential :=
  { morphs := [.suff "l"], covers := {.inference, .assumption, .hearsay, .quotative} }

/-- The evidentials, the *l*-form alone. -/
def evidentials : List Evidential := [lForm]

end Bulgarian.Evidentiality
