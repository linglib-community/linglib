module

public import Linglib.Semantics.Evidential.Defs

/-!
# Tuyuca evidentiality

Tuyuca (East Tucanoan, Vaupés) has a five-choice system of Aikhenvald's type D1, the most
frequently cited example of its kind: visual *-wi*, non-visual sensory *-ti*, apparent
(inferred) *-yi*, secondhand (reported) *-yigi* and assumed *-hiyi*, obligatory verbal
suffixes, classically described by Barnes. WALS codes the language as having direct
and indirect evidentials.

## References

* [aikhenvald-2004], §2.4
* [barnes-1984]
* [de-haan-2013]
-/

@[expose] public section

namespace Tuyuca.Evidentiality

open Evidential

/-- Visual *-wi*, non-visual *-ti*, apparent *-yi*, secondhand *-yigi* and assumed *-hiyi*. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "wi"], covers := {.visual} },
    { morphs := [.suff "ti"], covers := {.sensory} },
    { morphs := [.suff "yi"], covers := {.inference} },
    { morphs := [.suff "yigi"], covers := {.hearsay, .quotative} },
    { morphs := [.suff "hiyi"], covers := {.assumption} } ]

end Tuyuca.Evidentiality
