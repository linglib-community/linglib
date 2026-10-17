module

public import Linglib.Semantics.Evidential.Defs

/-!
# Turkish evidentiality

Turkish has a two-choice system of Aikhenvald's type A2: the non-firsthand *-mIş*, covering
report, inference and non-visual perception, contrasts with evidentiality-neutral forms such as
the *-DI* past, which do not signal firsthand evidence but leave the source unspecified. The
non-firsthand is fused with tense and the copula.

## References

* [aikhenvald-2004], §2.1
* [de-haan-2013]
-/

@[expose] public section

namespace Turkish.Evidentiality

open Evidential

/-- The non-firsthand *-mIş*; the *-DI* past is evidentiality-neutral, not a firsthand term. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "mIş"],
      covers := {.sensory, .inference, .assumption, .hearsay, .quotative} } ]

end Turkish.Evidentiality
