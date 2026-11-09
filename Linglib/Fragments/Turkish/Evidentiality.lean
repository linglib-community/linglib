module

public import Linglib.Semantics.Evidential.Defs

/-!
# Turkish evidentiality

Turkish has one evidential, the non-firsthand *-mIş*, covering report, inference and non-visual
perception, fused with tense and, as the copular *-(y)mIş*, with the copula. For Aikhenvald it
contrasts with evidentiality-neutral forms such as the *-DI* past, which do not signal firsthand
evidence but leave the source unspecified. Göksel and Kerslake instead gloss *-DI* as marking
direct knowledge beside past tense and perfective aspect, and *-mIş* as marking indirect
knowledge beside a relative past and perfective aspect; the inventory follows Aikhenvald.

## TODO

The form of *-mIş* is cited rather than read off `Turkish.Verb.Exponent.miş`, whose citation
form is a list of segments, some of them archiphonemes, with no spelling.

## References

* [aikhenvald-2004], §2.1
* [goksel-kerslake-2005]
-/

@[expose] public section

namespace Turkish.Evidentiality

open Evidential

/-- The non-firsthand *-mIş*. -/
def miş : Evidential :=
  { morphs := [.suff "mIş"], covers := {.sensory, .inference, .assumption, .hearsay, .quotative} }

/-- The evidentials, the non-firsthand alone; the *-DI* past is evidentiality-neutral, not a
firsthand term. -/
def evidentials : List Evidential := [miş]

end Turkish.Evidentiality
