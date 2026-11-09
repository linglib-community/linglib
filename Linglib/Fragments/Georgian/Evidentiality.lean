module

public import Linglib.Fragments.Georgian.Agreement
public import Linglib.Semantics.Evidential.Defs

/-!
# Georgian evidentiality

The perfect, whose traditional name translates as 'first evidential', is used for a past event
the speaker did not witness but assumes took place, on the basis of a present result or of what
someone has said. It also serves as a present perfect, in negated past statements and as an
optative, and it appears where no evidential nuance can be detected, as with a first person
subject, so Aikhenvald reads its non-firsthand meaning as an extension of its main meaning, that
of result, and the perfect as an evidentiality strategy; most grammars treat it as an
evidential. The pluperfect, the 'second evidential', carries the nuance still less clearly and
is best taken as a plain pluperfect.

## TODO

The particle *turme* 'apparently' and the quotative particles *metki*, *tko* and *o*, two of
them from forms of 'say', are not recorded.

## References

* [aikhenvald-2004]
* [hewitt-1995]
-/

@[expose] public section

namespace Georgian

/-- The evidential extension of a screeve: that of the perfect covers inference, assumption and
report, and the other screeves have none. -/
def Screeve.evidential : Screeve → Finset Evidential.Parameter
  | .perfect => {.inference, .assumption, .hearsay, .quotative}
  | _ => ∅

namespace Evidentiality

/-- Georgian has no evidentials proper on Aikhenvald's reading. -/
def evidentials : List Evidential := []

/-- The perfect in its non-firsthand use, cited by the suffix Hewitt glosses as the perfect. -/
def perfect : Evidential := { morphs := [.suff "i"], covers := Screeve.perfect.evidential }

/-- The evidentiality strategies, the perfect alone. -/
def strategies : List Evidential := [perfect]

end Evidentiality

end Georgian
