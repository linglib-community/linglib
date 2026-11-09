module

public import Linglib.Semantics.Evidential.Defs

/-!
# Georgian evidentiality

The Georgian perfect, whose traditional name translates as 'first evidential', is used for a
past event the speaker did not witness but infers from a present result or was told about. It
also serves as a present perfect, in negated past statements and as an optative, so Aikhenvald
reads its non-firsthand meaning as an extension of its main meaning, that of result, and the
perfect as an evidentiality strategy; most grammars treat it as an evidential.

## TODO

The quotative particles *metki*, *tko* and *o*, two of them from forms of 'say', are not
recorded.

## References

* [aikhenvald-2004]
-/

@[expose] public section

namespace Georgian.Evidentiality

/-- Georgian has no evidentials proper on Aikhenvald's reading. -/
def evidentials : List Evidential := []

/-- The perfect in its non-firsthand use, cited by the suffix glossed as the perfect. -/
def perfect : Evidential :=
  { morphs := [.suff "i"], covers := {.inference, .assumption, .hearsay, .quotative} }

/-- The evidentiality strategies. -/
def strategies : List Evidential := [perfect]

end Georgian.Evidentiality
