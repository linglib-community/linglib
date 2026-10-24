module

public import Linglib.Syntax.Clause.Relative

/-!
# Korean relative clauses

Korean has no relative pronoun and no complementizer. A relative clause precedes its head noun
and its verb carries an adnominal suffix, *-(n)ɨn* in the present, *-n* in the past and *-l* in
the prospective; the relativized position is dropped together with its case marker, and this
strategy relativizes subjects, direct objects, indirect objects and obliques. A genitive cannot
be dropped: the possessive pronoun is retained, as in *chaki-ij lä-ka chongmyəngha-n kɨ salam*
'the man whose dog is smart', literally 'his dog is smart, the man'. The data are
[keenan-comrie-1977]'s.

## References

* [keenan-comrie-1977]
-/

@[expose] public section

namespace Korean

/-- The adnominal suffix of a prenominal clause, *-(n)ɨn*, *-n* or *-l*: the relativized position
is dropped from subjects through obliques, and at a genitive the possessive pronoun is
retained. -/
def relAdnominal : Relativizer where
  placement := .preNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique => {.gap}
    | .genitive => {.resumptive}
    | .objComparison => ∅

/-- The Korean relativizers. -/
def relativizers : List Relativizer := [relAdnominal]

end Korean
