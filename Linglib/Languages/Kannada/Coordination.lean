module

public import Linglib.Syntax.Category.Coordinator

/-!
# Kannada coordinators

Kannada, a Dravidian language of southern India, conjoins noun phrases with the enclitic *-uu*
on each coordinand, *Narahariy-u: So:maše:kharan-u:* 'Narahari and Somashekhara' in the
example Haspelmath cites from Sridhar, whose colon marks the long vowel written *uu* here as in
`Kannada.Indefinites`. The same enclitic is the additive particle 'also', and *-oo* is 'or'.
Each also marks an indefinite series on the interrogative pronouns, *yaar-uu* 'anyone' and
*yaar-oo* 'someone'.

## Main definitions

* `Kannada.Coordination.uu`, `Kannada.Coordination.oo`: the conjunctive and disjunctive
  enclitics.

## References

* [haspelmath-1997]
* [haspelmath-2007]
* [sridhar-1990]
-/

@[expose] public section

namespace Kannada.Coordination

/-- *-uu* 'and', enclitic on each coordinand, also the additive particle
`Kannada.FocusParticles.uu` and the marker of the *-uu* series of indefinites,
`Kannada.Indefinites.uuSeries`. -/
def uu : Coordinator :=
  { morph := .encl "uu", gloss := "and", role := .conjunctive }

/-- *-oo* 'or', enclitic, also the marker of the *-oo* series of indefinites,
`Kannada.Indefinites.ooSeries`. -/
def oo : Coordinator :=
  { morph := .encl "oo", gloss := "or", role := .disjunctive }

end Kannada.Coordination
