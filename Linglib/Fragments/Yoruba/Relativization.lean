module

public import Linglib.Syntax.Clause.Relative

/-!
# Yoruba relativization

Yoruba relative clauses begin with *tí*, high-toned unlike the particle and the preposition *ti*,
which Awobuluyi describes as an introducer rather than a relative pronoun. A relativized subject
is replaced by the high-tone *ó*, *Ọkùnrin tí ó pè mí* 'the man who called me', and a genitive by
*rẹ̀* or *wọn*, *Ọmọ tí olè jí ìwé rẹ̀* 'the child whose books were stolen'. A direct object,
indirect object or oblique is dropped, *Ọkùnrin tí mo rí* 'the man I saw', the object of *ní*
with further restructuring.

## Implementation notes

* Awobuluyi's §6.18–6.24 is the source, and the one WALS F122A cites for Yoruba. Keenan and
  Comrie analyse the subject *ó* as verb agreement, which their 1977 coding excludes from pronoun
  retention (p. 92); it is recorded here as the pronoun Awobuluyi describes.
* Keenan and Comrie's data paper rejects the genitive gap (example 126). Their 1977 Table 1
  codes the indirect object, oblique and object of comparison as recast through serial verbs;
  the first two are recorded with Awobuluyi's gap, and the third is not relativized.
* Awobuluyi derives genitives without *tí*, *owó Dàda* 'Dada's money', from relative clauses
  (§3.15), and Ajiboye analyses the mid-tone *ti* of genitive phrases as a complementizer.

## References

* [awobuluyi-1978]
* [keenan-comrie-1977]
* [keenan-comrie-1979]
* [ajiboye-2005]
-/

@[expose] public section

namespace Yoruba

/-- The introducer *tí*. A relativized subject or genitive retains a pronoun, a direct object,
indirect object or oblique leaves a gap, and the object of comparison is not relativized. -/
def relTi : Relativizer where
  form := "tí"
  placement := .postNominal
  realize
    | .subject | .genitive => {.resumptive}
    | .directObject | .indirectObject | .oblique => {.gap}
    | .objComparison => ∅

/-- The Yoruba relativizers. -/
def relativizers : List Relativizer := [relTi]

end Yoruba
