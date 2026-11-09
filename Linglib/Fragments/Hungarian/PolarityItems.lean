module

public import Linglib.Fragments.Hungarian.Indefinites
public import Linglib.Semantics.PolarityItem.LicensingContext

/-!
# Hungarian polarity items

This file types the person members of the Hungarian negative and free-choice series of
`Hungarian.Indefinites` as polarity items. *senki* 'nobody' is a strict negative-concord item:
it requires clausemate negation, and under negation in a higher clause it gives way to *valaki
is*, as Kenesei, Vago and Fenyvesi show (§1.4.3, §1.4.5), who call *senki* and *semmi*
universal negative polarity items. *akárki* and *bárki* 'anyone' are free-choice items, as in
*Akárki jöhet a konferenciára* 'Anyone may come to the conference'. Haspelmath (A.26.3) finds
the two series mainly in the free-choice function, but also in comparatives, under indirect
negation and, with an emphatic value, in conditionals, and stars both under direct negation and
in questions.

## Implementation notes

A weak negative polarity item is licensed under clausal negation and in questions, so the licensing
theory admits both free-choice series where Haspelmath stars them; `Studies/Haspelmath1997.lean`
states the difference between the theory and his region.

## References

* [haspelmath-1997]
* [kenesei-vago-fenyvesi-1998]
* [rounds-2001]
-/

@[expose] public section

namespace Hungarian.PolarityItems

open PolarityItem

/-- *senki* 'nobody', which needs clausemate negation. -/
def senki : PolarityItem :=
  { form := Indefinites.senki.form
  , licensor := some .antiMorphic }

/-- *akárki* 'anyone', a free choice item, *Akár-ki tanul-hat-ott* 'Anybody could learn' (A200),
whose series is also used in comparatives (A201), under negation in a higher clause (A202) and,
emphatically, in conditionals (A203), but not under direct negation (A199a) or in questions (A204)
([haspelmath-1997] A.26.3). -/
def akárki : PolarityItem :=
  { form := Indefinites.akárki.form
  , licensor := some .weak
  , freeChoice := true }

/-- *bárki* 'anyone', a free choice item whose series is used as the *akár*-series is, in
comparatives (A201), under negation in a higher clause (A202) and in conditionals (A203), but not
under direct negation (A199a) or in questions (A204) ([haspelmath-1997] A.26.3). -/
def bárki : PolarityItem :=
  { form := Indefinites.bárki.form
  , licensor := some .weak
  , freeChoice := true }

theorem senki_licensing_characterized (c : LicensingContext) :
    c.licenser.Licenses senki ↔ c.licenser.Carries .antiMorphic :=
  Licenser.licenses_iff_carries rfl (by decide) (by decide)

end Hungarian.PolarityItems
