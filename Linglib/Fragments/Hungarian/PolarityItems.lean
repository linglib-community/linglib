module

public import Linglib.Fragments.Hungarian.Indefinites
public import Linglib.Semantics.Polarity.Licensing

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

The comparative *mint akárhol Európában* 'than anywhere in Europe' is listed under the clausal
comparative, the licensing theory's routing of a surface *than NP*; the indirect negation of
Haspelmath's (A202), negation in a higher clause, has no licensing context. A weak negative
polarity item is licensed under clausal negation and in questions, so the licensing theory admits
both series where Haspelmath stars them (`freeChoice_excluded_admitted`); his implicational map
describes the series by a region of functions instead.

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
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *akárki* 'anyone', a free choice item attested under a possibility modal, *Akárki
tanulhatott* 'Anybody could learn', and, in its series, in the free relative *Akármit mondasz,
elindulok holnap* 'No matter what you say, I'm leaving tomorrow', in comparatives and in
conditionals, and starred under direct negation and in questions ([haspelmath-1997] A199a,
A200–A204). -/
def akárki : PolarityItem :=
  { form := Indefinites.akárki.form
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.modalPossibility, .freeRelative, .clausalComparative, .conditionalAntecedent]
  , excludedContexts := [.negation, .question] }

/-- *bárki* 'anyone', a free choice item attested under a possibility modal and, in its series, in
comparatives and in conditionals, and starred under direct negation and in questions
([haspelmath-1997] A199a, A201, A203, A204). -/
def bárki : PolarityItem :=
  { form := Indefinites.bárki.form
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .clausalComparative, .conditionalAntecedent]
  , excludedContexts := [.negation, .question] }

theorem senki_licensing_characterized (c : LicensingContext) :
    c.licenser.Licenses senki ↔ c.licenser.Carries .antiMorphic :=
  Licenser.licenses_iff_carries rfl (by decide) (by decide)

theorem freeChoice_licensing_sound :
    ∀ e ∈ [akárki, bárki], ∀ c ∈ e.licensingContexts, c.licenser.Admits e := by
  decide

theorem freeChoice_excluded_admitted :
    ∀ e ∈ [akárki, bárki], ∀ c ∈ e.excludedContexts, c.licenser.Admits e := by
  decide

end Hungarian.PolarityItems
