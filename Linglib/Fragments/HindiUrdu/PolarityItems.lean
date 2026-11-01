module

public import Linglib.Fragments.HindiUrdu.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# Hindi-Urdu polarity items

Hindi-Urdu builds its negative polarity items from weak indefinites and the particle *bhii* 'even':
*koii bhii* 'anyone', *ek bhii* 'even one', *kuch bhii* 'anything', *zaraa bhii* 'even a little',
*kabhii bhii* 'ever'. All are negative polarity and free choice items, licensed in
downward-entailing contexts and, as free choice items, in generics and generically read
possibility modals. Plain *koii* 'someone' is no polarity item: it is used in every function of
Haspelmath's map but the comparative and free choice, and takes either scope with respect to
negation. The sentences that attest the items and star them are rows of
`Data/Examples/Lahiri1998.json`.

## References

* [lahiri-1998]
* [haspelmath-1997]
-/

@[expose] public section

namespace HindiUrdu.PolarityItems

open PolarityItem

/-- *koii bhii* 'anyone', a negative polarity and free choice item. -/
def koiiBhii : PolarityItem :=
  { form := Indefinites.koiiBhii.form
  , licensor := some .weak
  , freeChoice := true }

/-- *ek bhii* 'even one', a negative polarity and free choice item. -/
def ekBhii : PolarityItem :=
  { form := "ek bhii"
  , licensor := some .weak
  , freeChoice := true }

/-- *kuch bhii* 'anything, any (mass)', a negative polarity and free choice item. -/
def kuchBhii : PolarityItem :=
  { form := (Indefinites.bhii Indefinites.kuch).form
  , licensor := some .weak
  , freeChoice := true }

/-- *zaraa bhii* 'even a little', a negative polarity and free choice item. -/
def zaraaBhii : PolarityItem :=
  { form := "zaraa bhii"
  , licensor := some .weak
  , freeChoice := true }

/-- *kabhii bhii* 'ever, anytime', a negative polarity and free choice item. -/
def kabhiiBhii : PolarityItem :=
  { form := (Indefinites.bhii Indefinites.kabhii).form
  , licensor := some .weak
  , freeChoice := true }

end HindiUrdu.PolarityItems
