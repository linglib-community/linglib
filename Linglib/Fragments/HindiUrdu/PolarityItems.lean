module

public import Linglib.Fragments.HindiUrdu.Indefinites
public import Linglib.Semantics.Polarity.Licensing

/-!
# Hindi-Urdu polarity items

Hindi-Urdu builds its negative polarity items from weak indefinites and the particle *bhii* 'even',
as Lahiri describes them for Hindi ((1)): *koii bhii* 'anyone', *ek bhii* 'even one', *kuch bhii*
'anything', *zaraa bhii* 'even a little', *kabhii bhii* 'ever'. All are negative polarity and free
choice items, licensed in downward-entailing contexts and, as free choice items, in generics and
generically read possibility modals but not under necessity modals (§5); the numeral and measure
items *ek bhii* and *zaraa bhii* are odd in imperatives (§5.4). Plain *koii* 'someone' is no
polarity item: it is used in every function of Haspelmath's map but the comparative and free choice
(A.22.3), and takes either scope with respect to negation (Lahiri (83)). The attested contexts
follow Lahiri §4–5.

## References

* [lahiri-1998]
* [haspelmath-1997]
-/

@[expose] public section

namespace HindiUrdu.PolarityItems

open PolarityItem

/-- *koii bhii* 'anyone', a negative polarity and free choice item ([lahiri-1998] (6),
(10)–(12), (29), (31b), (32), (34) for the downward-entailing uses; (35), (36b), (39b) for free
choice; out under a necessity modal, (36d)). -/
def koiiBhii : PolarityItem :=
  { form := Indefinites.koiiBhii.form
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .universalRestrictor, .adversative,
       .denyVerb, .beforeClause, .question, .generic, .modalPossibility,
       .imperative] }

/-- *ek bhii* 'even one', a negative polarity and free choice item, odd in imperatives
([lahiri-1998] (7), (10d), (11a), (29a), (29f), (34b), (35d), (36a); imperative (40b)). -/
def ekBhii : PolarityItem :=
  { form := "ek bhii"
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .universalRestrictor, .adversative,
       .denyVerb, .question, .generic, .modalPossibility] }

/-- *kuch bhii* 'anything, any (mass)' ([lahiri-1998] (8), (10f), (34c),
(35c), (39a)). -/
def kuchBhii : PolarityItem :=
  { form := (Indefinites.bhii Indefinites.kuch).form
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .question, .generic, .imperative] }

/-- *zaraa bhii* 'even a little', a negative polarity and free choice item, odd in imperatives
([lahiri-1998] (9), (10e), §4.5, (34d), (35e); imperative (40a)). -/
def zaraaBhii : PolarityItem :=
  { form := "zaraa bhii"
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [.negation, .conditionalAntecedent, .adversative, .question, .generic] }

/-- *kabhii bhii* 'ever, anytime' ([lahiri-1998] (36c)). -/
def kabhiiBhii : PolarityItem :=
  { form := (Indefinites.bhii Indefinites.kabhii).form
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts := [.modalPossibility] }

/-- The *bhii*-compound entries. -/
def bhiiItems : List PolarityItem :=
  [koiiBhii, ekBhii, kuchBhii, zaraaBhii, kabhiiBhii]

theorem hindi_licensing_sound :
    ∀ e ∈ bhiiItems, ∀ c ∈ e.licensingContexts, c.licenser.Admits e := by
  decide

end HindiUrdu.PolarityItems
