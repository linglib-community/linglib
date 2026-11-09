module

public import Linglib.Fragments.Mandarin.Indefinites
public import Linglib.Semantics.PolarityItem.LicensingContext

/-!
# Mandarin polarity-sensitive items

Mandarin indefinite polarity items, typed by `PolarityItem`. The bare interrogatives (*shéi* 谁
'who', *shénme* 什么 'what') are indefinites in the non-specific non-emphatic functions, from
irrealis through direct negation, and not in specific contexts that lack an element of uncertainty;
the emphatic wh + *dōu*~*yě* series ('even, also; every, all') is interchangeable between the two
particles, restricted to direct negation, and preverbal only; and the determiner *rènhé* 任何 'any',
used mainly with *dōu*, covers indirect and direct negation, the comparative and free choice
(Haspelmath, Fig. A.36).

## References

* [haspelmath-1997]
* [li-1992]
* [li-thompson-1981]
-/

@[expose] public section

namespace Mandarin.PolarityItems

open PolarityItem

/-! ### Bare interrogatives -/

/-- *shéi* (谁 'who', non-interrogative), an indefinite of the non-specific functions from irrealis
through direct negation ([haspelmath-1997] Fig. A.36): in questions, *Shéi xǐhuan tā ma?* 'Does
anyone like him?' (A266a), and degraded under direct negation, *?Tā bù xǐhuan shéi* (A267c, after
[li-1992] p. 150), where the emphatic series is used. -/
def shei : PolarityItem :=
  { form := Indefinites.shei.form
  , licensor := some .weak }

/-- *shénme* (什么 'what', non-interrogative), with *shéi*'s span and perfect under direct negation,
*Tā bù xǐhuan shénme* 'He does not like anything' (A267b); also in the irrealis imperative *Chī
diǎn shénme zài zǒu ba!* 'Please eat a little something before you leave' (A264, [li-1992] p. 152)
and in conditionals (A266b). -/
def shenme : PolarityItem :=
  { form := Indefinites.shenme.form
  , licensor := some .weak }

/-! ### The emphatic dōu~yě series -/

/-- *shéi dōu* ~ *shéi yě* (谁都/谁也, with clausemate negation) is the
    emphatic wh + *dōu*~*yě* series, as in *Tā shéi-dōu bù xìnren* 'She
    doesn't trust anyone' ([li-thompson-1981] p. 528). The two particles
    are interchangeable in the direct-negation function, the series' only
    region on the map, and occur preverbally only ([haspelmath-1997]
    A269, Fig. A.36). The same formation without negation is 'everyone',
    and [haspelmath-1997] (p. 309) leaves open whether the negated uses are
    indefinites or wide-scope universals. -/
def sheiDou : PolarityItem :=
  { form := Indefinites.sheiDou.form
  , licensor := some .antiMorphic }

/-! ### The free-choice determiner -/

/-- *rènhé* (任何 'any') is a free-choice determiner, used mainly with the adverb
    *dōu*. It gives free choice under modals (*Rènhé shíhou nǐ dōu kěyǐ lái* 'You
    can come anytime', A270) and occurs in comparatives (A271, a *bǐ* NP-comparative),
    under direct negation (A272) and under superordinate negation (A273).
    Etymologically *rèn* 'allow; appoint' + old interrogative *hé* 'what'
    ([haspelmath-1997] A.36.2). -/
def renhe : PolarityItem :=
  { form := Indefinites.renhe.form
  , licensor := some .weak
  , freeChoice := true }

theorem sheiDou_licensing_characterized (c : LicensingContext) :
    c.licenser.Licenses sheiDou ↔ c.licenser.Carries .antiMorphic :=
  Licenser.licenses_iff_carries rfl (by decide) (by decide)

end Mandarin.PolarityItems
