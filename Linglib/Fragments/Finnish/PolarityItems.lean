module

public import Linglib.Fragments.Finnish.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# Finnish polarity-sensitive items

Finnish has no negative quantifier: 'nobody' is the negative auxiliary with the
polarity-sensitive indefinite *kukaan*, as in *Kukaan ei usko minu-a* 'No one believes me'.
*Kukaan* is *kuka* 'who' with the clitic -kAAn '(not) either', which follows the case ending,
as in *ke-tä-än* 'anyone' (partitive), and it occurs chiefly with the negative auxiliary and
in questions. The wh-words with *hyvänsä* or its equivalent *tahansa* form free-choice items such
as *kuka hyvänsä* 'whoever, anyone at all'. The positive polarity item *vasta* 'only then', the
twin of German *erst*, is the punctual 'until' of a positive clause.

## References

* [karlsson-2017]
* [haspelmath-1997]
* [karttunen-1974]
-/

@[expose] public section

namespace Finnish.PolarityItems

open PolarityItem

/-! ### NPI -/

/-- *kukaan* 'anyone, no one', *kuka* 'who' with the scalar clitic -kAAn, the *-kaan* series of
[haspelmath-1997]. -/
def kukaan : PolarityItem :=
  { form := Indefinites.kukaan.form
  , licensor := some .weak }

/-! ### FCI -/

/-- *kuka hyvänsä* 'whoever, anyone at all', *kuka* 'who' with *hyvänsä*, or its equivalent
*tahansa*, the free-choice series of [haspelmath-1997]. -/
def kukaHyvänsä : PolarityItem :=
  { form := Indefinites.kukaHyvänsä.form
  , freeChoice := true }

/-! ### PPI -/

/-- *vasta* 'only then', the punctual *until* of a positive clause, the twin of German *erst* and
the positive counterpart of the negated *ennen kuin* ([karttunen-1974]), as in *prinsessa heräsi
vasta yhdeksältä* 'the princess did not wake up until nine'. -/
def vasta : PolarityItem :=
  { form := "vasta"
  , antiLicensor := some .antiMorphic }

end Finnish.PolarityItems
