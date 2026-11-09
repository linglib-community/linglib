module

public import Linglib.Fragments.Finnish.Indefinites
public import Linglib.Semantics.PolarityItem.Basic

/-!
# Finnish polarity-sensitive items

Finnish has no negative quantifier. The meaning 'nobody' is expressed by the negative auxiliary
together with the polarity-sensitive indefinite *kukaan*, as in *Kukaan ei usko minu-a* 'No one
believes me'. *Kukaan* consists of *kuka* 'who' and the clitic -kAAn '(not) either', which follows
the case ending, as in the partitive *ke-tä-än* 'anyone'. It occurs chiefly with the negative
auxiliary and in questions. The wh-words combined with *hyvänsä*, or with its equivalent
*tahansa*, form free-choice items such as *kuka hyvänsä* 'whoever, anyone at all'. The positive
polarity item *vasta* 'only then' is the punctual 'until' of a positive clause and the counterpart
of German *erst*.

## References

* [karlsson-2017]
* [haspelmath-1997]
* [karttunen-1974]
-/

@[expose] public section

namespace Finnish.PolarityItems

open PolarityItem

/-! ### NPI -/

/-- *kukaan* 'anyone, no one', which is *kuka* 'who' with the scalar clitic -kAAn. It belongs to
the *-kaan* series of [haspelmath-1997]. -/
def kukaan : PolarityItem :=
  { form := Indefinites.kukaan.form
  , licensor := some .weak }

/-! ### FCI -/

/-- *kuka hyvänsä* 'whoever, anyone at all', which is *kuka* 'who' with *hyvänsä* or with its
equivalent *tahansa*. It belongs to the free-choice series of [haspelmath-1997]. -/
def kukaHyvänsä : PolarityItem :=
  { form := Indefinites.kukaHyvänsä.form
  , freeChoice := true }

/-! ### PPI -/

/-- *vasta* 'only then', the punctual *until* of a positive clause, as in *prinsessa heräsi vasta
yhdeksältä* 'the princess did not wake up until nine'. It is the counterpart of German *erst* and
the positive counterpart of the negated *ennen kuin* ([karttunen-1974]). -/
def vasta : PolarityItem :=
  { form := "vasta"
  , antiLicensor := some .antiMorphic }

end Finnish.PolarityItems
