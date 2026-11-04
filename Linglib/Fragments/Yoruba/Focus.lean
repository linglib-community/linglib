module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Yorùbá focus particles

A fronted focus is followed in Standard Yorùbá by *ni*, *Bàtà ni Adé rà* 'Adé bought A SHOE',
and a focus left in place bears no particle at all. Awobuluyi classes *ni* with the relative
clause introducer *tí*: it marks the clause after a fronted noun as that noun's topical
qualifier, a qualifier of the noun is never left behind (*Omi mímu ni mo lọ pọn* 'It was drinking
water that I went to fetch', not *Omi ni mo lọ pọn mímu*), and the clause undergoes the changes a
relative clause does. In the south-eastern dialect Ìkálẹ̀ the particle is *rín*, at the end of
the clause whatever has been fronted: *Tolú Adé rí rín* 'Adé saw TOLÚ'. 'Only' is *kàn* between
the subject and the verb, *Tolú kàn jẹ iṣu*, and *nìkan*, *lásán* or *péré* after its associate,
*Tolú jẹ iṣu nìkan*.

## Main definitions

* `Yoruba.ni`, `Yoruba.rin`: the focus particles of Standard Yorùbá and of Ìkálẹ̀.
* `Yoruba.kan`, `Yoruba.nikan`, `Yoruba.lasan`, `Yoruba.pere`: the exclusive particles.

## References

* [awobuluyi-1978]
* [aremu-2025a]
* [aremu-2025b]
-/

@[expose] public section

namespace Yoruba

/-- Standard Yorùbá *ni*, immediately after the fronted focus. -/
def ni : Particle := { form := "ni", position := some .postHost }

/-- Ìkálẹ̀ *rín*, at the end of the clause. -/
def rin : Particle := { form := "rín", position := some .clauseFinal }

/-- *kàn* 'only', before the verb. -/
def kan : Particle := { form := "kàn", position := some .clauseMedial }

/-- *nìkan* 'only', immediately after its associate. -/
def nikan : Particle := { form := "nìkan", position := some .postHost }

/-- *lásán* 'only, merely', immediately after its associate. -/
def lasan : Particle := { form := "lásán", position := some .postHost }

/-- *péré* 'only, merely', immediately after its associate. -/
def pere : Particle := { form := "péré", position := some .postHost }

end Yoruba
