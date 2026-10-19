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
the clause whatever has been fronted: *Tolú Adé rí rín* 'Adé saw TOLÚ'.

## Main definitions

* `Yoruba.ni`, `Yoruba.rin`: the focus particles of Standard Yorùbá and of Ìkálẹ̀.

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

end Yoruba
