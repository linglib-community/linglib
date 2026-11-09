module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# Spanish polarity items

The negative words *nadie* 'nobody', *nada* 'nothing', *ninguno* 'none', *nunca* and *jamás*
'never' stand alone before the verb, *nadie vino* 'no one came', and after it require a negative
before it, *no vino nadie*; only one negative word may precede the verb, never *nadie no sabía la
verdad*, and every later word that can be negated is, *nunca hay nada nuevo en ninguna parte*
'there's never anything new anywhere'. The same words mean 'anyone', 'anything', 'ever' after a
comparative or a superlative, after expressions of doubt, denial, impossibility or too much, in
questions expecting the answer 'no', and after *antes de*, *antes que* and *sin*: *más que nada*
'more than anything', *sin nada ni nadie* 'without anything or anybody' (Butt and Benjamin
§27.4). *Jamás* is never used after a comparative, *ahora más que nunca* 'now more than ever'
(§27.5.6). The series is Haspelmath's type of negative indefinites that co-occur with
verbal negation in some positions and not in others.

## References

* [butt-benjamin-2019]
* [haspelmath-1997]
-/

@[expose] public section

namespace Spanish.PolarityItems

open PolarityItem

/-- *nadie* 'nobody', 'anybody', as in *es dudoso que nadie pueda pasar por nativo* 'it's doubtful
whether anyone can pass as a native', *la mayor tontería que haya dicho nadie* 'the most stupid
thing anyone has said', *él tenía la culpa por llegar antes que nadie* 'it was his fault for
arriving before anyone else'. -/
def nadie : PolarityItem :=
  { form := "nadie", licensor := some .weak }

/-- *nada* 'nothing', 'anything', as in *más que nada, es taimado* 'more than anything, he's
cunning', *pocos libros dirían nada semejante* 'few books would say anything similar', *he venido
sin nada* 'I've come without anything'. -/
def nada : PolarityItem :=
  { form := "nada", licensor := some .weak }

/-- *ninguno* 'none', 'any', as in *es más lista que ninguno de los otros* 'she's cleverer than any
of the others', literary *si he sido insincero con ninguno de vosotros* 'if I have been insincere
with any of you'. -/
def ninguno : PolarityItem :=
  { form := "ninguno", licensor := some .weak }

/-- *nunca* 'never', 'ever', as in *salió más temprano que nunca* 'she went out earlier than ever
before', *¿quién hubiera pensado nunca que se casaría con Julia?* 'who would ever have thought
he'd have married Julia?'. -/
def nunca : PolarityItem :=
  { form := "nunca", licensor := some .weak }

/-- *jamás* 'never', 'ever' is stronger and less common than *nunca*, as in *el mejor que jamás
hubiera* 'the best that ever was', and is never used after a comparative. -/
def jamás : PolarityItem :=
  { form := "jamás", licensor := some .weak }

/-- The polarity items. -/
def items : List PolarityItem := [nadie, nada, ninguno, nunca, jamás]

end Spanish.PolarityItems
