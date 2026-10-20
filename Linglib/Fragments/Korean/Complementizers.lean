module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Korean complementizers

Korean embeds a clause in three ways: a bare clause in the declarative ending *-ta* followed
by the connective *-ko*; a *-ta*-clause under the adnominal ending *-nun* and the light noun
*kes* 'thing'; and a bare adnominal clause under *kes*. The three endings are complementizer
entries and *kes* a word. Bondarenko's assignment of *-ta* to the Cont head and of *-nun* and
*-ko* to allomorphs of Comp is the matter of `Studies/Bondarenko2022.lean`.

## References

* [bogal-allbritten-moulton-2018]
* [bondarenko-2022]
-/

@[expose] public section

namespace Korean.Complementizers

/-! ### Clause-typing morphemes -/

/-- *-ta*, the declarative ending, on finite verbs and on bare embedded clauses
(*ilk-ess-ta-ko*). -/
def ta : Complementizer where
  morphs := [.suff "ta"]
  verbForm := some .Fin
  types := .only .declarative

/-- *-nun*, the adnominal ending, which turns a clause into a noun modifier and under *kes*
'thing' yields a nominalized complement. -/
def nun : Complementizer where
  morphs := [.suff "nun"]
  verbForm := some .Part
  licenser := some .nominal

/-- *-ko*, the connective ending on bare embedded clauses, adjacent to the verb. -/
def ko : Complementizer where
  morphs := [.suff "ko"]
  verbForm := some .Conv
  licenser := some .verbal

/-- The clause-typing inventory. -/
def complementizers : List Complementizer := [ta, nun, ko]

/-! ### The light noun *kes* -/

/-- *kes* 'thing', the light noun under adnominal clauses. -/
def kes : Morphology.Word := { form := "kes", cat := .NOUN }

end Korean.Complementizers
