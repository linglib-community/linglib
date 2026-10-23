module

public import Linglib.Fragments.Finnish.Indefinites
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.Finnish.TemporalConnectives

/-!
# Finnish polarity-sensitive items

Finnish has no negative quantifier: 'nobody' is the negative auxiliary with the
polarity-sensitive indefinite *kukaan*, as in *Kukaan ei usko minu-a* 'No one believes me'.
*Kukaan* is *kuka* 'who' with the clitic -kAAn '(not) either', which follows the case ending,
as in *ke-tä-än* 'anyone' (partitive), and it occurs chiefly with the negative auxiliary and
in questions. The wh-words with *tahansa* form free-choice items such as *kuka tahansa*
'whoever, anyone at all'. The positive polarity item *vasta* 'only then', the twin of German
*erst*, is the punctual 'until' of a positive clause.

## Main definitions

* `Finnish.PolarityItems.kukaan`, `Finnish.PolarityItems.kukaTahansa`,
  `Finnish.PolarityItems.vasta`: the entries.

## Main results

* `Finnish.PolarityItems.finnish_licensing_sound`: every context of every entry licenses it.

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
  , licensor := some .weak
  , licensingContexts := [.question, .negation] }

/-! ### FCI -/

/-- *kuka tahansa* 'whoever, anyone at all', one cell of the paradigm of wh-words with
*tahansa*, beside *mikä tahansa* 'whatever' and *missä tahansa* 'wherever', which has a literary
alternant with *hyvänsä*. -/
def kukaTahansa : PolarityItem :=
  { form := "kuka tahansa"
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### PPI -/

/-- *vasta* 'only then', the punctual *until* of a positive clause, the twin of German *erst* and
the positive counterpart of the negated *ennen kuin* ([karttunen-1974]). Its connective entry is
`Finnish.TemporalConnectives.vasta`. -/
def vasta : PolarityItem :=
  { form := TemporalConnectives.vasta.form
  , antiLicensor := some .antiMorphic }

/-- The entries. -/
def items : List PolarityItem := [kukaan, kukaTahansa, vasta]

/-- Every context of every entry licenses it. -/
theorem finnish_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenser.Admits e := by
  decide

end Finnish.PolarityItems
