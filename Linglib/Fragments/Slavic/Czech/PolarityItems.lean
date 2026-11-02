module

public import Linglib.Fragments.Slavic.Czech.Determiners
public import Linglib.Semantics.PolarityItem.Licensing

/-!
# Czech polarity items

Czech indefinites come in two polarity-sensitive series, typed by `PolarityItem`. The *ni-*
series (*nikdo*, *nic*, *nikdy*, *nikam*) and the determiner *žádný* are negative concord items.
In Short's words, "any negative subject or object pronoun or pronoun-adverb is reinforced by ne-
in the verb", as in *Nikdo to nekoupil* 'No one bought it' and *Petr nekoupil nic* 'Peter didn't
buy anything' (p. 511), so the concord holds whether the item precedes the verb or follows it.
The *ně-* series (*někdo*, the determiner *nějaký*), built on the prefix *ně-*, are positive
polarity items, which escape the immediate scope of clausemate negation; the two determiners
therefore diagnose the position of negation in polar questions. The determiners take their
forms from `Czech.Determiners`, and the *ne-* prefix lives in `Negation.lean`.

## References

* [short-1993-czech]
* [haspelmath-1997]
* [stankova-simik-2025]
* [stankova-2026]
-/

@[expose] public section

namespace Czech.PolarityItems

open PolarityItem

/-! ### The *ni-* series -/

/-- *nikdo* 'nobody', the human concord item. -/
def nikdo : PolarityItem :=
  { form := "nikdo"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nic* 'nothing', the non-human concord item. -/
def nic : PolarityItem :=
  { form := "nic"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nikdy* 'never', the temporal concord item. -/
def nikdy : PolarityItem :=
  { form := "nikdy"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nikam* 'nowhere (to)', the directional concord item. -/
def nikam : PolarityItem :=
  { form := "nikam"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *žádný* 'no', the determiner concord item, licensed by inner negation alone in polar
questions ([stankova-2026]). -/
def zadny : PolarityItem :=
  { form := Determiners.zadny.form
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- The strict concord items. -/
def niSeries : List PolarityItem := [nikdo, nic, nikdy, nikam, zadny]

/-! ### The *ně-* series -/

/-- *nějaký* 'some', the determiner positive polarity item, admitted by outer and medial
negation in polar questions ([stankova-simik-2025], [stankova-2026]). -/
def nejaky : PolarityItem :=
  { form := Determiners.nejaky.form
  , antiLicensor := some .antiMorphic }

/-- *někdo* 'someone', the human positive polarity item, which replaces *nikdo* under the
non-propositional negation of a fear-predicate complement ([stankova-simik-2025]). -/
def nekdo : PolarityItem :=
  { form := "někdo"
  , antiLicensor := some .antiMorphic }

/-- The positive polarity items. -/
def neSeries : List PolarityItem := [nejaky, nekdo]

/-! ### Verification -/

theorem niSeries_strict_concord :
    ∀ e ∈ niSeries, ∀ c : LicensingContext,
      c.licenser.Licenses e ↔ c.licenser.Carries .antiMorphic := by
  intro e he c
  simp only [niSeries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    exact Licenser.licenses_iff_carries rfl (by decide) (by decide)

theorem neSeries_antiLicensed :
    ∀ e ∈ neSeries, LicensingContext.negation.licenser.AntiLicenses e := by
  decide

end Czech.PolarityItems
