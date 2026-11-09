module

public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Fragments.German.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Data.Examples.Zwarts1998
public import Linglib.Data.Examples.Readers

/-!
# Zwarts (1998): Three types of polarity

Zwarts opens with Dutch and German negative polarity items of two kinds. The weak ones, Dutch
*hoeven* 'need' and *kunnen velen* 'can abide', German *brauchen* 'need' and *ausstehen können* 'can
stand', are fine under *at most n*, *few*, *no one* and *none of*; the strong ones, Dutch *ook maar
iets* 'anything at all' and *bijster* 'very', German *auch nur irgendetwas* and *sonderlich*, only
under the last two, which are anti-additive. Each example is linked to the Fragment entries of its
item and the named context of its quantifier, and the licensing theory [predicts every
judgment](##Zwarts1998.judgments_predicted), since *at most n* and *few* carry only weak strength.

## References

* [zwarts-1998]
-/

@[expose] public section

namespace Zwarts1998

open PolarityItem Examples

/-- A link from an example to the Fragment entry of its polarity item, the named context of the
quantifier above it, and the item's words as printed. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The context it stands in. -/
  context : LicensingContext
  /-- The item's words as printed. -/
  words : List String

open Dutch.PolarityItems German.PolarityItems in
/-- The links of the examples. -/
def links : List (Datum × Link) :=
  [(ex_1a, ⟨hoeven, .atMost, ["hoeven"]⟩), (ex_1b, ⟨hoeven, .nobody, ["hoeven"]⟩),
    (ex_1c, ⟨kunnenVelen, .few, ["kunnen", "velen"]⟩),
    (ex_1d, ⟨kunnenVelen, .nobody, ["kunnen", "velen"]⟩),
    (ex_2a, ⟨ookMaarIets, .atMost, ["ook", "maar", "iets"]⟩),
    (ex_2b, ⟨ookMaarIets, .nobody, ["ook", "maar", "iets"]⟩),
    (ex_2c, ⟨bijster, .few, ["bijster"]⟩), (ex_2d, ⟨bijster, .nobody, ["bijster"]⟩),
    (ex_3a, ⟨brauchen, .atMost, ["brauchen"]⟩), (ex_3b, ⟨brauchen, .nobody, ["brauchen"]⟩),
    (ex_3c, ⟨ausstehenKoennen, .few, ["ausstehen", "können"]⟩),
    (ex_3d, ⟨ausstehenKoennen, .nobody, ["ausstehen", "können"]⟩),
    (ex_4a, ⟨auchNurIrgendetwas, .atMost, ["auch", "nur", "irgendetwas"]⟩),
    (ex_4b, ⟨auchNurIrgendetwas, .nobody, ["auch", "nur", "irgendetwas"]⟩),
    (ex_4c, ⟨sonderlich, .few, ["sonderlich"]⟩), (ex_4d, ⟨sonderlich, .nobody, ["sonderlich"]⟩)]

-- each link's words are words of its example and of its entry's form, so a link to the wrong
-- entry fails
theorem links_attested :
    ∀ p ∈ links, ∀ w ∈ p.2.words,
      w.toList ∈ Datum.wordsOf p.1.primaryText ∧ w.toList <:+: p.2.item.form.toList := by
  decide +kernel

/-- The licensing theory admits each example's item in its context exactly when Zwarts judges the
example acceptable: the weak items everywhere, the strong ones only under *no one* and *none of*. -/
theorem judgments_predicted :
    ∀ p ∈ links, (p.1.judgment = .acceptable ↔ p.2.context.licenser.Admits p.2.item) := by
  decide +kernel

end Zwarts1998
