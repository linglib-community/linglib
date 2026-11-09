module

public import Linglib.Fragments.Dutch.PolarityItems
public import Linglib.Fragments.German.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Data.Examples.Zwarts1998
public import Linglib.Data.Examples.Readers

/-!
# Zwarts (1998): Three types of polarity

Zwarts calls a negative polarity item *weak* if it is acceptable in every downward-entailing context
and *strong* if it is acceptable only in anti-additive contexts. Dutch *hoeven* 'need' and *kunnen
velen* 'can abide' and German *brauchen* 'need' and *ausstehen können* 'can stand' are weak, and
occur under *at most n*, *few*, *no one*, and *none of*. Dutch *ook maar iets* 'anything at all' and
*bijster* 'very' and German *auch nur irgendetwas* and *sonderlich* are strong, and occur only under
the last two. Each example is linked to the lexical entry of its item and to the named context of
its quantifier. Since *at most n* and *few* are downward entailing but not anti-additive, the
licensing theory [predicts every judgment](##Zwarts1998.judgments_predicted).

## References

* [zwarts-1998]
-/

@[expose] public section

namespace Zwarts1998

open PolarityItem Examples

/-- A link from an example to the lexical entry of its polarity item, to the named context of the
quantifier above it, and to the words of the item as printed. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The context in which the item stands. -/
  context : LicensingContext
  /-- The words of the item as printed. -/
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

-- The words of each link occur in its example and in the form of its entry, so a link to the
-- wrong entry fails.
theorem links_attested :
    ∀ p ∈ links, ∀ w ∈ p.2.words,
      w.toList ∈ Datum.wordsOf p.1.primaryText ∧ w.toList <:+: p.2.item.form.toList := by
  decide +kernel

/-- The licensing theory admits the item of each example in its context exactly when Zwarts judges
the example acceptable. The weak items are admitted in every context, and the strong items only
under *no one* and *none of*. -/
theorem judgments_predicted :
    ∀ p ∈ links, (p.1.judgment = .acceptable ↔ p.2.context.licenser.Admits p.2.item) := by
  decide +kernel

end Zwarts1998
