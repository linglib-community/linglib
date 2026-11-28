module

public import Linglib.Languages.Dutch.PolarityItems
public import Linglib.Languages.German.PolarityItems
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
  /-- The class that Zwarts gives the item. -/
  cls : PolarityItem.Class

open Dutch.PolarityItems German.PolarityItems in
/-- The links of the examples. The items of (1) and (3) are weak, and those of (2) and (4) are
strong. -/
def links : List (Datum × Link) :=
  [(ex_1a, ⟨hoeven, .atMost, ["hoeven"], .npi .monotoneDecreasing⟩),
    (ex_1b, ⟨hoeven, .nobody, ["hoeven"], .npi .monotoneDecreasing⟩),
    (ex_1c, ⟨kunnenVelen, .few, ["kunnen", "velen"], .npi .monotoneDecreasing⟩),
    (ex_1d, ⟨kunnenVelen, .nobody, ["kunnen", "velen"], .npi .monotoneDecreasing⟩),
    (ex_2a, ⟨ookMaarIets, .atMost, ["ook", "maar", "iets"], .npi .antiAdditive⟩),
    (ex_2b, ⟨ookMaarIets, .nobody, ["ook", "maar", "iets"], .npi .antiAdditive⟩),
    (ex_2c, ⟨bijster, .few, ["bijster"], .npi .antiAdditive⟩),
    (ex_2d, ⟨bijster, .nobody, ["bijster"], .npi .antiAdditive⟩),
    (ex_3a, ⟨brauchen, .atMost, ["brauchen"], .npi .monotoneDecreasing⟩),
    (ex_3b, ⟨brauchen, .nobody, ["brauchen"], .npi .monotoneDecreasing⟩),
    (ex_3c, ⟨ausstehenKoennen, .few, ["ausstehen", "können"], .npi .monotoneDecreasing⟩),
    (ex_3d, ⟨ausstehenKoennen, .nobody, ["ausstehen", "können"], .npi .monotoneDecreasing⟩),
    (ex_4a, ⟨auchNurIrgendetwas, .atMost, ["auch", "nur", "irgendetwas"], .npi .antiAdditive⟩),
    (ex_4b, ⟨auchNurIrgendetwas, .nobody, ["auch", "nur", "irgendetwas"], .npi .antiAdditive⟩),
    (ex_4c, ⟨sonderlich, .few, ["sonderlich"], .npi .antiAdditive⟩),
    (ex_4d, ⟨sonderlich, .nobody, ["sonderlich"], .npi .antiAdditive⟩)]

-- The words of each link occur in its example and in the form of its entry, so a link to the
-- wrong entry fails.
theorem links_attested :
    ∀ p ∈ links, ∀ w ∈ p.2.words,
      w.toList ∈ Datum.wordsOf p.1.primaryText ∧ w.toList <:+: p.2.item.form.toList := by
  decide +kernel

/-- A context admits the class of the item of each example exactly when Zwarts judges the example
acceptable. The weak class is admitted in every context of the examples, and the strong class
only under *no one* and *none of*. -/
theorem judgments_predicted :
    ∀ p ∈ links, (p.1.judgment = .acceptable ↔ p.2.context.Admits p.2.cls) := by
  decide +kernel

-- The entry of each item lists the context of an acceptable example among those in which the item
-- is attested, and the context of a starred example among those from which it is excluded.
theorem entries_agree :
    ∀ p ∈ links, (p.1.judgment = .acceptable → p.2.context ∈ p.2.item.attested) ∧
      (p.1.judgment ≠ .acceptable → p.2.context ∈ p.2.item.excluded) := by
  decide +kernel

end Zwarts1998
