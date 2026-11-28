module

public import Linglib.Languages.Dutch.PolarityItems
public import Linglib.Languages.German.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Data.Examples.Zwarts1998
public import Linglib.Data.Examples.Readers

/-!
# Zwarts (1998): Three types of polarity

Zwarts sorts negative polarity items by where they occur. Dutch *hoeven* 'need' and *kunnen
velen* 'can abide' and German *brauchen* 'need' and *ausstehen können* 'can stand' occur under *at
most n*, *few*, *no one*, and *none of*, and are *weak*. Dutch *ook maar iets* 'anything at all'
and *bijster* 'very' and German *auch nur irgendetwas* and *sonderlich* occur only under the last
two, and are *strong*. His laws identify the two types by the functions that the contexts denote:
the weak items have the distribution of the monotone decreasing contexts, and the strong items
that of the anti-additive ones. Each example is linked to the lexical entry of its item and to
the named context of its quantifier. Since *at most n* and *few* are monotone decreasing but not
anti-additive, the two distributions contain exactly the contexts of the acceptable examples.

## References

* [zwarts-1998]
-/

@[expose] public section

namespace Zwarts1998

open PolarityItem Examples

/-- The distribution of the *weak* negative polarity items: the monotone decreasing contexts. -/
abbrev weak : Distribution := .npi .monotoneDecreasing

/-- The distribution of the *strong* negative polarity items: the anti-additive contexts. -/
abbrev strong : Distribution := .npi .antiAdditive

/-- A link from an example to the lexical entry of its polarity item, to the named context of the
quantifier above it, and to the words of the item as printed. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The context in which the item stands. -/
  context : LicensingContext
  /-- The words of the item as printed. -/
  words : List String
  /-- The distribution of the type to which Zwarts assigns the item. -/
  distribution : Distribution

open Dutch.PolarityItems German.PolarityItems in
/-- The links of the examples. The items of (1) and (3) are weak, and those of (2) and (4) are
strong. -/
def links : List (Datum × Link) :=
  [(ex_1a, ⟨hoeven, .atMost, ["hoeven"], weak⟩),
    (ex_1b, ⟨hoeven, .nobody, ["hoeven"], weak⟩),
    (ex_1c, ⟨kunnenVelen, .few, ["kunnen", "velen"], weak⟩),
    (ex_1d, ⟨kunnenVelen, .nobody, ["kunnen", "velen"], weak⟩),
    (ex_2a, ⟨ookMaarIets, .atMost, ["ook", "maar", "iets"], strong⟩),
    (ex_2b, ⟨ookMaarIets, .nobody, ["ook", "maar", "iets"], strong⟩),
    (ex_2c, ⟨bijster, .few, ["bijster"], strong⟩),
    (ex_2d, ⟨bijster, .nobody, ["bijster"], strong⟩),
    (ex_3a, ⟨brauchen, .atMost, ["brauchen"], weak⟩),
    (ex_3b, ⟨brauchen, .nobody, ["brauchen"], weak⟩),
    (ex_3c, ⟨ausstehenKoennen, .few, ["ausstehen", "können"], weak⟩),
    (ex_3d, ⟨ausstehenKoennen, .nobody, ["ausstehen", "können"], weak⟩),
    (ex_4a, ⟨auchNurIrgendetwas, .atMost, ["auch", "nur", "irgendetwas"], strong⟩),
    (ex_4b, ⟨auchNurIrgendetwas, .nobody, ["auch", "nur", "irgendetwas"], strong⟩),
    (ex_4c, ⟨sonderlich, .few, ["sonderlich"], strong⟩),
    (ex_4d, ⟨sonderlich, .nobody, ["sonderlich"], strong⟩)]

-- The words of each link occur in its example and in the form of its entry, so a link to the
-- wrong entry fails.
theorem links_attested :
    ∀ p ∈ links, ∀ w ∈ p.2.words,
      w.toList ∈ Datum.wordsOf p.1.primaryText ∧ w.toList <:+: p.2.item.form.toList := by
  decide +kernel

/-- The context of each example lies in the distribution of its item exactly when Zwarts judges the
example acceptable. -/
theorem judgments_predicted :
    ∀ p ∈ links, (p.1.judgment = .acceptable ↔ p.2.context.Admits p.2.distribution) := by
  decide +kernel

-- The entry of each item lists the context of an acceptable example among those in which the item
-- is attested, and the context of a starred example among those from which it is excluded.
theorem entries_agree :
    ∀ p ∈ links, (p.1.judgment = .acceptable → p.2.context ∈ p.2.item.attested) ∧
      (p.1.judgment ≠ .acceptable → p.2.context ∈ p.2.item.excluded) := by
  decide +kernel

end Zwarts1998
