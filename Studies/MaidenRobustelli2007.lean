module

public import Linglib.Fragments.Romance.Italian.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Data.Examples.MaidenRobustelli2007
public import Linglib.Data.Examples.Readers

/-!
# Maiden and Robustelli (2007): Italian negative words and negative polarity

The Italian negative pronouns *nessuno* and *niente* follow *non* or *senza* 'without', and
colloquially mean 'anybody', 'anything' in questions; *mai* is 'never' with a negation and 'ever' in
questions, superlatives and comparatives; formal *alcuno* replaces *nessuno* in negative sentences,
and *affatto* 'at all' is used only in negative ones. Each example is linked to the Fragment entry
of the word it prints and to the named context it stands in, and the licensing theory [admits every
example](##MaidenRobustelli2007.acceptable_admitted).

## Implementation notes

* *Non credo che* 'I don't think that' is linked to negation over a neg-raising attitude, and the
  fixed expression *più che mai* 'more than ever' to the clausal comparative.
* A link records the word as printed, apocopated *alcun* or a variant of *neanche*, and checks it
  against the entry's form.

## References

* [maiden-robustelli-2007]
-/

@[expose] public section

namespace MaidenRobustelli2007

open PolarityItem Italian.PolarityItems Examples

/-- A link from an example to the Fragment entry of the word it prints and the named context the
word stands in. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The context it stands in. -/
  context : LicensingContext
  /-- The word as printed. -/
  word : String

/-- The links of the examples. -/
def links : List (Datum × Link) :=
  [(haiDimenticato, ⟨niente, .question, "niente"⟩), (ceNessuno, ⟨nessuno, .question, "nessuno"⟩),
    (ceNiente, ⟨niente, .question, "niente"⟩),
    (nonCredo, ⟨nessuno, .superordinateNegation, "nessuno"⟩),
    (senzaNiente, ⟨niente, .withoutClause, "niente"⟩),
    (senzaDentroNessuno, ⟨nessuno, .withoutClause, "nessuno"⟩),
    (nonHaAlcun, ⟨alcuno, .negation, "alcun"⟩), (nonHoVistoAlcuno, ⟨alcuno, .negation, "alcuno"⟩),
    (senzaAlcuno, ⟨alcuno, .withoutClause, "alcuno"⟩), (nonGlieloDaro, ⟨mai, .negation, "mai"⟩),
    (haiMaiLetto, ⟨mai, .question, "mai"⟩), (piuDolce, ⟨mai, .superlative, "mai"⟩),
    (affattoSparito, ⟨affatto, .negation, "affatto"⟩),
    (affattoFascista, ⟨affatto, .negation, "affatto"⟩),
    (piuCheMai, ⟨mai, .clausalComparative, "mai"⟩),
    (nonEArrivato, ⟨nessuno, .negation, "nessuno"⟩), (nonHoAmato, ⟨nessuno, .negation, "nessuno"⟩),
    (nonVidiNiente, ⟨niente, .negation, "niente"⟩), (nonLHoMai, ⟨mai, .negation, "mai"⟩),
    (neancheAScuola, ⟨neanche, .negation, "neanche"⟩),
    (nemmenoInSogno, ⟨neanche, .negation, "nemmeno"⟩), (nessunoEMai, ⟨mai, .nobody, "mai"⟩),
    (senzaIncontrare, ⟨nessuno, .withoutClause, "nessuno"⟩)]

-- each link's word is a word of its example and part of its entry's form, so a link to the wrong
-- entry fails
theorem links_attested :
    ∀ p ∈ links, p.2.word.toList ∈ Datum.wordsOf p.1.primaryText ∧
      p.2.word.toList <:+: p.2.item.form.toList := by
  decide +kernel

/-- The licensing theory admits the item of every example in the context it stands in. -/
theorem acceptable_admitted :
    ∀ p ∈ links, p.1.judgment = .acceptable ∧ p.2.context.licenser.Admits p.2.item := by
  decide +kernel

end MaidenRobustelli2007
