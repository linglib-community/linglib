module

public import Linglib.Languages.Romance.Italian.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Data.Examples.MaidenRobustelli2007
public import Linglib.Data.Examples.Readers

/-!
# Maiden and Robustelli (2007): Italian negative words and negative polarity

The Italian negative pronouns *nessuno* and *niente* follow *non* or *senza* 'without', and in
colloquial usage they mean 'anybody' and 'anything' in questions. *Mai* means 'never' with a
negation and 'ever' in questions, superlatives, and comparatives. In formal usage *alcuno* replaces
*nessuno* in negative sentences, and *affatto* 'at all' occurs only in negative sentences. Each
example is linked to the lexical entry of the word it prints and to the named context in which the
word stands. [The entry lists that context among those in
which the word is attested](##MaidenRobustelli2007.entries_agree), and [the entries of the six
words are compatible with the class of weak negative polarity
items](##MaidenRobustelli2007.compatible_weak).

## Implementation notes

* *Non credo che* 'I don't think that' is linked to negation over a neg-raising attitude, and the
  fixed expression *più che mai* 'more than ever' is linked to the clausal comparative.
* A link records the word as it is printed, such as apocopated *alcun* or a variant of *neanche*,
  and the word is checked against the form of the entry.

## References

* [maiden-robustelli-2007]
-/

@[expose] public section

namespace MaidenRobustelli2007

open PolarityItem Italian.PolarityItems Examples

/-- A link from an example to the lexical entry of the word it prints and to the named context in
which the word stands. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The context in which the word stands. -/
  context : LicensingContext
  /-- The word as printed. -/
  word : String

/-- The links of the examples. -/
def links : List (Datum × Link) :=
  [(haiDimenticato, ⟨niente, .polarQuestion, "niente"⟩),
    (ceNessuno, ⟨nessuno, .polarQuestion, "nessuno"⟩),
    (ceNiente, ⟨niente, .polarQuestion, "niente"⟩),
    (nonCredo, ⟨nessuno, .superordinateNegation, "nessuno"⟩),
    (senzaNiente, ⟨niente, .withoutClause, "niente"⟩),
    (senzaDentroNessuno, ⟨nessuno, .withoutClause, "nessuno"⟩),
    (nonHaAlcun, ⟨alcuno, .negation, "alcun"⟩), (nonHoVistoAlcuno, ⟨alcuno, .negation, "alcuno"⟩),
    (senzaAlcuno, ⟨alcuno, .withoutClause, "alcuno"⟩), (nonGlieloDaro, ⟨mai, .negation, "mai"⟩),
    (haiMaiLetto, ⟨mai, .polarQuestion, "mai"⟩), (piuDolce, ⟨mai, .superlative, "mai"⟩),
    (affattoSparito, ⟨affatto, .negation, "affatto"⟩),
    (affattoFascista, ⟨affatto, .negation, "affatto"⟩),
    (piuCheMai, ⟨mai, .clausalComparative, "mai"⟩),
    (nonEArrivato, ⟨nessuno, .negation, "nessuno"⟩), (nonHoAmato, ⟨nessuno, .negation, "nessuno"⟩),
    (nonVidiNiente, ⟨niente, .negation, "niente"⟩), (nonLHoMai, ⟨mai, .negation, "mai"⟩),
    (neancheAScuola, ⟨neanche, .negation, "neanche"⟩),
    (nemmenoInSogno, ⟨neanche, .negation, "nemmeno"⟩), (nessunoEMai, ⟨mai, .nobody, "mai"⟩),
    (senzaIncontrare, ⟨nessuno, .withoutClause, "nessuno"⟩)]

-- The word of each link occurs in its example and is part of the form of its entry, so a link to
-- the wrong entry fails.
theorem links_attested :
    ∀ p ∈ links, p.2.word.toList ∈ Datum.wordsOf p.1.primaryText ∧
      p.2.word.toList <:+: p.2.item.form.toList := by
  decide +kernel

/-- Every example is acceptable, and the entry of its item lists its context among those in which
the item is attested. -/
theorem entries_agree :
    ∀ p ∈ links, p.1.judgment = .acceptable ∧ p.2.context ∈ p.2.item.attested := by
  decide +kernel

-- Each context that an entry lists is the context of an example of the item.
theorem contexts_linked :
    ∀ e ∈ [nessuno, niente, neanche, mai, alcuno, affatto], ∀ c ∈ e.attested ∪ e.excluded,
      ∃ p ∈ links, p.2.item.form = e.form ∧ p.2.context = c := by
  decide +kernel

/-- The entries of the six words are compatible with the class of weak negative polarity
items. -/
theorem compatible_weak :
    ∀ e ∈ [nessuno, niente, neanche, mai, alcuno, affatto], e.Compatible (.npi .weak) := by
  decide +kernel

end MaidenRobustelli2007
