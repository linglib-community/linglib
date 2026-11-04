module

public import Linglib.Data.Statistics.Schema

/-!
# Haspelmath2001: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Haspelmath2001.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The figures of world-wide surveys that the chapter cites for its criterion (iv), and its Table 107.1
on comitative-instrumental syncretism.

## References

* [haspelmath-2001]
-/

@[expose] public section

namespace Haspelmath2001

open Data.Statistics

/-- The twelve features of section 2. -/
inductive Feature where
  /-- articles: definite and indefinite articles, section 2.1 -/
  | articles
  /-- relativePronouns: relative clauses with relative pronouns, section 2.2 -/
  | relativePronouns
  /-- havePerfect: the 'have'-perfect, section 2.3 -/
  | havePerfect
  /-- nominativeExperiencers: nominative experiencers, section 2.4 -/
  | nominativeExperiencers
  /-- participialPassive: the participial passive, section 2.5 -/
  | participialPassive
  /-- anticausativeProminence: anticausative prominence, section 2.6 -/
  | anticausativeProminence
  /-- dativeExternalPossessors: dative external possessors, section 2.7 -/
  | dativeExternalPossessors
  /-- negativeIndefinitesWithoutVerbalNegation: negative pronouns and lack of verbal negation,
  section 2.8 -/
  | negativeIndefinitesWithoutVerbalNegation
  /-- particleComparative: particles in comparative constructions, section 2.9 -/
  | particleComparative
  /-- relativeBasedEquative: relative-based equative constructions, section 2.10 -/
  | relativeBasedEquative
  /-- strictAgreement: subject person affixes as strict agreement markers, section 2.11 -/
  | strictAgreement
  /-- intensifierReflexiveDifferentiation: intensifier-reflexive differentiation, section 2.12 -/
  | intensifierReflexiveDifferentiation
  deriving DecidableEq, Repr, Fintype

/-- The rows of Table 107.1. -/
inductive Area where
  /-- Europe: Europe -/
  | europe
  /-- Africa: Africa -/
  | africa
  /-- Americas: Americas -/
  | americas
  /-- Asia: Asia -/
  | asia
  /-- Oceania: Oceania -/
  | oceania
  /-- World: World -/
  | world
  deriving DecidableEq, Repr, Fintype

/-- A row of section 2, pp. 1494-1500: a world-wide survey cited for a feature: how many
languages of its sample have the feature. -/
structure Survey where
  /-- The feature. -/
  feature : Feature
  /-- The languages of the sample with the feature. -/
  withFeature : ℕ
  /-- The languages of the sample. -/
  sample : ℕ
  deriving DecidableEq, Repr

/-- The 5 rows of section 2, pp. 1494-1500, in the paper's order; from a sample of languages
coded from their descriptions; checked against the page images. -/
def surveys : List Survey :=
  [⟨.articles, 31, 400⟩,  -- Both articles; p. 1494 says a sample of about 400.
   ⟨.participialPassive, 4, 80⟩,  -- A participle plus an intransitive auxiliary, p. 1497.
   ⟨.negativeIndefinitesWithoutVerbalNegation, 5, 40⟩,  -- p. 1499.
   ⟨.particleComparative,  -- p. 1499 prints 19 as the sample; 18 with the feature and 4 European languages without it make 22 at least, and stassen-1985, p. 10, says 110.
     18,
     110⟩,
   ⟨.strictAgreement, 2, 272⟩]  -- p. 1500.

/-- A row of Table 107.1, p. 1503: comitative-instrumental syncretism by area, the languages and
the percentage of each type; a mixed type is left out, so the percentages do not add up to
100. -/
structure Table1071Row where
  /-- The syncretic languages. -/
  syncretic : ℕ
  /-- Their percentage. -/
  syncreticPercent : Decimal
  /-- The non-syncretic languages. -/
  nonSyncretic : ℕ
  /-- Their percentage. -/
  nonSyncreticPercent : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 107.1, p. 1503, by area; from a sample of languages coded from their
descriptions; checked against the page images. -/
def table1071 : Area → Table1071Row
  | .europe => ⟨25, ⟨49, 0⟩, 16, ⟨31, 0⟩⟩
  | .africa => ⟨20, ⟨31, 0⟩, 38, ⟨58, 0⟩⟩
  | .americas => ⟨16, ⟨21, 0⟩, 54, ⟨69, 0⟩⟩
  | .asia => ⟨12, ⟨18, 0⟩, 47, ⟨71, 0⟩⟩
  | .oceania => ⟨6, ⟨10, 0⟩, 54, ⟨86, 0⟩⟩
  | .world => ⟨79, ⟨24, 0⟩, 209, ⟨65, 0⟩⟩

end Haspelmath2001
