module

public import Linglib.Data.Experiments.Schema

/-!
# Haspelmath2021: corpus counts (generated)

Auto-generated from `Linglib/Data/Corpus/Haspelmath2021.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The illustrative frequency figures of the paper's Appendix, gathered from the earlier literature to
make Universal 2 plausible: for seven languages, how often the arguments of each role take the more
and the less prominent value of a prominence scale. The A and P counts are of monotransitive clauses
and the R and T counts of ditransitive ones; each printed table gives one corpus on one scale.

## References

* [haspelmath-2021]
-/

@[expose] public section

namespace Haspelmath2021

open Data.Experiments

/-- The corpus study a table reports, as the paper cites it. -/
inductive Corpus where
  /-- Swedish (Dahl and Fraurud 1996: 51): Swedish -/
  | swedish
  /-- Movima (Bolivia; Haude 2014: 9): Movima -/
  | movima
  /-- Vera'a (Vanuatu; Haig and Schnell 2016: 599): Vera'a -/
  | veraa
  /-- English (Jäger 2007: 80, Table 3): English, monotransitive clauses -/
  | englishJager
  /-- Tahitian (Snyder 2003: 80, 329): Tahitian -/
  | tahitian
  /-- English (Thompson 1990): English, ditransitive clauses, pp. 243 and 244 -/
  | englishThompson
  /-- Finnish (Kaiser 2002: 9, 81): Finnish -/
  | finnish
  /-- German (Haspelmath 2004: 35): German -/
  | german
  deriving DecidableEq, Repr, Fintype

/-- The prominence scale a table reports, under the paper's heading. -/
inductive Scale where
  /-- Animacy: human against nonhuman for A and P, animate against inanimate for R and T -/
  | animacy
  /-- Full nominality: person form against full nominal -/
  | fullNominality
  /-- Definiteness: definite against indefinite -/
  | definiteness
  /-- Person: locuphoric (1/2) against aliophoric (3) -/
  | person
  /-- Givenness: old against new -/
  | givenness
  deriving DecidableEq, Repr, Fintype

/-- The role of the counted arguments. -/
inductive Role where
  /-- A: the agent of a monotransitive clause -/
  | a
  /-- P: the patient of a monotransitive clause -/
  | p
  /-- R: the recipient of a ditransitive clause -/
  | r
  /-- T: the theme of a ditransitive clause -/
  | t
  deriving DecidableEq, Repr, Fintype

/-- A row of Appendix: how often the arguments of a role take the more and the less prominent
value of a scale in a corpus, one row for each printed row of the Appendix's tables, whose
totals are the sums of the two counts. -/
structure Frequency where
  /-- The corpus. -/
  corpus : Corpus
  /-- The prominence scale. -/
  scale : Scale
  /-- The role of the counted arguments. -/
  role : Role
  /-- The number at the more prominent value: human or animate, person form, definite,
  locuphoric, old. -/
  prominent : ℕ
  /-- The number at the less prominent value. -/
  nonProminent : ℕ
  deriving DecidableEq, Repr

/-- The 20 rows of Appendix, in the paper's order; checked against the page images. -/
def frequencies : List Frequency :=
  [⟨.swedish, .animacy, .a, 1766, 1361⟩,
   ⟨.swedish, .animacy, .p, 580, 3896⟩,
   ⟨.movima, .animacy, .a, 896, 355⟩,
   ⟨.movima, .animacy, .p, 370, 885⟩,
   ⟨.veraa, .fullNominality, .a, 680, 115⟩,
   ⟨.veraa, .fullNominality, .p, 325, 580⟩,
   ⟨.englishJager, .definiteness, .a, 973, 32⟩,
   ⟨.englishJager, .definiteness, .p, 467, 538⟩,
   ⟨.englishJager, .person, .a, 803, 202⟩,
   ⟨.englishJager, .person, .p, 47, 958⟩,
   ⟨.tahitian, .animacy, .r, 329, 0⟩,
   ⟨.tahitian, .animacy, .t, 11, 318⟩,
   ⟨.englishThompson, .animacy, .r, 190, 6⟩,  -- p. 243
   ⟨.englishThompson, .animacy, .t, 9, 187⟩,  -- p. 243
   ⟨.englishThompson, .fullNominality, .r, 115, 81⟩,  -- p. 244
   ⟨.englishThompson, .fullNominality, .t, 11, 185⟩,  -- p. 244
   ⟨.finnish, .givenness, .r, 58, 23⟩,
   ⟨.finnish, .givenness, .t, 19, 62⟩,
   ⟨.german, .person, .r, 147, 94⟩,
   ⟨.german, .person, .t, 49, 192⟩]

end Haspelmath2021
