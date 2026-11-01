/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Semantics.Reference.Indefinite
public import Mathlib.Data.Finset.Grade
public import Linglib.Data.Examples.Haspelmath1997
public import Linglib.Fragments.English.Indefinites
public import Linglib.Fragments.Georgian.Indefinites
public import Linglib.Fragments.Finnish.Indefinites
public import Linglib.Fragments.HindiUrdu.Indefinites
public import Linglib.Fragments.Hungarian.Indefinites
public import Linglib.Fragments.German.Indefinites
public import Linglib.Fragments.Japanese.Indefinites
public import Linglib.Fragments.Kannada.Indefinites
public import Linglib.Fragments.Korean.Indefinites
public import Linglib.Fragments.Latin.Indefinites
public import Linglib.Fragments.Latvian.Indefinites
public import Linglib.Fragments.Mandarin.Indefinites
public import Linglib.Fragments.Quechua.Indefinites
public import Linglib.Fragments.Romance.Italian.Indefinites
public import Linglib.Fragments.Slavic.Russian.Indefinites
public import Linglib.Fragments.Swahili.Indefinites
public import Linglib.Fragments.Turkish.Indefinites
public import Linglib.Fragments.Yakut.Indefinites
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Haspelmath (1997): Indefinite Pronouns

This file formalizes Haspelmath's implicational map of indefinite functions and the claims
made over it: the adjacency requirement that every indefinite series cover a connected region of
the nine-function map, the two further principles of §4.5 restricting which connected regions
occur, and the series of eighteen languages of the 40-language sample as Appendix A draws them.

`attestedCombinations` is Table 4.1, the combinations of functions attested in the sample;
`Principle1` and `Principle2` are the restrictions of §4.5, which `excluded_connected` shows to be
independent of adjacency. A connected region with a second function contains a neighbour of each of
its functions, so a series covering a leaf of the map (specific known, direct negation, free choice)
covers the leaf's only neighbour (`mem_of_adjacent_eq_singleton`); the specific-known case is the
ban on the ABA syncretism, so a connected region covers an interval of the three specificity
functions (`ordConnected_specificityFunctions`).

The map itself is explained by the features of §5.6, binary properties of the functions such as
specificity and the scope of negation: the functions sharing a value of a feature form a contiguous
area (`contiguous`), the features tell every function apart but question, conditional and
comparative (`features_eq_iff`), and an original free-choice indefinite extended toward the specific
end loses one feature at each step (`substance_chain`), the steps that order the specificity
functions (`strictMono_features_toFunction`). The negation feature is anti-morphic in exactly the
licensing contexts realizing direct negation, but anti-additive in all of them only if *doubt* is
set aside (`carries_antiAdditive_iff`).

The paradigms verify the adjacency requirement (`sample_connected`), the overlap of series that the
book holds against contrast-based accounts of grammatical meaning (`sample_overlap`), and the
human/non-human distinction the book finds practically everywhere, which only the Latvian
*kaut*-series lacks (`disjoint_forms_person_thing`). The book's examples for fifteen of the
languages are the rows of `Data/Examples/Haspelmath1997.json`, one row for each variant the book
prints in a line; the figures cover the acceptable rows and exclude the starred ones
(`acceptable_covers`, `ungrammatical_excludes`).

## Implementation notes

The map is `Indefinite.implicationalMap` and the adjacency requirement on a region the
connectedness of the subgraph it induces; the book's numbering of the functions is
`HaspelmathFunction.number`, so Table 4.1 is entered in the book's digit notation. Each paradigm
follows the figure and text of its Appendix A section rather than Table 4.1 where the two
differ: Hungarian *akár-* is 4589 in the table but excluded from questions and admitted under
indirect negation in A.26, so it is entered as 5689. Finnish *hyvänsä* is entered with the
comparative, which the book restricts to equative standards, and Swahili CL-o CL-ote with the
comparative the book predicts without data; both are the book's own map-driven analyses. Series
that are not pronouns in the book's sense (Georgian free-choice *nebismieri*, Turkish *kimse*,
the Italian determiner *qualsiasi*) are omitted, so a paradigm need not cover all nine
functions.

The features of §5.6 do not make the map a subgraph of a hypercube on their values: irrealis and
question are adjacent and differ in scalarity and in the reversal of the scale, which classifies
only question, and question and conditional are adjacent and differ in nothing. What holds is that
adjacent functions differ in at most one feature classifying both (`card_distinguishes_le_one`);
the converse fails, question and comparative differing in nothing without being adjacent.

§5.6 counts both negation functions anti-additive, after van der Wouden, who holds that no verb
with negative properties is only monotone decreasing. The *doubt* context of
`PolarityItem.LicensingContext`, which realizes indirect negation, models *doubt* by his own sketch
of it as not believing the complement and is only downward entailing (`carries_antiAdditive_iff`,
`VanDerWouden1997.verb_strengths`), so the claim fails for *doubt* on that analysis.

A `Series` is an indefinite series with the region its Appendix A figure encloses, named as the book
names it. The region is the book's analysis of the series and not a lexical property of its members:
a figure records where a series is possible and not where it is preferred (Russian *-to* is drawn
over the functions of *-nibud'*, which is preferred there), and it fills cells the book has no data
for on the strength of the map (Yakut *da* and Mandarin bare interrogatives under indirect negation,
the Swahili comparative). For those cells `sample_connected` restates the map; it tests the
adjacency requirement on the others. Every language's series are those of its Fragment.

## TODO

* The book counts 95 geometrically possible combinations under the adjacency requirement; the
  encoded map has 108 connected regions, and no reading of the edges of Fig. 4.4 recovers the
  book's count.

## References

* [haspelmath-1997]
* [vanderwouden-1997]
-/

@[expose] public section

namespace Haspelmath1997

open Indefinite

/-! ### The map -/

variable {s : Finset HaspelmathFunction} {f g : HaspelmathFunction}

theorem mem_of_adjacent_eq_singleton (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : f ∈ s) (hfg : f.adjacent = [g]) : g ∈ s := by
  have := hs.coe_sort
  obtain ⟨⟨g', hg'⟩, hadj⟩ := h.preconnected.exists_adj_of_nontrivial ⟨f, hf⟩
  rw [SimpleGraph.induce_adj, implicationalMap_adj, hfg, List.mem_singleton] at hadj
  exact hadj ▸ hg'

theorem specificUnknown_mem_of_specificKnown_mem (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : .specificKnown ∈ s) : .specificUnknown ∈ s :=
  mem_of_adjacent_eq_singleton h hs hf rfl

theorem specificUnknown_mem_of_irrealis_mem (h : (implicationalMap.induce ↑s).Connected)
    (hk : .specificKnown ∈ s) (hi : .irrealis ∈ s) : .specificUnknown ∈ s :=
  specificUnknown_mem_of_specificKnown_mem h ⟨_, hk, _, hi, by decide⟩ hk

theorem ordConnected_specificityFunctions (h : (implicationalMap.induce ↑s).Connected) :
    (specificityFunctions s : Set SpecificityFunction).OrdConnected :=
  SpecificityFunction.ordConnected_iff.2 fun hk hn ↦ mem_specificityFunctions.2 <|
    specificUnknown_mem_of_irrealis_mem h (mem_specificityFunctions.1 hk)
      (mem_specificityFunctions.1 hn)

theorem indirectNeg_mem_of_directNeg_mem (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : .directNeg ∈ s) : .indirectNeg ∈ s :=
  mem_of_adjacent_eq_singleton h hs hf rfl

theorem comparative_mem_of_freeChoice_mem (h : (implicationalMap.induce ↑s).Connected)
    (hs : s.Nontrivial) (hf : .freeChoice ∈ s) : .comparative ∈ s :=
  mem_of_adjacent_eq_singleton h hs hf rfl

/-! ### The features behind the map

Haspelmath explains the arrangement of the map by binary features of the functions: whether the
referent is known to the speaker, whether the indefinite is specific, whether it denotes a scalar
endpoint and whether it is in the scope of negation, with two subclassifying features, the
reversal of the scale among the scalar endpoints and anti-morphicity among the negations. His
requirement is that the functions sharing a value of a feature form a contiguous area of the map
(`contiguous`). The features then tell every function apart but question, conditional and
comparative, whose relative position he explains otherwise (`features_eq_iff`), adjacent functions
differ in at most one feature (`card_distinguishes_le_one`), and an original free-choice
indefinite extended toward the specific end loses one feature at each step (`substance_chain`). -/

/-- The features by which Haspelmath explains the map, each named by its marked value, the one he
counts as semantic substance lost when an indefinite is extended to a weaker function. -/
inductive Feature where
  /-- The referent is unknown to the speaker. -/
  | unknown
  /-- The indefinite is non-specific. -/
  | nonSpecific
  /-- The indefinite denotes a scalar endpoint. -/
  | scalarEndpoint
  /-- The scalar endpoint lies on a reversed scale. -/
  | scaleReversal
  /-- The indefinite is in the scope of negation. -/
  | negation
  /-- The negation is anti-morphic. -/
  | antiMorphic
  deriving DecidableEq, Fintype, Repr

namespace Feature

/-- The functions with the marked value of a feature, as Haspelmath's diagrams draw them. -/
def marked : Feature → Finset HaspelmathFunction
  | unknown => {.specificUnknown, .irrealis, .question, .conditional, .indirectNeg, .directNeg,
      .comparative, .freeChoice}
  | nonSpecific => {.irrealis, .question, .conditional, .indirectNeg, .directNeg, .comparative,
      .freeChoice}
  | scalarEndpoint => {.question, .conditional, .indirectNeg, .directNeg, .comparative, .freeChoice}
  | scaleReversal => {.question, .conditional, .indirectNeg, .directNeg, .comparative}
  | negation => {.indirectNeg, .directNeg}
  | antiMorphic => {.directNeg}

/-- A feature classifies every function, but the reversal of the scale classifies only the scalar
endpoints and anti-morphicity only the negations. -/
def domain : Feature → Finset HaspelmathFunction
  | scaleReversal => scalarEndpoint.marked
  | antiMorphic => negation.marked
  | _ => Finset.univ

/-- The functions with the unmarked value of a feature. -/
def unmarked (φ : Feature) : Finset HaspelmathFunction := φ.domain \ φ.marked

theorem marked_subset_domain (φ : Feature) : φ.marked ⊆ φ.domain := by
  cases φ <;> decide

/-- A feature tells two functions apart when it classifies both and gives them different
values. -/
def Distinguishes (φ : Feature) (f g : HaspelmathFunction) : Prop :=
  f ∈ φ.domain ∧ g ∈ φ.domain ∧ (f ∈ φ.marked ↔ g ∉ φ.marked)

instance (φ : Feature) (f g : HaspelmathFunction) : Decidable (φ.Distinguishes f g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Feature

/-- The features whose marked value a function has. -/
def features (f : HaspelmathFunction) : Finset Feature := Finset.univ.filter (f ∈ ·.marked)

/-- The functions sharing a value of a feature form a contiguous area of the map. -/
theorem contiguous (φ : Feature) :
    (implicationalMap.induce ↑φ.marked).Connected ∧
      (implicationalMap.induce ↑φ.unmarked).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  cases φ <;> decide +kernel

theorem card_distinguishes_le_one :
    ∀ f g, implicationalMap.Adj f g →
      (Finset.univ.filter fun φ : Feature ↦ φ.Distinguishes f g).card ≤ 1 := by
  decide

/-- Question, conditional and comparative, which the features do not tell apart. -/
def undistinguished : Finset HaspelmathFunction := {.question, .conditional, .comparative}

theorem features_eq_iff :
    ∀ f g, features f = features g ↔ f = g ∨ f ∈ undistinguished ∧ g ∈ undistinguished := by
  decide

theorem substance_chain :
    features .specificKnown ⋖ features .specificUnknown ∧
      features .specificUnknown ⋖ features .irrealis ∧
      features .irrealis ⋖ features .freeChoice := by
  simp only [Finset.covBy_iff_exists_insert]
  decide +kernel

theorem strictMono_features_toFunction :
    StrictMono fun u : SpecificityFunction ↦ features u.toFunction := by
  decide

/-! ### Negation and the licensing contexts

Haspelmath subdivides the negation feature by two Boolean properties of the negating context: both
negation functions are anti-additive and only direct negation is anti-morphic. Among the licensing
contexts of `PolarityItem.LicensingContext` that realize a negation function, the anti-morphic ones
are exactly those realizing direct negation, but anti-additivity fails for *doubt*, whose licenser,
not believing the complement, is only downward entailing. -/

section Licensing

open PolarityItem LicensingContext

theorem carries_antiMorphic_iff {c : LicensingContext}
    (hc : ∃ f ∈ c.haspelmath, f ∈ Feature.negation.marked) :
    c.licenser.Carries .antiMorphic ↔ c.haspelmath = some .directNeg := by
  cases c <;> simp [LicensingContext.haspelmath, Feature.marked] at hc ⊢
  · exact Licenser.carries_classical_iff.2
      ⟨holds_negation .antiMorphic, not_isStrawsonUE_negation⟩
  · exact fun h ↦ absurd (holds_withoutClause_iff.1 (Licenser.carries_classical_iff.1 h).1)
      (by decide)
  · exact fun h ↦ absurd (holds_doubtVerb_iff.1 (Licenser.carries_classical_iff.1 h).1) (by decide)
  · exact fun h ↦ absurd (holds_denyVerb_iff.1 (Licenser.carries_classical_iff.1 h).1) (by decide)

theorem carries_antiAdditive_iff {c : LicensingContext}
    (hc : ∃ f ∈ c.haspelmath, f ∈ Feature.negation.marked) :
    c.licenser.Carries .antiAdditive ↔ c ≠ .doubtVerb := by
  cases c <;> simp [LicensingContext.haspelmath, Feature.marked] at hc ⊢
  · exact Licenser.carries_classical_iff.2
      ⟨holds_negation .antiAdditive, not_isStrawsonUE_negation⟩
  · exact Licenser.carries_classical_iff.2
      ⟨holds_withoutClause_iff.2 le_rfl, not_isStrawsonUE_withoutClause⟩
  · exact fun h ↦ absurd (holds_doubtVerb_iff.1 (Licenser.carries_classical_iff.1 h).1) (by decide)
  · exact Licenser.carries_classical_iff.2 ⟨holds_denyVerb_iff.2 le_rfl, not_isStrawsonUE_denyVerb⟩

end Licensing

/-! ### Table 4.1 and the principles of §4.5 -/

/-- `region ns` is the set of functions whose numbers are in `ns`, the book's digit notation. -/
def region (ns : List ℕ) : Finset HaspelmathFunction := Finset.univ.filter (·.number ∈ ns)

/-- The middle of the map is question, conditional, indirect negation and comparative. -/
def middle : Finset HaspelmathFunction := region [4, 5, 6, 8]

/-- A region satisfies Principle 1 if it covers at least three functions whenever it is confined
to the middle of the map. -/
def Principle1 (s : Finset HaspelmathFunction) : Prop := s ⊆ middle → 3 ≤ s.card

instance : DecidablePred Principle1 := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- A region satisfies Principle 2 if it does not combine specific known with the comparative or
free-choice function. -/
def Principle2 (s : Finset HaspelmathFunction) : Prop :=
  .specificKnown ∈ s → .comparative ∉ s ∧ .freeChoice ∉ s

instance : DecidablePred Principle2 := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- Table 4.1 lists the combinations of functions attested in the 40-language sample, each with
the series the table gives as its example. -/
def attestedCombinations : List (String × Finset HaspelmathFunction) :=
  [ ("Russian koe-", region [1]), ("Kazakh älde-", region [1, 2]),
    ("Serbian/Croatian ne-", region [1, 2, 3]), ("English some-", region [1, 2, 3, 4, 5]),
    ("German etwas", region [1, 2, 3, 4, 5, 6]), ("Swedish någon", region [1, 2, 3, 4, 5, 6, 7]),
    ("Kannada -oo", region [2]), ("Basque bait-", region [2, 3]),
    ("Latin ali-, Greek ka-", region [2, 3, 4, 5]),
    ("Portuguese qualquer", region [2, 3, 4, 5, 6, 7, 8, 9]),
    ("German irgend", region [2, 3, 4, 5, 6, 8, 9]), ("Russian -nibud'", region [3, 4, 5]),
    ("Ossetic is-", region [3, 4, 5, 6]), ("Greek tipota", region [3, 4, 5, 6, 7]),
    ("Nanay -daa", region [3, 4, 5, 6, 7, 8]), ("Hindi/Urdu bhii", region [3, 4, 5, 6, 7, 8, 9]),
    ("Lithuanian nors", region [3, 4, 5, 6, 8]), ("Dutch dan ook", region [3, 4, 5, 6, 8, 9]),
    ("Hebrew iš", region [4, 5, 6, 7]), ("Catalan cap", region [4, 5, 6, 7, 8]),
    ("English any", region [4, 5, 6, 7, 8, 9]), ("German je", region [4, 5, 6, 8]),
    ("Serbian/Croatian bilo", region [4, 5, 6, 8, 9]), ("Hungarian akár", region [4, 5, 8, 9]),
    ("Italian nessuno", region [4, 6, 7]), ("Finnish -kaan", region [4, 6, 7, 8]),
    ("Icelandic nokkur", region [4, 6, 8]), ("Russian by to ni bylo", region [5, 6, 8]),
    ("Bulgarian -to i da e", region [5, 6, 8, 9]), ("Modern Greek -dhipote", region [5, 8, 9]),
    ("Icelandic n-", region [6, 7]), ("Maltese ebda", region [6, 7, 8]),
    ("Kannada -uu", region [6, 7, 8, 9]), ("German jeder", region [6, 8, 9]),
    ("German n-", region [7]), ("Swedish som helst", region [8, 9]),
    ("Icelandic sem er", region [9]) ]

/-- The combinations Principle 1 lists as excluded. -/
def excludedByPrinciple1 : List (Finset HaspelmathFunction) :=
  [region [4], region [5], region [6], region [8], region [4, 5], region [4, 6], region [5, 8],
    region [6, 8]]

/-- The combinations Principle 2 lists as excluded. -/
def excludedByPrinciple2 : List (Finset HaspelmathFunction) :=
  [region [1, 2, 3, 4, 5, 6, 8], region [1, 2, 3, 4, 6, 7, 8], region [1, 2, 3, 4, 6, 8, 9],
    region [1, 2, 3, 4, 6, 7, 8, 9], region [1, 2, 3, 5, 8], region [1, 2, 3, 4, 5, 8, 9]]

theorem attested_connected :
    ∀ c ∈ attestedCombinations, (implicationalMap.induce ↑c.2).Connected := by
  -- Reachability from one function of a region is much cheaper to decide than between all pairs.
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

theorem attested_principles :
    ∀ c ∈ attestedCombinations, Principle1 c.2 ∧ Principle2 c.2 := by
  decide

-- Decide the quantifier by walking the list, not by enumerating every region of the map.
attribute [local instance high] List.decidableBAll in
theorem excluded_connected :
    ∀ s ∈ excludedByPrinciple1 ++ excludedByPrinciple2, (implicationalMap.induce ↑s).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

attribute [local instance high] List.decidableBAll in
theorem excluded_violate :
    (∀ s ∈ excludedByPrinciple1, ¬ Principle1 s) ∧
      ∀ s ∈ excludedByPrinciple2, ¬ Principle2 s := by
  decide +kernel

/-! ### Eighteen languages of the 40-language sample -/

/-- A `Series` is an indefinite series with the region of the map that its figure in Appendix A
encloses. Its name is the book's, by which the examples are tagged. -/
structure Series extends IndefinitePronoun.Series where
  /-- The functions the series covers. -/
  functions : Finset HaspelmathFunction
  deriving DecidableEq

/-- The English series (A.3, §4.3.1) are *some-* 12345, *any-* 456789 and *no-* 7. -/
def english : List Series :=
  [ { English.Indefinites.someSeries with functions := region [1, 2, 3, 4, 5] },
    { English.Indefinites.anySeries with functions := region [4, 5, 6, 7, 8, 9] },
    { English.Indefinites.noSeries with functions := region [7] } ]

/-- The Russian series (A.16) are *koe-* 1, *-to* 2345, *-nibud'* 345, *-libo* 34568, *by to ni
bylo* 568, *ni-* 7, and *ugodno* and the determiner *ljuboj* 9. The *-to*-series is mainly used
specifically but is not excluded from the functions of *-nibud'*, where *-nibud'* is preferred;
*-libo* replaces *-nibud'* under indirect negation and in comparatives. -/
def russian : List Series :=
  [ { Russian.Indefinites.koeSeries with functions := region [1] },
    { Russian.Indefinites.toSeries with functions := region [2, 3, 4, 5] },
    { Russian.Indefinites.nibudSeries with functions := region [3, 4, 5] },
    { Russian.Indefinites.liboSeries with functions := region [3, 4, 5, 6, 8] },
    { Russian.Indefinites.byToNiByloSeries with functions := region [5, 6, 8] },
    { Russian.Indefinites.niSeries with functions := region [7] },
    { Russian.Indefinites.ugodnoSeries with functions := region [9] },
    { Russian.Indefinites.ljubojSeries with functions := region [9] } ]

/-- The German series (A.1) are *etwas* 123456, *irgend-* 2345689, temporal *je* 4568, *jeder*
689 and *n-* 7. -/
def german : List Series :=
  [ { German.Indefinites.etwasSeries with functions := region [1, 2, 3, 4, 5, 6] },
    { German.Indefinites.irgendSeries with functions := region [2, 3, 4, 5, 6, 8, 9] },
    { German.Indefinites.jeSeries with functions := region [4, 5, 6, 8] },
    { German.Indefinites.jederSeries with functions := region [6, 8, 9] },
    { German.Indefinites.nSeries with functions := region [7] } ]

/-- The Latin series (A.6) are *-dam* 1, *ali-* 2345, *-quam* 4568, the negative series 7, and
*-vis* and *-libet* 9. -/
def latin : List Series :=
  [ { Latin.Indefinites.damSeries with functions := region [1] },
    { Latin.Indefinites.aliSeries with functions := region [2, 3, 4, 5] },
    { Latin.Indefinites.quamSeries with functions := region [4, 5, 6, 8] },
    { Latin.Indefinites.nSeries with functions := region [7] },
    { Latin.Indefinites.visSeries with functions := region [9] } ]

/-- The Yakut series (A.25) are *ere* 12, *eme* 345, *da* 6789 with indirect negation
predicted, and *bayarar* 9. -/
def yakut : List Series :=
  [ { Yakut.Indefinites.ereSeries with functions := region [1, 2] },
    { Yakut.Indefinites.emeSeries with functions := region [3, 4, 5] },
    { Yakut.Indefinites.daSeries with functions := region [6, 7, 8, 9] },
    { Yakut.Indefinites.bayararSeries with functions := region [9] } ]

/-- The Kannada series (A.35) are *-oo* 2, *-aadaruu* 345 and *-uu* 6789; no series expresses a
referent the speaker has in mind. -/
def kannada : List Series :=
  [ { Kannada.Indefinites.ooSeries with functions := region [2] },
    { Kannada.Indefinites.aadaruuSeries with functions := region [3, 4, 5] },
    { Kannada.Indefinites.uuSeries with functions := region [6, 7, 8, 9] } ]

/-- The Latvian series (A.18) are *kaut* 12345, the figure not separating the specific
functions, *ne-* 7 and *jeb-* 689. The bare interrogatives are also used as indefinites, *kāds*
'somebody' in conditionals and under indirect negation, and the figure draws no region for
them. -/
def latvian : List Series :=
  [ { Latvian.Indefinites.kautSeries with functions := region [1, 2, 3, 4, 5] },
    { Latvian.Indefinites.neSeries with functions := region [7] },
    { Latvian.Indefinites.jebSeries with functions := region [6, 8, 9] } ]

/-- The Japanese series (A.38) are *-ka* 12345, *-mo* 678 and *-demo* 9. -/
def japanese : List Series :=
  [ { Japanese.Indefinites.kaSeries with functions := region [1, 2, 3, 4, 5] },
    { Japanese.Indefinites.moSeries with functions := region [6, 7, 8] },
    { Japanese.Indefinites.demoSeries with functions := region [9] } ]

/-- The Mandarin Chinese series (A.36) are generic nouns 12, the bare interrogatives in all
non-specific non-emphatic functions 34567 (with no data for indirect negation), *dōu*/*yě* 7,
and the determiner *rènhé* 6789. -/
def mandarin : List Series :=
  [ { Mandarin.Indefinites.genericNounSeries with functions := region [1, 2] },
    { Mandarin.Indefinites.interrogativeSeries with functions := region [3, 4, 5, 6, 7] },
    { Mandarin.Indefinites.douSeries with functions := region [7] },
    { Mandarin.Indefinites.yeSeries with functions := region [7] },
    { Mandarin.Indefinites.renheSeries with functions := region [6, 7, 8, 9] } ]

/-- The Turkish series (A.23) are *bir-* 1234567, *hiç* 467 and *herhangi* 23456789. The figure
starts the *herhangi* outline at irrealis non-specific; the text admits either series in every
function from specific unknown to direct negation and gives *herhangi biri* as a
specific-unknown example, and the region follows the text. -/
def turkish : List Series :=
  [ { Turkish.Indefinites.birSeries with functions := region [1, 2, 3, 4, 5, 6, 7] },
    { Turkish.Indefinites.hiçSeries with functions := region [4, 6, 7] },
    { Turkish.Indefinites.herhangiSeries with functions := region [2, 3, 4, 5, 6, 7, 8, 9] } ]

/-- The Hindi/Urdu series (A.22) are *koii* 1234567 and *koii bhii* 3456789. -/
def hindi : List Series :=
  [ { HindiUrdu.Indefinites.koiiSeries with functions := region [1, 2, 3, 4, 5, 6, 7] },
    { HindiUrdu.Indefinites.bhiiSeries with functions := region [3, 4, 5, 6, 7, 8, 9] } ]

/-- The Italian series (A.10) are *qualche-* 123456, *nessuno* 467 (questions but not
conditionals) and *-unque* 89. -/
def italian : List Series :=
  [ { Italian.Indefinites.qualcheSeries with functions := region [1, 2, 3, 4, 5, 6] },
    { Italian.Indefinites.nessunoSeries with functions := region [4, 6, 7] },
    { Italian.Indefinites.unqueSeries with functions := region [8, 9] } ]

/-- The Finnish series (A.27) are *eräs* 1, *-kin* 2345, *-kaan* 4678, and *hyvänsä* 589 with
the comparative only as an equative standard. -/
def finnish : List Series :=
  [ { Finnish.Indefinites.eräsSeries with functions := region [1] },
    { Finnish.Indefinites.kinSeries with functions := region [2, 3, 4, 5] },
    { Finnish.Indefinites.kaanSeries with functions := region [4, 6, 7, 8] },
    { Finnish.Indefinites.hyvänsäSeries with functions := region [5, 8, 9] } ]

/-- The Korean series (A.39) are the bare interrogatives and *-nka*, alike at 123456, *-to* 678,
and *-na* and *-tunci* 9. -/
def korean : List Series :=
  [ { Korean.Indefinites.interrogativeSeries with functions := region [1, 2, 3, 4, 5, 6] },
    { Korean.Indefinites.nkaSeries with functions := region [1, 2, 3, 4, 5, 6] },
    { Korean.Indefinites.toSeries with functions := region [6, 7, 8] },
    { Korean.Indefinites.naSeries with functions := region [9] },
    { Korean.Indefinites.tunciSeries with functions := region [9] } ]

/-- The Hungarian series (A.26) are *vala-* 123456, *sem-* 7, and *akár-* and *bár-* 5689,
excluded from questions. The figure does not draw the marginal *né*-series. -/
def hungarian : List Series :=
  [ { Hungarian.Indefinites.valaSeries with functions := region [1, 2, 3, 4, 5, 6] },
    { Hungarian.Indefinites.semSeries with functions := region [7] },
    { Hungarian.Indefinites.akárSeries with functions := region [5, 6, 8, 9] },
    { Hungarian.Indefinites.bárSeries with functions := region [5, 6, 8, 9] } ]

/-- The Georgian series (A.34) are *-γac* 12, *-me* 34568 and *ara-* 7. The text also puts the
potential *vera-* and prohibitive *nura-* series in direct negation, where the figure does not
draw them, and free choice is expressed by the adjective *nebismieri*, not by a series. -/
def georgian : List Series :=
  [ { Georgian.Indefinites.γacSeries with functions := region [1, 2] },
    { Georgian.Indefinites.meSeries with functions := region [3, 4, 5, 6, 8] },
    { Georgian.Indefinites.araSeries with functions := region [7] } ]

/-- The Ancash Quechua series (A.37) are the bare interrogatives for the specific functions,
which the map of the language does not distinguish, and *-pis* 3456789. -/
def quechua : List Series :=
  [ { Quechua.Indefinites.interrogativeSeries with functions := region [1, 2] },
    { Quechua.Indefinites.pisSeries with functions := region [3, 4, 5, 6, 7, 8, 9] } ]

/-- The Swahili series (A.33) are generic nouns 1234567 and CL-o CL-ote 456789, with the
comparative predicted. -/
def swahili : List Series :=
  [ { Swahili.Indefinites.genericNounSeries with functions := region [1, 2, 3, 4, 5, 6, 7] },
    { Swahili.Indefinites.oOteSeries with functions := region [4, 5, 6, 7, 8, 9] } ]

/-- The eighteen languages. -/
def sample : List (List Series) :=
  [ english, russian, german, latin, yakut, kannada, latvian, japanese, mandarin, turkish, hindi,
    italian, finnish, korean, hungarian, georgian, quechua, swahili ]

theorem sample_connected :
    ∀ p ∈ sample, ∀ e ∈ p, (implicationalMap.induce ↑e.functions).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  decide +kernel

theorem sample_principles :
    ∀ p ∈ sample, ∀ e ∈ p, Principle1 e.functions ∧ Principle2 e.functions := by
  decide

theorem sample_overlap :
    ∀ p ∈ [english, russian, german, latin, yakut, mandarin, turkish, hindi, italian, finnish,
      korean, hungarian, swahili], ¬ p.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

theorem disjoint_forms_person_thing :
    ∀ p ∈ sample, ∀ s ∈ p, s.toSeries ≠ Latvian.Indefinites.kautSeries →
      Disjoint (s.forms .person) (s.forms .thing) := by
  decide +kernel

theorem not_disjoint_kaut_forms_person_thing :
    ¬ Disjoint (Latvian.Indefinites.kautSeries.forms .person)
      (Latvian.Indefinites.kautSeries.forms .thing) := by
  decide

theorem mo_comparative_with_negation :
    ∃ e ∈ japanese, .comparative ∈ e.functions ∧ .directNeg ∈ e.functions ∧
      .freeChoice ∉ e.functions := by
  decide

/-! ### The book's examples -/

/-- The paradigm of a language of the sample, by Glottocode; Latin, Yakut and Kannada have no
example rows. -/
def paradigm? (l : Glottocode) : Option (List Series) :=
  List.lookup l [(.english, english), (.russian, russian), (.latvian, latvian),
    (.german, german), (.japanese, japanese), (.mandarinChinese, mandarin),
    (.turkish, turkish), (.hindi, hindi), (.italian, italian), (.finnish, finnish),
    (.korean, korean), (.hungarian, hungarian), (.georgian, georgian),
    (.huaylasAncashQuechua, quechua), (.swahili, swahili)]

/-- The functions by the names the example rows give them. -/
def functionTable : List (String × HaspelmathFunction) :=
  [("specificKnown", .specificKnown), ("specificUnknown", .specificUnknown),
    ("irrealis", .irrealis), ("question", .question), ("conditional", .conditional),
    ("indirectNeg", .indirectNeg), ("directNeg", .directNeg), ("comparative", .comparative),
    ("freeChoice", .freeChoice)]

/-- The region the figure of an example's language draws for a series. -/
def region? (e : Datum) (label : String) : Option (Finset HaspelmathFunction) :=
  (paradigm? e.language).bind fun p ↦ (p.find? (·.name = label)).map (·.functions)

/-- The figure draws the series over the function the example illustrates. -/
def Covers (e : Datum) (label : String) : Prop :=
  ∃ f ∈ e.parse? "function" functionTable, ∃ r ∈ region? e label, f ∈ r

/-- The figure leaves the function the example illustrates outside the series. -/
def Excludes (e : Datum) (label : String) : Prop :=
  ∃ f ∈ e.parse? "function" functionTable, ∃ r ∈ region? e label, f ∉ r

instance (e : Datum) (label : String) : Decidable (Covers e label) :=
  inferInstanceAs (Decidable (∃ f ∈ _, ∃ r ∈ _, _))

instance (e : Datum) (label : String) : Decidable (Excludes e label) :=
  inferInstanceAs (Decidable (∃ f ∈ _, ∃ r ∈ _, _))

theorem acceptable_covers :
    ∀ e ∈ Examples.all, e.judgment = .acceptable → ∀ l ∈ e.features "series", Covers e l := by
  decide +kernel

theorem ungrammatical_excludes :
    ∀ e ∈ Examples.all, e.judgment = .ungrammatical → e.context = "" →
      ∀ l ∈ e.features "series", Excludes e l := by
  decide +kernel

end Haspelmath1997
