module

public import Linglib.Data.Examples.ChengCheng2026
public import Linglib.Morphology.DistributedMorphology.RootCategorization
public import Studies.Harley2017

/-!
# Cheng and Cheng (2026): Using light verbs as verbalizers

Cheng and Cheng analyze the Mandarin light verb *dǎ* 'hit' as a rootless exponent of the
verbalizer, a head below the causative *gěi* and Voice *bǎ*. In *dǎ*+R (*dǎ-sǎo* 'clean') a root
adjoins to the verbalizer; in *dǎ*+N (*dǎ diànhuà* 'make a phone call') the verbalizer takes a
noun phrase.

## Main statements

* `topDown_eq_iff`: the heads realize *bǎ*, *gěi*, *dǎ* as in (30) iff v, the lower Caus and
  Voice head separate projections.
* `diagnostics_iff`: the judgments of (44), (46), (48) and (49) follow from whether *dǎ* shares a
  complex head with the root after it.
* `x0At_tree_lexicon`: under both attachments the root shares the complex head of *dǎ*.
* `mayCondition'_rootPos_daPos_iff`: *dǎ* is local to the root after it in *dǎ*+R only.

## Implementation notes

* Heads are parts of an interval partition of `Harley2017.Feature`. The paper's causative v is
  Harley's lower Caus, which Harley takes to be productive; the paper's (28) calls it lexical.
* One linking hypothesis connects the tests to structure: a form separating *dǎ* from what
  follows it is acceptable iff the two do not share a complex head.
* `Combination.ShareHead` compares complex heads as trees, which suffices because the heads
  compared differ in shape.

## TODO

* §5.4 attributes the idiosyncrasy of *dǎ*+N to a First Phase defined by *dǎ*, but the noun's
  root is not local to *dǎ*. Whether it belongs to idioms below Voice (`ComplexHead.IdiomLocal`)
  or to the noun, which (68) bears on, needs sourced data on *diànhuà*.
* Whether *dǎ-yíng* (22) admits the potential infix, the mark of a resultative in footnote 20,
  needs a sourced judgment.
* The independence claims of §3 beyond `subsetPrinciple_v`, and the light verbs of §6.3.

## References

* [cheng-cheng-2026]
* [harley-2017]
* [sybesma-2021]
* [alexiadou-lohndal-2017]
* [bobaljik-harley-2017]
-/

@[expose] public section

namespace ChengCheng2026

open DistributedMorphology DistributedMorphology.RootCategorization Morphology.Exponence
open Harley2017 (Feature)
open PhraseStructure Core.Order

/-! ### Three heads -/

/-- The exponents of the heads in (30). -/
inductive Exponent where
  /-- The light verb *dǎ*. -/
  | da
  /-- The causative *gěi*. -/
  | gei
  /-- Voice *bǎ*. -/
  | ba
  deriving DecidableEq, Repr

/-- Exponent names as they appear in the data. -/
def exponentTable : List (String × Exponent) := [("dǎ", .da), ("gěi", .gei), ("bǎ", .ba)]

/-- The context-free items *dǎ* for v, *gěi* for the lower Caus and *bǎ* for Voice; the last two
follow [sybesma-2021]. -/
def vocabulary : RuleSet (VocabularyItem Feature Exponent) :=
  [{.v} ⟷ .da, {.caus₁} ⟷ .gei, {.voice} ⟷ .ba]

theorem subsetPrinciple_v (l r : List (Finset Feature)) :
    subsetPrinciple vocabulary ⟨{.v}, l, r⟩ = some .da := by
  rw [subsetPrinciple_eq_head?_applicable (by decide)]
  simp [RuleSet.applicable, vocabulary]

/-- The exponents of the heads bearing Voice, the lower Caus and v, in that order. -/
def topDown (P : IntervalPartition Feature) : List (Option Exponent) :=
  [.voice, .caus₁, .v].map fun f ↦ subsetPrinciple vocabulary (P.part f)

/-- The exponents a datum lists, in surface order. -/
def exponents (d : Datum) : List Exponent :=
  (d.features "exponent").filterMap (exponentTable.lookup ·)

theorem exponents_ex_30 :
    ∀ d ∈ [Examples.ex_30a, Examples.ex_30b], exponents d = [.ba, .gei, .da] := by
  decide +kernel

/-- An interval partition of v, the lower Caus and Voice realizes the exponents of (30) iff it is
discrete. -/
theorem topDown_eq_iff {P : IntervalPartition Feature} (hs : P.support = {.v, .caus₁, .voice})
    {d : Datum} (hd : d ∈ [Examples.ex_30a, Examples.ex_30b]) :
    topDown P = (exponents d).map some ↔ P = .discrete {.v, .caus₁, .voice} := by
  rw [exponents_ex_30 d hd]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [topDown, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [← hs, IntervalPartition.eq_discrete_iff_injOn, hs]
    intro x hx y hy hxy
    simp at hx hy
    grind
  · subst h
    simp [topDown]
    decide

/-! ### Separability -/

/-- The two kinds of combination with *dǎ*. -/
inductive Combination where
  /-- *dǎ*+R, as in *dǎ-sǎo* 'clean'. -/
  | root
  /-- *dǎ*+N, as in *dǎ diànhuà* 'make a phone call'. -/
  | noun
  deriving DecidableEq, Repr

/-- Combination names as they appear in the data. -/
def combinationTable : List (String × Combination) := [("R", .root), ("N", .noun)]

/-- The lexicon of the *dǎ*+R structure, with trivial words. -/
def lexicon : Lexicon Unit := ⟨.v, (), (), ()⟩

/-- The *dǎ*+N structure (53): the verbalizer over an nP. -/
def nounTree : Tree Cat Unit :=
  .node (.cat .v) [.terminal (.cat .v) (), .node (.cat .n) [complexHead ⟨.n, (), (), ()⟩]]

namespace Combination

/-- The structure of a combination; for *dǎ*+R, the adjunction structure (50). -/
def tree : Combination → Tree Cat Unit
  | root => Attachment.modifier.tree lexicon
  | noun => nounTree

/-- The position of *dǎ*. -/
def daPos : Combination → TreePath
  | root => ⟨[0, 1]⟩
  | noun => ⟨[0]⟩

/-- The position of the root after *dǎ*. -/
def rootPos : Combination → TreePath
  | root => RootCategorization.rootPos
  | noun => ⟨[1, 0, 0]⟩

/-- *dǎ* and the root after it lie in one complex head. -/
def ShareHead (c : Combination) : Prop := x0At c.tree c.daPos = x0At c.tree c.rootPos

instance (c : Combination) : Decidable c.ShareHead := inferInstanceAs (Decidable (_ = _))

end Combination

/-- Under either attachment, *dǎ* and the root lie in one complex head. -/
theorem x0At_tree_lexicon (a : Attachment) :
    x0At (a.tree lexicon) ⟨[0, 1]⟩ = x0At (a.tree lexicon) RootCategorization.rootPos := by
  cases a <;> rfl

/-- The combination a datum tests, and whether its form separates *dǎ* from what follows it. -/
def test? (d : Datum) : Option (Combination × Bool) := do
  let c ← d.parse? "combination" combinationTable
  let s ← d.parse? "separated" [("yes", true), ("no", false)]
  pure (c, s)

theorem length_filterMap_test? : (Examples.all.filterMap test?).length = 12 := by decide +kernel

/-- A test form is acceptable iff it keeps *dǎ* with what follows it or the two lie in different
complex heads. -/
theorem diagnostics_iff : ∀ d ∈ Examples.all, ∀ p ∈ test? d,
    d.judgment = .acceptable ↔ (p.2 = true → ¬ p.1.ShareHead) := by
  decide +kernel

/-! ### Locality of the root -/

/-- *dǎ* is local to the root after it iff the combination is *dǎ*+R. -/
theorem mayCondition'_rootPos_daPos_iff (c : Combination) :
    MayCondition' c.tree c.rootPos c.daPos ↔ c = .root := by
  cases c <;> decide

end ChengCheng2026
