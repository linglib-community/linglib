module

public import Linglib.Data.Examples.ChengCheng2026
public import Linglib.Morphology.DistributedMorphology.RootCategorization
public import Studies.Harley2017

/-!
# Cheng and Cheng (2026): Using light verbs as verbalizers

Cheng and Cheng take the Mandarin light verb *dǎ* 'hit' to be a rootless exponent of the
verbalizer, a head of its own below the causative *gěi* and Voice *bǎ*. Merged with a root, as
in *dǎ-sǎo* 'clean', the verbalizer shares its complex head with the root and nothing comes
between them; over a noun, as in *dǎ diànhuà* 'make a phone call', it takes a noun phrase that an
aspect marker, a verb-doubling cleft, a fragment answer and ellipsis can each leave behind.

## Main statements

* `topDown_eq_iff`: a clause pronouncing *bǎ*, *gěi* and *dǎ*, as (30) does, heads v, the lower
  Caus and Voice separately, and the separate heads pronounce them in that order.
* `diagnostics_iff`: each judgment of (44), (46), (48) and (49) follows from whether *dǎ* and
  what follows it share a complex head.
* `x0At_tree_lexicon`: a root merged as complement or as modifier shares the complex head of *dǎ*
  alike, so the four tests cannot decide between the attachments.
* `mayCondition'_rootPos_daPos_iff`: *dǎ* is local to the root of what follows it with a root and
  not over a noun.

## Implementation notes

* The heads are the parts of an interval partition of Harley's projections
  (`Harley2017.Feature`). The causative between *dǎ* and *bǎ* is Harley's lower Caus, which
  Harley takes to be productive; the paper's rendering of Harley's hierarchy calls it lexical.
* A test separates *dǎ* from what follows it or keeps them together. The linking hypothesis is
  that a separating form is acceptable exactly when the two do not share a complex head.
* The trees are those of (50) and (53), with no words. `Combination.ShareHead` compares the
  complex heads containing the two positions, which differ in shape wherever they differ.

## TODO

* §5.4 places the idiosyncrasy of *dǎ*+N in a First Phase that *dǎ* defines, while the noun's
  root is not local to *dǎ* (`mayCondition'_rootPos_daPos_iff`); the idiosyncrasy would then
  belong to idioms below Voice (`ComplexHead.IdiomLocal`) or to the noun's own reading, and
  (68)'s reading of *sān-ge diànhuà* as calls needs a sourced use of *diànhuà* without *dǎ* to
  decide.
* Whether (22)'s achievement *dǎ-yíng* admits the potential infix, which footnote 20 takes to mark
  a resultative, needs a sourced judgment.
* §3's independence of transitivity, Voice, aspect and tense, beyond the context-free insertion
  of *dǎ* (`subsetPrinciple_v`), and §6.3's *zuò*, *kāi* and *chū*.

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

/-- The exponents of the three heads of (30). -/
inductive Exponent where
  /-- The light verb *dǎ*. -/
  | da
  /-- The causative *gěi*. -/
  | gei
  /-- Voice *bǎ*. -/
  | ba
  deriving DecidableEq, Repr

/-- The exponents as the rows name them. -/
def exponentTable : List (String × Exponent) := [("dǎ", .da), ("gěi", .gei), ("bǎ", .ba)]

/-- *dǎ* realizes v, *gěi* the lower Caus and *bǎ* Voice, each whatever its context, as Sybesma
takes *gěi* and *bǎ* ([sybesma-2021]). -/
def vocabulary : RuleSet (VocabularyItem Feature Exponent) :=
  [{.v} ⟷ .da, {.caus₁} ⟷ .gei, {.voice} ⟷ .ba]

/-- A head bearing v alone is pronounced *dǎ*, whatever surrounds it. -/
theorem subsetPrinciple_v (l r : List (Finset Feature)) :
    subsetPrinciple vocabulary ⟨{.v}, l, r⟩ = some .da := by
  rw [subsetPrinciple_eq_head?_applicable (by decide)]
  simp [RuleSet.applicable, vocabulary]

/-- The exponents of the heads of Voice, the lower Caus and v, from the top down. -/
def topDown (P : IntervalPartition Feature) : List (Option Exponent) :=
  [.voice, .caus₁, .v].map fun f ↦ subsetPrinciple vocabulary (P.part f)

/-- The exponents a row pronounces, in surface order. -/
def exponents (d : Datum) : List Exponent :=
  (d.features "exponent").filterMap (exponentTable.lookup ·)

theorem exponents_ex_30 :
    ∀ d ∈ [Examples.ex_30a, Examples.ex_30b], exponents d = [.ba, .gei, .da] := by
  decide +kernel

/-- **The split, derived.** Over v, the lower Caus and Voice, the heads pronounce *bǎ*, *gěi* and
*dǎ* from the top down, as each clause of (30) does, exactly when each heads its own projection. -/
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

/-- The two combinations of *dǎ*. -/
inductive Combination where
  /-- *dǎ* with a root, as in *dǎ-sǎo* 'clean'. -/
  | root
  /-- *dǎ* over a noun, as in *dǎ diànhuà* 'make a phone call'. -/
  | noun
  deriving DecidableEq, Repr

/-- The combinations as the rows name them. -/
def combinationTable : List (String × Combination) := [("R", .root), ("N", .noun)]

/-- The verbalizer realized *dǎ* with a root and an object, the words left out. -/
def lexicon : Lexicon Unit := ⟨.v, (), (), ()⟩

/-- The verbalizer realized *dǎ* over a noun phrase, the noun's root categorized by n (53). -/
def nounTree : Tree Cat Unit :=
  .node (.cat .v) [.terminal (.cat .v) (), .node (.cat .n) [complexHead ⟨.n, (), (), ()⟩]]

namespace Combination

/-- The structure of a combination, the root adjoined to the verbalizer as in (50). -/
def tree : Combination → Tree Cat Unit
  | root => Attachment.modifier.tree lexicon
  | noun => nounTree

/-- The position of *dǎ*. -/
def daPos : Combination → TreePath
  | root => ⟨[0, 1]⟩
  | noun => ⟨[0]⟩

/-- The position of the root of what follows *dǎ*. -/
def rootPos : Combination → TreePath
  | root => RootCategorization.rootPos
  | noun => ⟨[1, 0, 0]⟩

/-- *dǎ* and the root of what follows it share a complex head. -/
def ShareHead (c : Combination) : Prop := x0At c.tree c.daPos = x0At c.tree c.rootPos

instance (c : Combination) : Decidable c.ShareHead := inferInstanceAs (Decidable (_ = _))

end Combination

/-- Under either attachment *dǎ* and the root share a complex head, so the four tests cannot
decide between the attachments. -/
theorem x0At_tree_lexicon (a : Attachment) :
    x0At (a.tree lexicon) ⟨[0, 1]⟩ = x0At (a.tree lexicon) RootCategorization.rootPos := by
  cases a <;> rfl

/-- The combination a row tests, and whether its form separates *dǎ* from what follows it. -/
def test? (d : Datum) : Option (Combination × Bool) := do
  let c ← d.parse? "combination" combinationTable
  let s ← d.parse? "separated" [("yes", true), ("no", false)]
  pure (c, s)

/-- Twelve rows are tests, so `diagnostics_iff` is not vacuous. -/
theorem length_filterMap_test? : (Examples.all.filterMap test?).length = 12 := by decide +kernel

/-- **Separability from structure.** A form of (44), (46), (48) or (49) is acceptable exactly when
it keeps *dǎ* with what follows it or the two do not share a complex head. -/
theorem diagnostics_iff : ∀ d ∈ Examples.all, ∀ p ∈ test? d,
    d.judgment = .acceptable ↔ (p.2 = true → ¬ p.1.ShareHead) := by
  decide +kernel

/-! ### Locality of the root -/

/-- *dǎ* is local to the root of what follows it, and may fix its reading, exactly when it
categorizes that root. -/
theorem mayCondition'_rootPos_daPos_iff (c : Combination) :
    MayCondition' c.tree c.rootPos c.daPos ↔ c = .root := by
  cases c <;> decide

end ChengCheng2026
