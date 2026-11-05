module

public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Data.Examples.HalleMarantz1993

/-!
# Halle and Marantz (1993): Distributed Morphology and the Pieces of Inflection

This file formalizes Halle and Marantz's English verb inflection, section 3.1. The
seven suffixes of (8) compete under the Subset Principle for the fused Tns–Agr node,
`vocabulary`, and the principal parts of (7) fall out, `principal_parts`. The node's
features are the binary `[±past]` and `[±participle]` and the `[3sg]` agreement complex; the
stem stands on the terminal to its left, where the stem lists of the conditioned suffixes read
it as context, so an item's substantive features outrank its stem condition,
`substantive_precedes_contextual`. Agr is added at MS to `[−participle]` Tns nodes and fuses
with Tns before insertion, `tnsAgrFusion`, so a participial node takes no Agr,
`agr_only_on_finite`. The regular verb's identical finite past and past
participle is underspecification rather than a participle rule: `-d` carries only `[+past]`, and
the only participle-specific past item is the stem-listed `-n`,
`participle_eq_past_of_not_strong`; the stem-conditioned past `∅` and the Elsewhere `∅` are
distinct items, `zero_morphemes_distinct`.

## Implementation notes

The `∅` and `-t` pasts tie on complexity and need no order, since their stem lists are disjoint,
`strongPast_disjoint_tPast`. The past block, `[+participle]` `-ing` and `[3sg]` `-z` also tie, and
there the order matters: the paper suggests "a universal hierarchy of tense > aspect > agreement",
failing which the order "must be stipulated". `rank` breaks that tie by the hierarchy, so insertion
does not read the listing of `vocabulary`, and the hierarchy orders the items as (8) lists them,
`vocabulary_ranked`. Stem readjustment (*dwel-t*, *brough-t*) is the paper's separate rule system
(10) and is outside this file.

## References

* [halle-marantz-1993]
-/

@[expose] public section

namespace HalleMarantz1993

open DistributedMorphology Morphology

/-! ### The fused Tns–Agr node -/

/-- The four stems of (7), one per past-suffix class. -/
inductive Verb where
  | beat | put | dwell | play
  deriving DecidableEq, Repr

/-- Features at the fused Tns–Agr node, the paper's binary `[±past]` and `[±participle]` and
its `[3sg]` person–number complex, and the stem, borne by the terminal to the node's left. -/
inductive Feature where
  | past (b : Bool)
  | participle (b : Bool)
  | sg3
  | stem (v : Verb)
  deriving DecidableEq, Repr

/-- A Tns node. -/
def tns (past participle : Bool) : Finset Feature :=
  {.past past, .participle participle}

/-- The Agr node added at MS: the `[3sg]` complex or the unmarked one. -/
def agr (sg3 : Bool) : Finset Feature :=
  if sg3 then {.sg3} else ∅

/-- Agr fuses with a `[−participle]` Tns node into one terminal bearing both
bundles. -/
def tnsAgrFusion : FusionRule Feature where
  condition p _ := .participle false ∈ p

/-- The fused node of a finite form. -/
def tnsAgr (past sg3 : Bool) : Finset Feature := tns past false ∪ agr sg3

/-- The fused node `b` next to the stem `v`. -/
def nextTo (b : Finset Feature) (v : Verb) : Neighborhood (Finset Feature) := ⟨b, [{.stem v}], []⟩

theorem agr_only_on_finite (past sg3 : Bool) :
    tnsAgrFusion.apply (tns past true) (agr sg3) = none := by
  simp [FusionRule.apply, tnsAgrFusion, tns]

/-! ### The Vocabulary (8) -/

/-- Stems taking `-n` in the past participle (*beat-en*). -/
def strongParticiple : List Verb := [.beat]

/-- Stems taking the `∅` past (*beat*, *put*). -/
def strongPast : List Verb := [.beat, .put]

/-- Stems taking the `-t` past (*dwel-t*). -/
def tPast : List Verb := [.dwell]

/-- The items of a stem-conditioned suffix: one per listed stem, the paper's disjunctive list in
a contextual feature, which reads the stem to the node's left. -/
def forStems (features : Finset Feature) (e : String) (stems : List Verb) :
    List (VocabularyItem Feature String) :=
  stems.map fun v ↦ ⟨insert (-1, .stem v) (features ⟷ e).site, e⟩

/-- The seven suffixes of (8): the past block (`-n`, the unordered `∅` and
`-t`, default `-d`), then `[+participle]` `-ing`, `[3sg]` `-z`, and
the Elsewhere `∅`. -/
def vocabulary : RuleSet (VocabularyItem Feature String) :=
  forStems {.past true, .participle true} "-n" strongParticiple ++
    forStems {.past true} "∅" strongPast ++ forStems {.past true} "-t" tPast ++
    [{.past true} ⟷ "-d", {.participle true} ⟷ "-ing", {.sg3} ⟷ "-z", ∅ ⟷ "∅"]

theorem strongPast_disjoint_tPast : List.Disjoint strongPast tPast :=
  List.disjoint_left.mpr (by decide)

/-- The levels of the paper's hierarchy of tense over aspect over agreement. -/
def Feature.level : Feature → ℕ
  | .past _ => 2
  | .participle _ => 1
  | .sg3 | .stem _ => 0

/-- An item ranks by its complexity and, where complexity ties, by the highest level among the
features it spells out. -/
def rank (i : VocabularyItem Feature String) : (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  toLex (i.specificity, i.features.sup Feature.level)

/-- The suffix inserted at a node. -/
def suffix (n : Neighborhood (Finset Feature)) : Option String := vocabulary.realize rank n

/-- The hierarchy orders the items as (8) lists them, "in the order of decreasing complexity". -/
theorem vocabulary_ranked : vocabulary.Pairwise fun i j ↦ rank j ≤ rank i := by
  decide

/-! ### The principal parts (7) -/

/-- A row of (7). -/
inductive Part where
  | pastParticiple | pastFinite | nonpast3sg | nonpastParticiple | nonpastFinite
  deriving DecidableEq, Repr

/-- The fused node a row is spelled out at; participles take no Agr. -/
def Part.bundle : Part → Finset Feature
  | .pastParticiple => tns true true
  | .pastFinite => tnsAgr true false
  | .nonpast3sg => tnsAgr false true
  | .nonpastParticiple => tns false true
  | .nonpastFinite => tnsAgr false false

/-- The fused node of a row next to the stem `v`. -/
def Part.node (p : Part) (v : Verb) : Neighborhood (Finset Feature) := nextTo p.bundle v

/-- A cell of (7): stem, row, and the suffix the paper segments. -/
structure Cell where
  verb : Verb
  part : Part
  suffix : String
  deriving DecidableEq

def Verb.ofString : String → Option Verb
  | "beat" => some .beat | "put" => some .put | "dwell" => some .dwell | "play" => some .play
  | _ => none

def Part.ofString : String → Option Part
  | "past_participle" => some .pastParticiple | "past_finite" => some .pastFinite
  | "nonpast_3sg" => some .nonpast3sg | "nonpast_participle" => some .nonpastParticiple
  | "nonpast_finite" => some .nonpastFinite | _ => none

/-- The cell an example of (7) records, from its `paperFeatures`. -/
def Cell.ofDatum (ex : Datum) : Option Cell := do
  let verb ← ex.paperFeatures.lookup "verb" >>= Verb.ofString
  let part ← ex.paperFeatures.lookup "part" >>= Part.ofString
  let suffix ← ex.paperFeatures.lookup "suffix"
  pure ⟨verb, part, suffix⟩

theorem cell_ofDatum_isSome : ∀ ex ∈ Examples.all, (Cell.ofDatum ex).isSome := by decide

/-- The cells of (7). -/
def cells : List Cell := Examples.all.filterMap Cell.ofDatum

/-- **The principal parts**: insertion from (8) spells out every cell of (7) with the suffix the
paper segments. -/
theorem principal_parts : ∀ c ∈ cells, suffix (c.part.node c.verb) = some c.suffix := by
  decide

/-! ### What the competition explains -/

theorem participle_eq_past_of_not_strong (v : Verb) (hv : v ∉ strongParticiple) :
    suffix (Part.pastParticiple.node v) = suffix (Part.pastFinite.node v) := by
  revert hv; cases v <;> decide

theorem zero_past_blocks_default :
    vocabulary.selectBy rank (Part.pastFinite.node .put) =
      some ⟨{(0, .past true), (-1, .stem .put)}, "∅"⟩ := by
  decide

theorem zero_morphemes_distinct :
    vocabulary.selectBy rank (Part.pastFinite.node .put) ≠
      vocabulary.selectBy rank (Part.nonpastFinite.node .put) := by
  decide

/-- At a `[+past]` node that is `[3sg]` complexity ties `-d` with `-z`, and the hierarchy inserts
`-d`. -/
theorem past_precedes_agreement :
    (({.past true} ⟷ "-d" : VocabularyItem Feature String).specificity =
        ({.sg3} ⟷ "-z" : VocabularyItem Feature String).specificity) ∧
      suffix (nextTo (tnsAgr true true) .play) = some "-d" := by
  decide

/-- Substantive features outrank contextual ones: an item for `[+past, +participle]` in any
environment wins over an item for `[+past]` restricted to the stem, wherever it is listed. -/
theorem substantive_precedes_contextual :
    subsetPrinciple (forStems {.past true} "∅" [.put] ++ [{.past true, .participle true} ⟷ "-n"])
      (Part.pastParticiple.node .put) = some "-n" := by
  decide

/-! ### Fusion in the spell-out pipeline -/

/-- Fusion of adjacent Tns and Agr, then insertion by the Subset Principle. -/
def tnsAgrSpellout : Spellout (Finset Feature) String where
  modules := [tnsAgrFusion.applyFirstAdjacent]
  insert n := (suffix n).toList

theorem plays_pf : tnsAgrSpellout.pf [tns false false, agr true] = [["-z"]] := by
  decide

theorem plays_misalignment :
    [tns false false, agr true].length = 2 ∧
      (tnsAgrSpellout.pf [tns false false, agr true]).length = 1 := by
  exact ⟨rfl, by rw [plays_pf]; rfl⟩

end HalleMarantz1993
