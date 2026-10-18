module

public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Data.Examples.HalleMarantz1993

/-!
# Halle and Marantz (1993): Distributed Morphology and the Pieces of Inflection

This file formalizes Halle and Marantz's English verb inflection, section 3.1. The
seven suffixes of (8) compete under the Subset Principle for the fused Tns–Agr node,
`vocabulary`, and the principal parts of (7) fall out, `principal_parts`. The node's
features are the binary `[±past]` and `[±participle]`, the `[3sg]` agreement complex, and the
stem the node is inserted next to, the paper's contextual feature; Agr is added at MS to
`[−participle]` Tns nodes and fuses with Tns before insertion, `tnsAgrFusion`, so a participial
node takes no Agr, `agr_only_on_finite`. The regular verb's identical finite past and past
participle is underspecification rather than a participle rule: `-d` carries only `[+past]`, and
the only participle-specific past item is the stem-listed `-n`,
`participle_eq_past_of_not_strong`; the stem-conditioned past `∅` and the Elsewhere `∅` are
distinct items, `zero_morphemes_distinct`.

## Implementation notes

The paper says the ordering between the `∅` and `-t` pasts "is not determined by complexity"
and needs none, since their stem lists are disjoint, and that the ordering among the past block,
`[3sg]` `-z`, and `[+participle]` `-ing` "must be stipulated"; the Subset Principle's count ties
at those points, and the list order of `vocabulary` carries the stipulation,
`past_precedes_agreement`. Stem readjustment (*dwel-t*, *brough-t*) is the paper's separate rule
system (10) and is outside this file.

## References

* [halle-marantz-1993]
-/

@[expose] public section

namespace HalleMarantz1993

open DistributedMorphology

/-! ### The fused Tns–Agr node -/

/-- The four stems of (7), one per past-suffix class. -/
inductive Verb where
  | beat | put | dwell | play
  deriving DecidableEq, Repr

/-- Features at the fused Tns–Agr node: the paper's binary `[±past]` and
`[±participle]`, its `[3sg]` person–number complex, and the adjacent stem. -/
inductive Feature where
  | past (b : Bool)
  | participle (b : Bool)
  | sg3
  | stem (v : Verb)
  deriving DecidableEq, Repr

/-- A Tns node next to stem `v`. -/
def tns (v : Verb) (past participle : Bool) : Finset Feature :=
  {.past past, .participle participle, .stem v}

/-- The Agr node added at MS: the `[3sg]` complex or the unmarked one. -/
def agr (sg3 : Bool) : Finset Feature :=
  if sg3 then {.sg3} else ∅

/-- Agr fuses with a `[−participle]` Tns node into one terminal bearing both
bundles. -/
def tnsAgrFusion : FusionRule Feature where
  condition p _ := .participle false ∈ p

/-- The fused node of a finite form. -/
def tnsAgr (v : Verb) (past sg3 : Bool) : Finset Feature := tns v past false ∪ agr sg3

/-- Agr is added only to `[−participle]` nodes: Fusion rejects a participial
Tns. -/
theorem agr_only_on_finite (v : Verb) (past sg3 : Bool) :
    tnsAgrFusion.apply (tns v past true) (agr sg3) = none := by
  simp [FusionRule.apply, tnsAgrFusion, tns]

/-! ### The Vocabulary (8) -/

/-- Stems taking `-n` in the past participle (*beat-en*). -/
def strongParticiple : List Verb := [.beat]

/-- Stems taking the `∅` past (*beat*, *put*). -/
def strongPast : List Verb := [.beat, .put]

/-- Stems taking the `-t` past (*dwel-t*). -/
def tPast : List Verb := [.dwell]

/-- The items of a stem-conditioned suffix: one per listed stem, the paper's
disjunctive list in a contextual feature. -/
def forStems (features : Finset Feature) (e : String) (stems : List Verb) :
    List (VocabularyItem Feature String) :=
  stems.map fun v ↦ insert (.stem v) features ⟷ e

/-- The seven suffixes of (8): the past block (`-n`, the unordered `∅` and
`-t`, default `-d`), then `[3sg]` `-z`, `[+participle]` `-ing`, and
the Elsewhere `∅`. -/
def vocabulary : List (VocabularyItem Feature String) :=
  forStems {.past true, .participle true} "-n" strongParticiple ++
    forStems {.past true} "∅" strongPast ++ forStems {.past true} "-t" tPast ++
    [{.past true} ⟷ "-d", {.sg3} ⟷ "-z", {.participle true} ⟷ "-ing", ∅ ⟷ "∅"]

/-- The `∅` and `-t` pasts "are not ordered by complexity" and need no
ordering: their stem lists are disjoint. -/
theorem strongPast_disjoint_tPast : List.Disjoint strongPast tPast :=
  List.disjoint_left.mpr (by decide)

/-! ### The principal parts (7) -/

/-- A row of (7). -/
inductive Part where
  | pastParticiple | pastFinite | nonpast3sg | nonpastParticiple | nonpastFinite
  deriving DecidableEq, Repr

/-- The fused node a row is spelled out at; participles take no Agr. -/
def Part.node : Part → Verb → Finset Feature
  | .pastParticiple, v => tns v true true
  | .pastFinite, v => tnsAgr v true false
  | .nonpast3sg, v => tnsAgr v false true
  | .nonpastParticiple, v => tns v false true
  | .nonpastFinite, v => tnsAgr v false false

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

/-- Every row of the data pool is a well-formed cell. -/
theorem cell_ofDatum_isSome : ∀ ex ∈ Examples.all, (Cell.ofDatum ex).isSome := by decide

/-- The cells of (7). -/
def cells : List Cell := Examples.all.filterMap Cell.ofDatum

/-- **The principal parts**: the Subset Principle over (8) spells out every
cell of (7) with the suffix the paper segments. -/
theorem principal_parts :
    ∀ c ∈ cells, subsetPrinciple vocabulary (c.part.node c.verb) = some c.suffix := by
  decide

/-! ### What the competition explains -/

/-- **Syncretism by underspecification**: outside the `-n` list, the past
participle and the finite past receive the same suffix, because every past
item but `-n` carries only `[+past]`. -/
theorem participle_eq_past_of_not_strong (v : Verb) (hv : v ∉ strongParticiple) :
    subsetPrinciple vocabulary (Part.pastParticiple.node v) =
      subsetPrinciple vocabulary (Part.pastFinite.node v) := by
  revert hv; cases v <;> decide

/-- The stem-conditioned past `∅` (*put*) blocks the default `-d`: the
winner is the stem-listed item. -/
theorem zero_past_blocks_default :
    winner? vocabulary (Part.pastFinite.node .put) = some ({.past true, .stem .put} ⟷ "∅") := by
  decide

/-- The paper's two zero morphemes are different items: the stem-conditioned
past `∅` and the Elsewhere `∅` of the nonpast finite node. -/
theorem zero_morphemes_distinct :
    winner? vocabulary (Part.pastFinite.node .put) ≠
      winner? vocabulary (Part.nonpastFinite.node .put) := by
  decide

/-- The stipulated block order: at a `[+past]` node that is also `[3sg]`,
`-d` and `-z` tie on specificity and the past block's precedence in
`vocabulary` decides — *play-ed*, not *play-s*. -/
theorem past_precedes_agreement :
    subsetPrinciple vocabulary (tnsAgr .play true true) = some "-d" := by
  decide

/-! ### Fusion in the spell-out pipeline -/

/-- Fusion of adjacent Tns and Agr, then insertion by the Subset Principle. -/
def tnsAgrSpellout : Spellout (Finset Feature) String where
  modules := [tnsAgrFusion.applyFirstAdjacent]
  insert n := (subsetPrinciple vocabulary n).toList

/-- *play-s*: the domain `[Tns, Agr]` spells out as the single exponent
`-z`. -/
theorem plays_pf : tnsAgrSpellout.pf [tns .play false false, agr true] = [["-z"]] := by
  decide

/-- Two terminals enter, one exponent slot leaves: the misalignment is
carried by the fusion module. -/
theorem plays_misalignment :
    [tns .play false false, agr true].length = 2 ∧
      (tnsAgrSpellout.pf [tns .play false false, agr true]).length = 1 := by
  exact ⟨rfl, by rw [plays_pf]; rfl⟩

end HalleMarantz1993
