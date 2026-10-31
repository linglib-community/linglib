module

public import Linglib.Data.Examples.AlexiadouLohndal2017
public import Studies.BobaljikHarley2017
public import Studies.Embick2004
public import Studies.DeBelderVanCraenenbroeck2015
public import Studies.VanCraenenbroeck2014
public import Linglib.Data.Examples.Readers

/-!
# Alexiadou and Lohndal (2017): The structural configurations of root categorization

Distributed Morphology agrees that a Root is categorized by a functional head, but not on the
configuration. The Root may be merged as the complement of the categorizer, as its modifier, as
either according to its class, or inserted after syntax into a position of its own. The chapter
weighs the evidence for each view and finds none conclusive. Hiaki suppletion, offered for Roots
that take their internal argument as a complement, survives on a derivation in which the Root never
takes one: the Root moves into a low head, and the argument merges with the complex head they form,
local enough under the refined locality condition. One-replacement and the selection of objects
across categories fail to decide too: a noun with arguments is derived from a verb, its nP
embedding the verbal structure, so whatever the configuration of the Root and its argument, *one*
strands adjuncts and not arguments and the noun's argument is selected as the verb's. Without a
secondary resultative predicate, Direct Merge of a Root and its merger as a complement are
practically indistinguishable. What does favor letting Roots merge in either way is a contrast in
resultatives: *colored dark* is possible and *blackened dark* is not, since only a Root that can
modify v leaves v's complement free for an aP. Inserting Roots after syntax into the empty position
that Primary Merge leaves derives that the material over a Root labels it, but not that a Root is
categorized at all.

## Implementation notes

* The locality condition (25) is the one the chapter quotes from the manuscript of Bobaljik and
  Harley's chapter, `DistributedMorphology.MayCondition'`, and the trees are over the categories
  of `BobaljikHarley2017`. In (27c) the lower F is the complex head of F and the Root.
* That Direct Merge and complement Merge build one complex head is
  `Embick2004.headDaughter?_moveRoot`.
* A view's licensing of a resultative aP is read off how it attaches a Root of each class: a v
  with a Root as its complement has no room for an aP, as Embick's analysis of v[FIENT] requires
  (`interpretable_aP_iff`).
* *one* stands for the nP over the verbal structure, with the adjunct adjoined to it; the chapter
  places both at ClP, which is above the verbal structure too.

## TODO

The discussion of verb–object idioms, the generalization that only nouns derived from verbs have
argument structure, and the endocentricity argument for Roots as modifiers are not formalized.

## References

* [alexiadou-lohndal-2017]
* [bobaljik-harley-2017]
* [embick-2004]
-/

@[expose] public section

namespace AlexiadouLohndal2017

open PhraseStructure BobaljikHarley2017
open DistributedMorphology (MayCondition MayCondition')
open DistributedMorphology.RootCategorization (Attachment)

/-! ### Hiaki suppletion without Root complements -/

/-- The structure (26), the internal argument in the specifier of F over vP, the Root in situ. -/
def tree26 : T :=
  .node .voice [.terminal .d .phrase, .node .voice [.terminal .voice .voice,
    .node .f [.terminal .d .phrase,
      .node .f [.terminal .f .f, .node .v [.terminal .v .v, .terminal .root .root]]]]]

/-- The last step of the derivation (27). Once vP is spelled out, the Root forms a complex head with
F, and the internal argument merges with that head. -/
def tree27 : T :=
  .node .f [.terminal .d .phrase, .adjoin .f [.terminal .f .f, .terminal .root .root]]

/-- Under (25), the internal argument may condition the Root in (27) but not in (26). -/
theorem mayCondition'_tree27 :
    MayCondition' tree27 ⟨[1, 1]⟩ ⟨[0]⟩ ∧ ¬ MayCondition tree26 ⟨[1, 1, 1, 1, 1]⟩ ⟨[1, 1, 0]⟩ := by
  decide

/-! ### The four views and the resultative contrast -/

/-- The four views of how a Root is categorized (6) merge it as the complement of v, as its
modifier, or as either according to its class, or insert it after syntax. -/
inductive View
  | complement | modifier | mixed | postSyntactic
  deriving DecidableEq, Repr

/-- The classes of Roots, manner Roots like √COLOR and state or result Roots like √BLACK. -/
inductive RootClass
  | manner | result
  deriving DecidableEq, Repr

/-- How each view attaches a Root of each class to v; a Root inserted after syntax is attached in
neither way. -/
def View.attach : View → RootClass → Option Attachment
  | .complement, _ => some .complement
  | .modifier, _ => some .modifier
  | .mixed, .manner => some .modifier
  | .mixed, .result => some .complement
  | .postSyntactic, _ => none

/-- A view licenses a Root of a class with a resultative aP when it attaches the Root as v's
modifier, since a Root that is v's complement leaves no room for an aP. -/
def View.LicensesResultative (v : View) (c : RootClass) : Prop := v.attach c = some .modifier

instance (v : View) (c : RootClass) : Decidable (v.LicensesResultative c) :=
  inferInstanceAs (Decidable (_ = _))

theorem interpretable_aP_iff (x : Embick2004.DP) (m : Option Embick2004.Root)
    (a : Embick2004.Root) (μ : Embick2004.MeansRule) :
    (⟨some x, m, .aP a, some μ⟩ : Embick2004.FientP).Interpretable ↔ m.isSome := by
  cases m <;> simp [Embick2004.FientP.Interpretable]

/-- The classes as named in the rows. -/
def classTable : List (String × RootClass) := [("manner", .manner), ("result", .result)]

/-- The resultative examples, the class of their Root with their judgment. -/
def data : List (RootClass × Judgment) :=
  Examples.all.filterMap fun d ↦ (d.parse? "rootClass" classTable).map (·, d.judgment)

theorem data_length : data.length = 2 := by decide +kernel

/-- Only the mixed view derives the contrast (56). -/
theorem derives_iff (v : View) :
    (∀ p ∈ data, p.2 = .acceptable ↔ v.LicensesResultative p.1) ↔ v = .mixed := by
  cases v <;> decide +kernel

/-! ### One-replacement and selection in deverbal nouns -/

section Deverbal

open VanCraenenbroeck2014 (Config)
open DistributedMorphology (Strands)
open DistributedMorphology.RootCategorization (selector)

/-- A deverbal noun with an adjunct, the nP of a nominalizer over the phrase of a Root and its
argument under v, with a PP adjoined to it. -/
def deverbal (c : Config) : Tree DistributedMorphology.RootCategorization.Cat Unit :=
  .adjoin (.cat .n) [.node (.cat .n) [.terminal (.cat .n) (), c.tree .v], .terminal .p ()]

/-- The position of a dependent in `deverbal`. -/
def position (c : Config) : Harley2014.Dependent → Core.Order.TreePath
  | .argument => ⟨0 :: 1 :: c.argPos.toList⟩
  | .adjunct => ⟨[1]⟩

/-- *one*, a proform of the category of the noun, strands the dependent from the Root. -/
def OneStrands (c : Config) (d : Harley2014.Dependent) : Prop :=
  Strands (.cat .n) (deverbal c) ⟨0 :: 1 :: c.rootPos.toList⟩ (position c d)

instance (c : Config) (d : Harley2014.Dependent) : Decidable (OneStrands c d) :=
  inferInstanceAs (Decidable (Strands _ _ _ _))

/-- The examples of (8), the dependent each strands with its judgment. -/
def oneData : List (Harley2014.Dependent × Judgment) :=
  Examples.all.filterMap fun d ↦
    (d.parse? "stranded" Harley2014.dependentTable).map (·, d.judgment)

theorem oneData_length : oneData.length = 2 := by decide +kernel

/-- In a deverbal noun, *one* strands exactly the dependents (8) accepts, and the argument merges
with the verb's head, whatever the configuration. -/
theorem deverbal_derives (c : Config) :
    (∀ p ∈ oneData, p.2 = .acceptable ↔ OneStrands c p.1) ∧
      selector (deverbal c) (position c .argument) = selector (c.tree .v) c.argPos := by
  cases c <;> decide +kernel

end Deverbal

/-! ### Roots inserted after syntax -/

/-- **A Root need not be categorized.** Primary Merge pairs the null derivation with whichever item
it selects first, and that item labels the result, so the derivation of *the books* builds a Root
from its definite and plural features alone, labelled by the definite feature. -/
theorem root_without_categorizer :
    ∃ o : DeBelderVanCraenenbroeck2015.Obj DeBelderVanCraenenbroeck2015.Feature,
      Relation.ReflTransGen DeBelderVanCraenenbroeck2015.Step (.init [{.definite}, {.plural}])
        ⟨[], o⟩ ∧ o.roots = 1 ∧ o.label = some {.definite} :=
  ⟨_, DeBelderVanCraenenbroeck2015.derivation_theBooks, rfl, rfl⟩

end AlexiadouLohndal2017
