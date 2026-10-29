module

public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Adpositions
public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Reordering
public import Mathlib.Data.Fin.VecNotation

/-!
# Futrell, Levy and Gibson (2020): Dependency Locality as an Explanatory Principle for Word Order

This file formalizes the worked examples of Futrell, Levy and Gibson's case for dependency
length minimization as a source of word-order universals: the dependency trees of its sections
2.3 and 2.4, with every total dependency length checked against the printed figure.
Displacement makes trees nonprojective in extraposition and *wh*-movement ((3) and (4)), both
trees of gap degree one. Short-before-long order minimizes dependency length after a
head-initial head, and its mirror image, long-before-short, before a head-final one ((7) and
(8)); a chain of single dependents is shortest with consistent head direction (9), while a head
with several short dependents does better splitting them across itself (10), the exceptions to
harmony that Gildea and Temperley derived. Heavy NP shift is the flagship case (11): keeping
the object before the particle costs one unit for a light object and five for a heavy one. The
random-order baseline of the corpus studies is illustrated by (13), the attested order against a
reordering of the same tree. The corpus results of sections 4 and 5, the Monte Carlo comparisons
with random baselines, are not formalized; the per-language head-final proportions and mean
dependency lengths of Table 2 are the rows of `Data.UD.DependencyLength.FutrellEtAl2020`.

## Implementation notes

* English words come from the Fragment lexicon, and the trees follow the paper's drawing
  convention, on which a preposition heads its noun, so arc lengths match the printed diagrams.
* Mirror-image and reordering claims go through `Graph.mirror` and `Graph.map`, so they
  hold by the general invariance theorems rather than by inspection of hand-typed twins.
* Dependency length is the distance `Nat.dist` between head and dependent, the measure behind
  the totals of the printed figures, on which adjacent words are one apart; the prose of
  section 2.4 of the preprint describes it as the number of intervening words.
* Gap degree is this file's measure of how far the trees of (3) and (4) depart from
  projectivity. The paper's claim that natural languages deviate from context-freeness only
  mildly is the mild context-sensitivity of languages, a property of grammar formalisms that the
  gap degree of single trees does not settle.

## References

* [futrell-levy-gibson-2020]
* [gildea-temperley-2010]
* [behaghel-1909]
-/

@[expose] public section

namespace FutrellEtAl2020

open DependencyGrammar
open Morphology (Word)
open English.Nouns English English.Pronouns English.Determiners English.Verbs
  English.Adpositions

-- `this` is a Lean keyword, so the demonstrative needs a qualified alias.
abbrev this_ := English.Determiners.this.toWord
abbrev ap : Word := Word.mk' "AP" .PROPN

/-- Schematic token for the paper's abstract tree diagrams (A, B, C, …). -/
def tok (s : String) : Word := Word.mk' s .X

/-! ### Examples (3)–(4): displacement and nonprojectivity

Displacement produces nonprojective trees: right extraposition in (3),
where *who you know* modifies *woman* across the intervening verb, and
wh-movement in (4), where *what* is the object of *did*. Both have gap
degree 1. -/

/-- Example (3): "I think a woman arrived who you know". -/
def extraposition : Graph UD.DepRel 8 :=
  .ofArcs
    [i.toWord, think.toWord .base, a.toWord, woman.toWordSg, arrive.toWord .past,
     who.toWord, you.toWord, know.toWord .base]
    1
    [(1, 0, .nsubj), (1, 4, .ccomp), (4, 3, .nsubj), (3, 2, .det),
     (3, 7, .acl), (7, 5, .obj), (7, 6, .nsubj)]

/-- Example (4): "I know what he thinks you did yesterday". -/
def whMovement : Graph UD.DepRel 8 :=
  .ofArcs
    [i.toWord, know.toWord .base, what.toWord, he.toWord, think.toWord .thirdSg,
     you.toWord, do_.toWord .past, Word.mk' "yesterday" .ADV]
    1
    [(1, 0, .nsubj), (1, 4, .ccomp), (4, 3, .nsubj), (4, 6, .ccomp),
     (6, 5, .nsubj), (6, 2, .obj), (6, 7, .advmod)]

example : ¬ extraposition.IsProjective := by decide
example : ¬ whMovement.IsProjective := by decide

theorem displacement_gap_degree_one :
    extraposition.gapDegree = 1 ∧ whMovement.gapDegree = 1 := by decide

/-! ### Examples (7)–(8): short-before-long and its head-final mirror

A head with three dependent phrases of sizes 1, 2, 3. In head-initial
contexts (7), placing them short-to-long after the head minimizes total
dependency length; the head-final long-before-short preference (8) is its
exact mirror — here literally `Graph.mirror`, so the equal-cost claim is
`Graph.totalLength_mirror`, not an inspection of hand-typed twins. -/

/-- (7a) A [B] [C D] [E F G]: dependents short-to-long after the head. -/
def shortBeforeLong : Graph Unit 7 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    0 [(0, 1, ()), (0, 2, ()), (2, 3, ()), (0, 4, ()), (4, 5, ()), (4, 6, ())]

/-- (7b), the same head with its phrases reordered long to short: A [E F G] [C D] [B]. -/
def longBeforeShort : Graph Unit 7 :=
  shortBeforeLong.reorderDependents 0 (.swap ⟨1, by decide⟩ ⟨4, by decide⟩)

-- (7a), (7b), (7)
theorem short_before_long_head_initial :
    shortBeforeLong.totalLength < longBeforeShort.totalLength :=
  (Graph.totalLength_lt_reorderDependents_iff (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2 (by decide +kernel)

-- (8)
theorem long_before_short_head_final :
    shortBeforeLong.mirror.totalLength < longBeforeShort.mirror.totalLength := by
  simpa [Graph.totalLength_mirror] using short_before_long_head_initial

/-! ### Examples (9)–(10): head-direction consistency and its exceptions -/

/-- (9a) chain A → B → C → D linearized consistently: A B C D. -/
def consistentChain : Graph Unit 4 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D"]
    0 [(0, 1, ()), (1, 2, ()), (2, 3, ())]

/-- (9b) the same chain linearized with mixed head direction: A C D B. -/
def mixedChain : Graph Unit 4 :=
  .ofArcs [tok "A", tok "C", tok "D", tok "B"]
    0 [(0, 3, ()), (3, 1, ()), (1, 2, ())]

-- (9)
theorem consistent_chain_shorter :
    consistentChain.totalLength < mixedChain.totalLength := by decide

/-- (10a) A B C D: both dependents (B and C–D) after the head A. -/
def dependentsSameSide : Graph Unit 4 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D"]
    0 [(0, 1, ()), (0, 2, ()), (2, 3, ())]

/-- (10b) B A C D: the one-word dependent moved before the head. -/
def dependentsSplit : Graph Unit 4 :=
  .ofArcs [tok "B", tok "A", tok "C", tok "D"]
    1 [(1, 0, ()), (1, 2, ()), (2, 3, ())]

-- (10) [gildea-temperley-2010]
theorem split_beats_consistency :
    dependentsSplit.totalLength < dependentsSameSide.totalLength := by decide

/-! ### Example (11): heavy NP shift

The paper's flagship worked example: the cost of the verb–object–particle
order is 1 for a light object (6 vs. 7) and 5 for a heavy one (11 vs. 16),
deriving the weight-sensitivity of heavy NP shift (cf. example (6)). -/

/-- (11a) "John threw out the trash", total dependency length 6. -/
def lightParticleEarly : Graph UD.DepRel 5 :=
  .ofArcs [john.toWord, throw.toWord .past, out.toWord, the.toWord, trash.toWordSg]
    1 [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det)]

/-- (11b) "John threw the trash out", total dependency length 7. -/
def lightParticleLate : Graph UD.DepRel 5 :=
  .ofArcs [john.toWord, throw.toWord .past, the.toWord, trash.toWordSg, out.toWord]
    1 [(1, 0, .nsubj), (1, 3, .obj), (3, 2, .det), (1, 4, .compound)]

/-- (11c) "John threw out the trash sitting in the kitchen", total 11. -/
def heavyParticleEarly : Graph UD.DepRel 9 :=
  .ofArcs
    [john.toWord, throw.toWord .past, out.toWord, the.toWord, trash.toWordSg,
     sit.toWord .presentParticiple, in_.toWord, the.toWord, kitchen.toWordSg]
    1
    [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det),
     (4, 5, .acl), (5, 6, .obl), (6, 8, .obl), (8, 7, .det)]

/-- (11d) "John threw the trash sitting in the kitchen out", total 16. -/
def heavyParticleLate : Graph UD.DepRel 9 :=
  .ofArcs
    [john.toWord, throw.toWord .past, the.toWord, trash.toWordSg,
     sit.toWord .presentParticiple, in_.toWord, the.toWord, kitchen.toWordSg, out.toWord]
    1
    [(1, 0, .nsubj), (1, 3, .obj), (3, 2, .det), (3, 4, .acl),
     (4, 5, .obl), (5, 7, .obl), (7, 6, .det), (1, 8, .compound)]

-- The printed totals of the four figures.
example : lightParticleEarly.totalLength = 6 := by decide
example : lightParticleLate.totalLength = 7 := by decide
example : heavyParticleEarly.totalLength = 11 := by decide
example : heavyParticleLate.totalLength = 16 := by decide

theorem dlm_penalty_grows_with_weight :
    lightParticleLate.totalLength - lightParticleEarly.totalLength <
    heavyParticleLate.totalLength - heavyParticleEarly.totalLength := by decide

/-! ### Example (13): the random-order baseline

The attested sentence against reorderings of the same structure — stated
through `Graph.map`, so "same structure" is by construction, which is
what the paper's random-baseline methodology asserts. -/

/-- (13a) "this story comes from the AP", the attested order, total 6. -/
def attestedOrder : Graph UD.DepRel 6 :=
  .ofArcs [this_, story.toWordSg, come.toWord .thirdSg, from_.toWord, the.toWord, ap]
    2 [(1, 0, .det), (2, 1, .nsubj), (2, 3, .obl), (3, 5, .obl), (5, 4, .det)]

/-- The position permutation taking the attested order to the paper's
    first reordering "from AP the this story comes". -/
def σB : Equiv.Perm (Fin 6) :=
  ⟨![3, 4, 5, 0, 2, 1], ![3, 5, 4, 0, 1, 2], by decide, by decide⟩

/-- (13b) the reordering, as a relabeling of the attested structure. -/
def reorderingB : Graph UD.DepRel 6 := attestedOrder.map σB

example : attestedOrder.totalLength = 6 := by decide
example : reorderingB.totalLength = 9 := by decide

theorem attested_below_reordering :
    attestedOrder.totalLength < reorderingB.totalLength := by decide

end FutrellEtAl2020
