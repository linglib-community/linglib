module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Morphology.Word.Basic
public import Linglib.Data.Experiments.Kuhlmann2013

/-!
# Kuhlmann (2013): Mildly Non-Projective Dependency Grammar

This file formalizes the structural side of [kuhlmann-2013], which reads lexicalized linear
context-free rewriting systems as dependency grammars and measures the non-projectivity that
parsing them has to pay for. The fan-out of a rule extracted from a treebank is the
block-degree of its head, one more than the substrate's gap degree, so [projectivity is
block-degree one](##isProjective_iff_blockDegree_eq_one). Well-nestedness, which makes parsing
polynomial through binarization, fails exactly when [two sibling nodes have interleaving
yields](##not_isWellNested_iff_siblings). The Dutch and German verb clusters of Figure 1
separate the projective from the non-projective order while keeping the dependencies fixed, and
the trees of Figures 10 and 11 witness block-degrees 2 and 3 and the independence of
well-nestedness from block-degree.

Tables 3 and 4 count the rules and the trees five treebanks lose when the extracted yield
functions are restricted. On a tree the restrictions are bounds on block-degree, [fan-out 1 being
projectivity](##Restriction.holds_fanOutOne_iff) and [fan-out at most 2 gap degree at most
1](##Restriction.holds_fanOutLeTwo_iff). The text's percentages are recomputed from the counts:
fan-out 1 loses between 11.16% and 23.15% of the trees and, [on the Arabic total the text
implies](##ruleLoss_fanOutOne), between 0.74% and 1.75% of the rules; allowing fan-out 2
recovers more than 94% of the lost rules and trees, and [adding well-nestedness still recovers
more than 92% of the rules](##reduction_wellNested).

## Implementation notes

Positions are zero-based, so node `i` of a figure is position `i - 1`. The substrate's
`Graph.IsWellNested` is the paper's definition under the paper's own gloss: yields may overlap
only when one node dominates the other. Block-degree is the gap degree plus one, as the
paper's footnote on gap-degree observes. A restriction keeps a tree when it keeps every rule
extracted from it, which for the well-nested restriction reads the tree's well-nestedness as
that of its rules, a correspondence the paper states for canonical grammars. A percentage of the
text is compared with the counts by `Decimal.RoundsPercent`, at the precision the text prints
it. The lexicalized LCFRS machinery, canonical grammars, the parsing algorithm, and the
NP-hardness result are not formalized.

## Errata

* Table 3 prints 5,839 rules for Arabic, of which the 411 lost at fan-out 1 are 7.04%; the
  text's 0.74%, the least of the rule losses, is [411 of 55,839](##ruleLoss_fanOutOne).
* The text gives Turkish's well-nested rule-loss reduction as 92.65%; the counts give
  [92.64%](##reduction_wellNested).
-/

@[expose] public section

namespace Kuhlmann2013

open DependencyGrammar Relation
open Morphology (Word)
open Data.Experiments (Decimal)

variable {n : ℕ} {g : Graph n}

/-! ### Block-degree (§7.1) -/

/-- The block-degree of a graph: the maximal number of blocks a node's yield falls into, one
more than the gap degree. -/
def blockDegree (g : Graph n) : ℕ := g.gapDegree + 1

theorem isProjective_iff_blockDegree_eq_one :
    g.IsProjective ↔ blockDegree g = 1 := by
  rw [Graph.isProjective_iff_gapDegree_eq_zero, blockDegree]
  omega

/-! ### Well-nestedness (§8.1) -/

/-- Lemma 9: a tree is ill-nested iff two sibling nodes have interleaving yields. -/
theorem not_isWellNested_iff_siblings (hT : g.IsTree) :
    ¬ g.IsWellNested ↔ ∃ p u v, g.Adj p u ∧ g.Adj p v ∧ u ≠ v ∧ g.Interleave u v := by
  constructor
  · intro h
    simp only [Graph.IsWellNested, not_forall, not_or] at h
    obtain ⟨u, v, ⟨a, ha, b, hb, c, hc, d, hd, halt⟩, huv, hvu⟩ := h
    obtain ⟨p, u', v', hu', hv', hne, hu'u, hv'v⟩ :=
      exists_adj_adj_of_not_dominates (hT.root_dominates u) (hT.root_dominates v) huv hvu
    exact ⟨p, u', v', hu', hv', hne,
      a, hu'u.trans ha, b, hu'u.trans hb, c, hv'v.trans hc, d, hv'v.trans hd, halt⟩
  · rintro ⟨p, u, v, hpu, hpv, huv, hI⟩ hW
    rcases hW u v hI with h | h
    · exact hT.not_dominates_of_adj hpu (hT.dominates_head h huv hpv)
    · exact hT.not_dominates_of_adj hpv (hT.dominates_head h huv.symm hpu)

/-! ### Figure 1: nested against cross-serial

The German order nests the verb–argument dependencies and is projective; the Dutch order
crosses them and is not, at gap degree 1. -/

/-- Dutch cross-serial: *dat Jan Piet Marie zag helpen lezen*. -/
def dutchCrossSerial : Graph 7 :=
  .ofArcs
    [Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB,
     Word.mk' "lezen" .VERB]
    0
    [(0, 4, .dep), (4, 1, .nsubj), (4, 5, .xcomp),
     (5, 2, .nsubj), (5, 6, .xcomp), (6, 3, .nsubj)]

/-- German nested: *dass Jan Piet Marie lesen helfen sah*. -/
def germanNested : Graph 7 :=
  .ofArcs
    [Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB,
     Word.mk' "sah" .VERB]
    0
    [(0, 6, .dep), (6, 1, .nsubj), (6, 5, .xcomp),
     (5, 2, .nsubj), (5, 4, .xcomp), (4, 3, .nsubj)]

theorem dutchCrossSerial_isTree : dutchCrossSerial.IsTree := by decide
theorem germanNested_isTree : germanNested.IsTree := by decide

theorem figure1_projectivity : ¬ dutchCrossSerial.IsProjective ∧ germanNested.IsProjective := by
  decide

theorem figure1_blockDegree :
    blockDegree dutchCrossSerial = 2 ∧ blockDegree germanNested = 1 := by
  decide

theorem dutchCrossSerial_isWellNested :
    dutchCrossSerial.IsWellNested ∧ ¬ dutchCrossSerial.IsPlanar := by
  decide +kernel

/-! ### Figures 10 and 11: block-degree and well-nestedness -/

/-- An unlabelled position. -/
def dot : Word := Word.mk' "•" .X

/-- Figure 10, `D₁`: the yield of node 2 falls into the blocks {2, 3} and {6}. -/
def fig10D1 : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 0
    [(0, 1, .dep), (0, 4, .dep), (4, 3, .dep), (1, 2, .dep), (2, 5, .dep)]

/-- Figure 10, `D₂`: the yield of node 1 falls into the blocks {1}, {3} and {6}. -/
def fig10D2 : Graph 6 :=
  .ofArcs [dot, dot, dot, dot, dot, dot] 1
    [(1, 0, .dep), (1, 4, .dep), (4, 3, .dep), (0, 2, .dep), (2, 5, .dep)]

-- Example 6
theorem figure10_blockDegree : blockDegree fig10D1 = 2 ∧ blockDegree fig10D2 = 3 := by
  decide

/-- Figure 11, `D₁`: non-projective with no overlapping yields at all. -/
def fig11D1 : Graph 4 :=
  .ofArcs [dot, dot, dot, dot] 1 [(1, 0, .dep), (1, 2, .dep), (0, 3, .dep)]

/-- Figure 11, `D₂`: the yields of nodes 1 and 2 overlap, but node 1 dominates node 2. -/
def fig11D2 : Graph 4 :=
  .ofArcs [dot, dot, dot, dot] 0 [(0, 2, .dep), (2, 1, .dep), (1, 3, .dep)]

/-- Figure 11, `D₃`: the yields of the sibling nodes 2 and 3 overlap. -/
def fig11D3 : Graph 5 :=
  .ofArcs [dot, dot, dot, dot, dot] 0 [(0, 2, .dep), (2, 4, .dep), (0, 1, .dep), (1, 3, .dep)]

-- Figure 11, Example 8
theorem figure11_wellNested :
    (fig11D1.IsWellNested ∧ ¬ fig11D1.IsProjective) ∧
      (fig11D2.IsWellNested ∧ ¬ fig11D2.IsProjective) := by
  decide +kernel

theorem fig11D2_interleave : fig11D2.Interleave 0 1 ∧ Dominates fig11D2 0 1 := by
  decide +kernel

-- Lemma 9
theorem fig11D3_not_isWellNested : ¬ fig11D3.IsWellNested :=
  (not_isWellNested_iff_siblings (by decide)).2
    ⟨0, 1, 2, by decide, by decide, by decide, by decide +kernel⟩

theorem figure11_blockDegree : blockDegree fig11D2 = 2 ∧ blockDegree fig11D3 = 2 := by
  decide

/-! ### Tables 3 and 4: coverage on dependency treebanks (§7.4, §8.4) -/

/-- What a restriction keeps of a tree: every rule extracted from it meets the restriction, the
fan-out of the rule extracted at a node being the node's block-degree (§7.3) and its
well-nestedness that of the tree (§8.3). -/
def Restriction.Holds : Restriction → Graph n → Prop
  | .fanOutOne, g => blockDegree g = 1
  | .fanOutLeTwo, g => blockDegree g ≤ 2
  | .wellNested, g => g.IsWellNested ∧ blockDegree g ≤ 2

-- §7.1
theorem Restriction.holds_fanOutOne_iff : Restriction.fanOutOne.Holds g ↔ g.IsProjective :=
  isProjective_iff_blockDegree_eq_one.symm

/-- A bound of 2 on the fan-out of the rules extracted from a tree is a bound of 1 on its gap
degree. -/
theorem Restriction.holds_fanOutLeTwo_iff :
    Restriction.fanOutLeTwo.Holds g ↔ g.gapDegree ≤ 1 := by
  simp only [Restriction.Holds, blockDegree]
  omega

/-- The text's "between `a` (`lo`) and `b` (`hi`)": over the treebanks the share
`num t / den t` is least at `lo` and greatest at `hi`, where it rounds to the percentages `a`
and `b`. -/
def SharesBetween (num den : Treebank → ℕ) (a : Decimal) (lo : Treebank) (b : Decimal)
    (hi : Treebank) : Prop :=
  a.RoundsPercent (num lo) (den lo) ∧ b.RoundsPercent (num hi) (den hi) ∧
    ∀ t, (num lo / den lo : ℚ) ≤ num t / den t ∧ (num t / den t : ℚ) ≤ num hi / den hi

instance {num den : Treebank → ℕ} {a b : Decimal} {lo hi : Treebank} :
    Decidable (SharesBetween num den a lo b hi) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _, _))

-- §7.4
theorem treeLoss_fanOutOne :
    SharesBetween (loss · .fanOutOne |>.trees) (size · |>.trees)
      ⟨1116, 2⟩ .arabic ⟨2315, 2⟩ .czech := by
  decide +kernel

/-- The text's rule losses at fan-out 1, between 0.74% on Arabic and 1.75% on Slovene, hold of
the 55,839 Arabic rules its 0.74% implies, not of the 5,839 that Table 3 prints. -/
theorem ruleLoss_fanOutOne :
    SharesBetween (loss · .fanOutOne |>.rules) (Function.update (size · |>.rules) .arabic 55839)
      ⟨74, 2⟩ .arabic ⟨175, 2⟩ .slovene ∧
    ¬ (⟨74, 2⟩ : Decimal).RoundsPercent (loss .arabic .fanOutOne).rules (size .arabic).rules := by
  decide +kernel

-- §7.4
theorem reduction_fanOutLeTwo :
    SharesBetween (fun t ↦ (loss t .fanOutOne).rules - (loss t .fanOutLeTwo).rules)
      (loss · .fanOutOne |>.rules) ⟨9416, 2⟩ .turkish ⟨9976, 2⟩ .arabic ∧
    SharesBetween (fun t ↦ (loss t .fanOutOne).trees - (loss t .fanOutLeTwo).trees)
      (loss · .fanOutOne |>.trees) ⟨9431, 2⟩ .turkish ⟨9939, 2⟩ .arabic := by
  decide +kernel

-- §7.4
theorem czech_fanOutLeTwo :
    (⟨2, 2⟩ : Decimal).RoundsPercent (loss .czech .fanOutLeTwo).rules (size .czech).rules ∧
      ((loss .czech .fanOutLeTwo).trees : ℚ) / (size .czech).trees ≤ 5 / 1000 := by
  decide +kernel

/-- Well-nestedness loses more rules than fan-out at most 2 alone on every treebank, and still
recovers between 92.64% (Turkish), which the text prints as 92.65%, and 99.51% (Arabic) of the
rules lost at fan-out 1. -/
theorem reduction_wellNested :
    (∀ t, (loss t .fanOutLeTwo).rules < (loss t .wellNested).rules) ∧
      SharesBetween (fun t ↦ (loss t .fanOutOne).rules - (loss t .wellNested).rules)
        (loss · .fanOutOne |>.rules) ⟨9264, 2⟩ .turkish ⟨9951, 2⟩ .arabic ∧
      ¬ (⟨9265, 2⟩ : Decimal).RoundsPercent
        ((loss .turkish .fanOutOne).rules - (loss .turkish .wellNested).rules)
        (loss .turkish .fanOutOne).rules := by
  decide +kernel

end Kuhlmann2013
