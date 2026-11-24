module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.Dependency.Projectivity
public import Linglib.Syntax.Dependency.Length
public import Mathlib.Data.Fin.VecNotation
public import Linglib.Morphology.Word.Basic

/-!
# de Marneffe and Nivre (2019): Dependency grammar

This file formalizes the formal claims of the review of dependency grammar in
[de-marneffe-nivre-2019] on the library's dependency graphs, whose projectivity is that of
[kuhlmann-nivre-2006]. A dependency tree is a spanning tree over the words of a sentence, §2.4,
and its projectivity has two formulations the review takes as equivalent, that every word
between the endpoints of an arc is dominated by the arc's head and that the yield of every
subtree is a contiguous substring; Figure 3 is nonprojective on both counts. Dependency trees
are insensitive to word order, §3.1, so the two orders of (1) are one graph relabelled along a
rotation of the positions. Dependency length, §3.2, explains the preference for (2a) over (2b)
and its absence between (3a) and (3b), the minimization of [behaghel-1932] and
[temperley-2007], and the object relative (4a) of [gibson-1998] holds its filler at a longer
distance than the subject relative (4b). The treebanks before Universal Dependencies annotated
parallel sentences in schemes with different relations and different heads, so that the Swedish,
Danish and English analyses of Figure 6 share at most two of their five arcs pairwise and none
across all three, §4. Universal Dependencies puts content words above
function words, Figure 4b against the function-word-headed Figure 4a, the function words
attaching to the content word with which they form a nucleus in the sense of [tesniere-1959],
so that the content-word skeleton of a sentence is shared across languages, Figure 7; its basic
representation is a tree and its enhanced representation a general graph, in which the subject
of Figure 9 has three heads and lies on a cycle, §4.4.

## Implementation notes

The review's figures carry traditional grammatical-function labels, its footnote 2; the fixtures
use their Universal Dependencies counterparts, and the function-word-headed arcs of Figure 4a,
for which UD has no relation, carry `dep`. Punctuation is dropped from (1) so that its two orders
are exactly a rotation. The coreference relation of Figure 9's enhanced graph is not in the
library's relation inventory and is omitted; the multiple heads and the cycle do not depend on
it. The analyses of Figure 6 carry the relations of their own treebanks, those the figure
uses. The word strings and bubble trees of Figure 2 and the nuclei of Figure 5 are not
representable on a graph over words and are not formalized.

## References

* [de-marneffe-nivre-2019]
* [kuhlmann-nivre-2006]
* [behaghel-1932]
* [temperley-2007]
* [gibson-1998]
* [tesniere-1959]
-/

@[expose] public section

namespace DeMarneffeNivre2019

open Dependency Morphology

/-! ### Dependency trees and projectivity, §2.4 -/

/-- Figure 1: *small dogs chase cats happily*. -/
def fig1 : Graph UD.DepRel (Fin 5) :=
  .ofArcs [(1, 0, .amod), (2, 1, .nsubj), (2, 3, .obj), (2, 4, .advmod)]

/-- Figure 3: *bigger dogs than mine*. -/
def fig3 : Graph UD.DepRel (Fin 4) :=
  .ofArcs [(1, 0, .amod), (0, 3, .advmod), (3, 2, .mark)]

-- Figure 3
theorem fig3_not_isArcProjective : ¬ fig3.IsArcProjective :=
  fun h ↦ (by decide : ¬ fig3.Reachable 0 1)
    (h (by decide : fig3.Adj 0 3) 1 (Set.mem_uIcc.2 (Or.inl ⟨by decide, by decide⟩)))

theorem fig3_reachSet : (fig3.reachSet 0).toFinset = {0, 2, 3} ∧ ¬ fig3.IsProjective :=
  ⟨by decide, fig3.isProjective_iff_isArcProjective.not.2 fig3_not_isArcProjective⟩

/-! ### Insensitivity to word order, §3.1 -/

/-- (1a) *While it was snowing, I went for a run*. -/
def ex1a : Graph UD.DepRel (Fin 9) :=
  .ofArcs [(5, 3, .advcl), (3, 0, .mark), (3, 1, .nsubj), (3, 2, .aux), (5, 4, .nsubj),
      (5, 8, .obl), (8, 6, .case), (8, 7, .det)]

/-- (1b) *I went for a run, while it was snowing*. -/
def ex1b : Graph UD.DepRel (Fin 9) :=
  .ofArcs [(1, 8, .advcl), (8, 5, .mark), (8, 6, .nsubj), (8, 7, .aux), (1, 0, .nsubj),
      (1, 4, .obl), (4, 2, .case), (4, 3, .det)]

-- §3.1, (1), (1b), (1a)
theorem ex1b_eq_comap : ex1b = ex1a.comap (Equiv.addRight (5 : Fin 9)).symm :=
  Graph.ext_label (funext₂ (by decide))

/-! ### Dependency length, §3.2 -/

/-- (2a) *She threw out the bin with old trash*. -/
def ex2a : Graph UD.DepRel (Fin 8) :=
  .ofArcs [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det), (4, 7, .nmod),
      (7, 5, .case), (7, 6, .amod)]

/-- (2b) *She threw the bin with old trash out*. -/
def ex2b : Graph UD.DepRel (Fin 8) :=
  .ofArcs [(1, 0, .nsubj), (1, 7, .compound), (1, 3, .obj), (3, 2, .det), (3, 6, .nmod),
      (6, 4, .case), (6, 5, .amod)]

/-- (3a) *She threw out the bin*. -/
def ex3a : Graph UD.DepRel (Fin 5) :=
  .ofArcs [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det)]

/-- (3b) *She threw the bin out*. -/
def ex3b : Graph UD.DepRel (Fin 5) :=
  .ofArcs [(1, 0, .nsubj), (1, 4, .compound), (1, 3, .obj), (3, 2, .det)]

-- (2), (3), (2a), §3.2 [temperley-2007]
theorem particle_shift_length :
    ex2b.totalLength - ex2a.totalLength = 4 ∧ ex3b.totalLength - ex3a.totalLength = 1 := by
  decide

/-- (4a) *The reporter who the senator attacked admitted the error*. -/
def ex4a : Graph UD.DepRel (Fin 9) :=
  .ofArcs [(6, 1, .nsubj), (1, 0, .det), (1, 5, .acl), (5, 2, .obj), (5, 4, .nsubj),
      (4, 3, .det),
      (6, 8, .obj), (8, 7, .det)]

/-- (4b) *The reporter who attacked the senator admitted the error*. -/
def ex4b : Graph UD.DepRel (Fin 9) :=
  .ofArcs [(6, 1, .nsubj), (1, 0, .det), (1, 3, .acl), (3, 2, .nsubj), (3, 5, .obj),
      (5, 4, .det),
      (6, 8, .obj), (8, 7, .det)]

-- (4a), (4b), (4) [gibson-1998]
theorem relative_filler_distance :
    (ex4a.Adj 5 2 ∧ Nat.dist (5 : Fin 9) (2 : Fin 9) = 3) ∧
      ex4b.Adj 3 2 ∧ Nat.dist (3 : Fin 9) (2 : Fin 9) = 1 := by decide

/-! ### Universal Dependencies, §4 -/

/-- The relations of the Swedish Treebank in Figure 6. -/
inductive SwedishTreebankRel where
  | DT | SS | OO | CJ
  deriving DecidableEq, Repr

/-- The relations of the Danish Dependency Treebank in Figure 6. -/
inductive DanishTreebankRel where
  | subj | nobj | dobj | coord | conj
  deriving DecidableEq, Repr

/-- The Stanford typed dependencies in Figure 6. -/
inductive StanfordRel where
  | det | nsubj | dobj | cc | conj
  deriving DecidableEq, Repr

/-- Figure 6, Swedish: *en katt jagar råttor och möss*, the conjunction heading the
coordination. -/
def fig6sv : Graph SwedishTreebankRel (Fin 6) :=
  .ofArcs [(1, 0, .DT), (2, 1, .SS), (2, 4, .OO), (4, 3, .CJ), (4, 5, .CJ)]

/-- Figure 6, Danish: *en kat jager rotter og mus*, the article heading the noun. -/
def fig6da : Graph DanishTreebankRel (Fin 6) :=
  .ofArcs [(2, 0, .subj), (0, 1, .nobj), (2, 3, .dobj), (3, 4, .coord), (4, 5, .conj)]

/-- Figure 6, English: *a cat chases rats and mice*. -/
def fig6en : Graph StanfordRel (Fin 6) :=
  .ofArcs [(1, 0, .det), (2, 1, .nsubj), (2, 3, .dobj), (3, 4, .cc), (3, 5, .conj)]

-- Figure 6, §4: at most 40% of the arcs shared pairwise, none by all three
theorem fig6_arcs :
    fig6sv.arcs.card = 5 ∧ fig6da.arcs.card = 5 ∧ fig6en.arcs.card = 5 ∧
      (fig6sv.arcs ∩ fig6en.arcs).card = 2 ∧ (fig6da.arcs ∩ fig6en.arcs).card = 2 ∧
      (fig6sv.arcs ∩ fig6da.arcs).card = 1 ∧ fig6sv.arcs ∩ fig6da.arcs ∩ fig6en.arcs = ∅ := by
  decide

/-- Function words in the sense of §2.5 and §4: adpositions, auxiliaries, conjunctions,
determiners and particles. -/
def IsFunctionWord : UD.UPOS → Prop
  | .ADP | .AUX | .CCONJ | .DET | .PART | .SCONJ => True
  | _ => False

instance : DecidablePred IsFunctionWord := fun c ↦ by
  cases c <;> unfold IsFunctionWord <;> infer_instance

/-- §4.5: content words are higher in the tree than function words: a function word heads
nothing but the further parts of a fixed expression. -/
def ContentWordsHigher {n : ℕ} (words : Fin n → Word) (g : Graph UD.DepRel (Fin n)) : Prop :=
  ∀ v w r, g.label v w = some r → IsFunctionWord (words v).cat → r = .fixed

instance {n : ℕ} (words : Fin n → Word) (g : Graph UD.DepRel (Fin n)) :
    Decidable (ContentWordsHigher words g) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The words of Figure 4, *Sue believes that Kim will rely on her*. -/
abbrev fig4Words : List Word :=
  [Word.mk' "Sue" .PROPN, Word.mk' "believes" .VERB, Word.mk' "that" .SCONJ,
    Word.mk' "Kim" .PROPN, Word.mk' "will" .AUX, Word.mk' "rely" .VERB, Word.mk' "on" .ADP,
    Word.mk' "her" .PRON]

/-- Figure 4a: function words as heads. -/
def fig4a : Graph UD.DepRel (Fin 8) :=
  .ofArcs [(1, 0, .nsubj), (1, 2, .ccomp), (2, 4, .dep), (4, 3, .nsubj),
    (4, 5, .dep), (5, 6, .obl), (6, 7, .dep)]

/-- Figure 4b: content words as heads, as in Universal Dependencies. -/
def fig4b : Graph UD.DepRel (Fin 8) :=
  .ofArcs [(1, 0, .nsubj), (1, 5, .ccomp), (5, 2, .mark), (5, 3, .nsubj),
    (5, 4, .aux), (5, 7, .obl), (7, 6, .case)]

-- Figure 4, §4.5
theorem fig4_contentWordsHigher :
    ContentWordsHigher fig4Words.get fig4b ∧
      ¬ ContentWordsHigher fig4Words.get fig4a := by decide

/-- The words of Figure 7, English. -/
abbrev fig7enWords : List Word :=
  [Word.mk' "the" .DET, Word.mk' "dog" .NOUN, Word.mk' "will" .AUX,
    Word.mk' "chase" .VERB, Word.mk' "the" .DET, Word.mk' "cat" .NOUN, Word.mk' "out" .ADP,
    Word.mk' "of" .ADP, Word.mk' "the" .DET, Word.mk' "room" .NOUN]

/-- Figure 7, English: *the dog will chase the cat out of the room*. -/
def fig7en : Graph UD.DepRel (Fin 10) :=
  .ofArcs [(3, 1, .nsubj), (1, 0, .det), (3, 2, .aux), (3, 5, .obj), (5, 4, .det),
      (3, 9, .obl),
      (9, 6, .case), (6, 7, .fixed), (9, 8, .det)]

/-- Figure 7, Finnish: *koira jahtaa kissan huoneesta*, the relations marked by case. -/
def fig7fi : Graph UD.DepRel (Fin 4) :=
  .ofArcs [(1, 0, .nsubj), (1, 2, .obj), (1, 3, .obl)]

/-- `g₁` is the content-word skeleton of `g₂` along `t`: `t` maps the positions of `g₁` onto
the content words of `g₂`, the words that are not function words, and preserves every relation
among them, the solid arcs of Figure 7. -/
def IsContentSkeleton {m n : ℕ} (t : Fin m → Fin n) (g₁ : Graph UD.DepRel (Fin m))
    (words : Fin n → Word) (g₂ : Graph UD.DepRel (Fin n)) : Prop :=
  (∀ v w, g₂.label (t v) (t w) = g₁.label v w) ∧ (∀ v, ¬ IsFunctionWord (words (t v)).cat) ∧
    ∀ u, ¬ IsFunctionWord (words u).cat → ∃ v, t v = u

-- Figure 7, §4
theorem fig7_parallel :
    IsContentSkeleton ![1, 3, 5, 9] fig7fi fig7enWords.get fig7en ∧
      ContentWordsHigher fig7enWords.get fig7en := by
  unfold IsContentSkeleton; decide

/-- Figure 9, the basic representation of *Students who forgot to come failed the oral and
written exam*: a spanning tree. -/
def fig9 : Graph UD.DepRel (Fin 12) :=
  .ofArcs [(5, 0, .nsubj), (0, 2, .acl), (2, 1, .nsubj), (2, 4, .xcomp),
    (4, 3, .mark), (5, 10, .obj), (10, 6, .det), (10, 7, .amod), (7, 9, .conj), (9, 8, .cc),
    (5, 11, .punct)]

/-- Figure 9, the enhanced representation: the relative pronoun's subject relation gives way
to one from *forgot* to *students*, the controlled subject of *come* is made explicit, and the
modifier relation is propagated to *written*. -/
def fig9Enhanced : Graph UD.DepRel (Fin 12) :=
  .ofArcs [(5, 0, .nsubj), (0, 2, .acl), (2, 0, .nsubj), (4, 0, .nsubj),
    (2, 4, .xcomp), (4, 3, .mark), (5, 10, .obj), (10, 6, .det), (10, 7, .amod),
    (10, 9, .amod), (7, 9, .conj), (9, 8, .cc), (5, 11, .punct)]

-- §4.4
theorem fig9Enhanced_not_isArborescence :
    ¬ fig9Enhanced.IsArborescence 5 ∧ (fig9Enhanced.inNeighborFinset 0).card = 3 ∧
      Relation.TransGen fig9Enhanced.Adj 0 0 := by
  decide

-- §4.4: *students* and *written* have a head in the enhanced graph that the basic tree lacks
theorem fig9_unrepresented :
    (∃ v, (fig9Enhanced.toDigraph \ fig9.toDigraph).Adj v 0) ∧
      ∃ v, (fig9Enhanced.toDigraph \ fig9.toDigraph).Adj v 9 := by
  decide

/-! ### The figures are trees -/

example : fig1.IsArborescence 2 ∧ fig3.IsArborescence 1 ∧ ex1a.IsArborescence 5 ∧
    ex1b.IsArborescence 1 ∧ ex2a.IsArborescence 1 ∧ ex2b.IsArborescence 1 := by decide
example : ex3a.IsArborescence 1 ∧ ex3b.IsArborescence 1 ∧ ex4a.IsArborescence 6 ∧
    ex4b.IsArborescence 6 ∧ fig6sv.IsArborescence 2 ∧ fig6da.IsArborescence 2 := by decide
example : fig6en.IsArborescence 2 ∧ fig4a.IsArborescence 1 ∧ fig4b.IsArborescence 1 ∧
    fig7en.IsArborescence 3 ∧ fig7fi.IsArborescence 1 ∧ fig9.IsArborescence 5 := by decide

end DeMarneffeNivre2019
