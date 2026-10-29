module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Length
public import Mathlib.Data.Fin.VecNotation

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

open DependencyGrammar Morphology

/-! ### Dependency trees and projectivity, §2.4 -/

/-- Figure 1: *small dogs chase cats happily*. -/
def fig1 : Tree UD.DepRel 5 :=
  .mk' (.ofArcs [Word.mk' "small" .ADJ, Word.mk' "dogs" .NOUN, Word.mk' "chase" .VERB,
      Word.mk' "cats" .NOUN, Word.mk' "happily" .ADV]
    2 [(1, 0, .amod), (2, 1, .nsubj), (2, 3, .obj), (2, 4, .advmod)])

/-- Figure 3: *bigger dogs than mine*. -/
def fig3 : Tree UD.DepRel 4 :=
  .mk' (.ofArcs [Word.mk' "bigger" .ADJ, Word.mk' "dogs" .NOUN, Word.mk' "than" .SCONJ,
      Word.mk' "mine" .PRON]
    1 [(1, 0, .amod), (0, 3, .advmod), (3, 2, .mark)])

-- Figure 3
theorem fig3_not_isArcProjective : ¬ fig3.IsArcProjective :=
  fun h ↦ (by decide : ¬ Dominates fig3.toGraph 0 1)
    (h (by decide : fig3.Adj 0 3) 1 (Set.mem_uIcc.2 (Or.inl ⟨by decide, by decide⟩)))

theorem fig3_projection : fig3.projection 0 = [0, 2, 3] ∧ ¬ fig3.IsProjective :=
  ⟨by decide, fig3.isProjective_iff_isArcProjective.not.2 fig3_not_isArcProjective⟩

/-! ### Insensitivity to word order, §3.1 -/

/-- (1a) *While it was snowing, I went for a run*. -/
def ex1a : Tree UD.DepRel 9 :=
  .mk' (.ofArcs [Word.mk' "while" .SCONJ, Word.mk' "it" .PRON, Word.mk' "was" .AUX,
      Word.mk' "snowing" .VERB, Word.mk' "I" .PRON, Word.mk' "went" .VERB, Word.mk' "for" .ADP,
      Word.mk' "a" .DET, Word.mk' "run" .NOUN]
    5 [(5, 3, .advcl), (3, 0, .mark), (3, 1, .nsubj), (3, 2, .aux), (5, 4, .nsubj),
      (5, 8, .obl), (8, 6, .case), (8, 7, .det)])

/-- (1b) *I went for a run, while it was snowing*. -/
def ex1b : Tree UD.DepRel 9 :=
  .mk' (.ofArcs [Word.mk' "I" .PRON, Word.mk' "went" .VERB, Word.mk' "for" .ADP,
      Word.mk' "a" .DET, Word.mk' "run" .NOUN, Word.mk' "while" .SCONJ, Word.mk' "it" .PRON,
      Word.mk' "was" .AUX, Word.mk' "snowing" .VERB]
    1 [(1, 8, .advcl), (8, 5, .mark), (8, 6, .nsubj), (8, 7, .aux), (1, 0, .nsubj),
      (1, 4, .obl), (4, 2, .case), (4, 3, .det)])

-- §3.1, (1), (1b), (1a)
theorem ex1b_eq_map : ex1b.toGraph = ex1a.toGraph.map (Equiv.addRight 5) := by
  rw [Graph.ext_iff]; decide

/-! ### Dependency length, §3.2 -/

/-- (2a) *She threw out the bin with old trash*. -/
def ex2a : Tree UD.DepRel 8 :=
  .mk' (.ofArcs [Word.mk' "She" .PRON, Word.mk' "threw" .VERB, Word.mk' "out" .ADP,
      Word.mk' "the" .DET, Word.mk' "bin" .NOUN, Word.mk' "with" .ADP, Word.mk' "old" .ADJ,
      Word.mk' "trash" .NOUN]
    1 [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det), (4, 7, .nmod),
      (7, 5, .case), (7, 6, .amod)])

/-- (2b) *She threw the bin with old trash out*. -/
def ex2b : Tree UD.DepRel 8 :=
  .mk' (.ofArcs [Word.mk' "She" .PRON, Word.mk' "threw" .VERB, Word.mk' "the" .DET,
      Word.mk' "bin" .NOUN, Word.mk' "with" .ADP, Word.mk' "old" .ADJ, Word.mk' "trash" .NOUN,
      Word.mk' "out" .ADP]
    1 [(1, 0, .nsubj), (1, 7, .compound), (1, 3, .obj), (3, 2, .det), (3, 6, .nmod),
      (6, 4, .case), (6, 5, .amod)])

/-- (3a) *She threw out the bin*. -/
def ex3a : Tree UD.DepRel 5 :=
  .mk' (.ofArcs [Word.mk' "She" .PRON, Word.mk' "threw" .VERB, Word.mk' "out" .ADP,
      Word.mk' "the" .DET, Word.mk' "bin" .NOUN]
    1 [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det)])

/-- (3b) *She threw the bin out*. -/
def ex3b : Tree UD.DepRel 5 :=
  .mk' (.ofArcs [Word.mk' "She" .PRON, Word.mk' "threw" .VERB, Word.mk' "the" .DET,
      Word.mk' "bin" .NOUN, Word.mk' "out" .ADP]
    1 [(1, 0, .nsubj), (1, 4, .compound), (1, 3, .obj), (3, 2, .det)])

-- (2), (3), (2a), §3.2 [temperley-2007]
theorem particle_shift_length :
    ex2b.totalLength - ex2a.totalLength = 4 ∧ ex3b.totalLength - ex3a.totalLength = 1 := by
  decide

/-- (4a) *The reporter who the senator attacked admitted the error*. -/
def ex4a : Tree UD.DepRel 9 :=
  .mk' (.ofArcs [Word.mk' "The" .DET, Word.mk' "reporter" .NOUN, Word.mk' "who" .PRON,
      Word.mk' "the" .DET, Word.mk' "senator" .NOUN, Word.mk' "attacked" .VERB,
      Word.mk' "admitted" .VERB, Word.mk' "the" .DET, Word.mk' "error" .NOUN]
    6 [(6, 1, .nsubj), (1, 0, .det), (1, 5, .acl), (5, 2, .obj), (5, 4, .nsubj), (4, 3, .det),
      (6, 8, .obj), (8, 7, .det)])

/-- (4b) *The reporter who attacked the senator admitted the error*. -/
def ex4b : Tree UD.DepRel 9 :=
  .mk' (.ofArcs [Word.mk' "The" .DET, Word.mk' "reporter" .NOUN, Word.mk' "who" .PRON,
      Word.mk' "attacked" .VERB, Word.mk' "the" .DET, Word.mk' "senator" .NOUN,
      Word.mk' "admitted" .VERB, Word.mk' "the" .DET, Word.mk' "error" .NOUN]
    6 [(6, 1, .nsubj), (1, 0, .det), (1, 3, .acl), (3, 2, .nsubj), (3, 5, .obj), (5, 4, .det),
      (6, 8, .obj), (8, 7, .det)])

-- (4a), (4b), (4) [gibson-1998]
theorem relative_filler_distance :
    Nat.dist (ex4a.headOf 2) 2 = 3 ∧ Nat.dist (ex4b.headOf 2) 2 = 1 := by decide

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
def fig6sv : Tree SwedishTreebankRel 6 :=
  .mk' (.ofArcs [Word.mk' "en" .DET, Word.mk' "katt" .NOUN, Word.mk' "jagar" .VERB,
      Word.mk' "råttor" .NOUN, Word.mk' "och" .CCONJ, Word.mk' "möss" .NOUN]
    2 [(1, 0, .DT), (2, 1, .SS), (2, 4, .OO), (4, 3, .CJ), (4, 5, .CJ)])

/-- Figure 6, Danish: *en kat jager rotter og mus*, the article heading the noun. -/
def fig6da : Tree DanishTreebankRel 6 :=
  .mk' (.ofArcs [Word.mk' "en" .DET, Word.mk' "kat" .NOUN, Word.mk' "jager" .VERB,
      Word.mk' "rotter" .NOUN, Word.mk' "og" .CCONJ, Word.mk' "mus" .NOUN]
    2 [(2, 0, .subj), (0, 1, .nobj), (2, 3, .dobj), (3, 4, .coord), (4, 5, .conj)])

/-- Figure 6, English: *a cat chases rats and mice*. -/
def fig6en : Tree StanfordRel 6 :=
  .mk' (.ofArcs [Word.mk' "a" .DET, Word.mk' "cat" .NOUN, Word.mk' "chases" .VERB,
      Word.mk' "rats" .NOUN, Word.mk' "and" .CCONJ, Word.mk' "mice" .NOUN]
    2 [(1, 0, .det), (2, 1, .nsubj), (2, 3, .dobj), (3, 4, .cc), (3, 5, .conj)])

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
def ContentWordsHigher {n : ℕ} (g : Graph UD.DepRel n) : Prop :=
  ∀ v w r, g.label v w = some r → IsFunctionWord (g.words v).cat → r = .fixed

instance {n : ℕ} (g : Graph UD.DepRel n) : Decidable (ContentWordsHigher g) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The words of Figure 4, *Sue believes that Kim will rely on her*. -/
abbrev fig4Words : List Word :=
  [Word.mk' "Sue" .PROPN, Word.mk' "believes" .VERB, Word.mk' "that" .SCONJ,
    Word.mk' "Kim" .PROPN, Word.mk' "will" .AUX, Word.mk' "rely" .VERB, Word.mk' "on" .ADP,
    Word.mk' "her" .PRON]

/-- Figure 4a: function words as heads. -/
def fig4a : Tree UD.DepRel 8 :=
  .mk' (.ofArcs fig4Words 1 [(1, 0, .nsubj), (1, 2, .ccomp), (2, 4, .dep), (4, 3, .nsubj),
    (4, 5, .dep), (5, 6, .obl), (6, 7, .dep)])

/-- Figure 4b: content words as heads, as in Universal Dependencies. -/
def fig4b : Tree UD.DepRel 8 :=
  .mk' (.ofArcs fig4Words 1 [(1, 0, .nsubj), (1, 5, .ccomp), (5, 2, .mark), (5, 3, .nsubj),
    (5, 4, .aux), (5, 7, .obl), (7, 6, .case)])

-- Figure 4, §4.5
theorem fig4_contentWordsHigher :
    ContentWordsHigher fig4b.toGraph ∧ ¬ ContentWordsHigher fig4a.toGraph := by decide

/-- Figure 7, English: *the dog will chase the cat out of the room*. -/
def fig7en : Tree UD.DepRel 10 :=
  .mk' (.ofArcs [Word.mk' "the" .DET, Word.mk' "dog" .NOUN, Word.mk' "will" .AUX,
      Word.mk' "chase" .VERB, Word.mk' "the" .DET, Word.mk' "cat" .NOUN, Word.mk' "out" .ADP,
      Word.mk' "of" .ADP, Word.mk' "the" .DET, Word.mk' "room" .NOUN]
    3 [(3, 1, .nsubj), (1, 0, .det), (3, 2, .aux), (3, 5, .obj), (5, 4, .det), (3, 9, .obl),
      (9, 6, .case), (6, 7, .fixed), (9, 8, .det)])

/-- Figure 7, Finnish: *koira jahtaa kissan huoneesta*, the relations marked by case. -/
def fig7fi : Tree UD.DepRel 4 :=
  .mk' (.ofArcs [Word.mk' "koira" .NOUN, Word.mk' "jahtaa" .VERB, Word.mk' "kissan" .NOUN,
      Word.mk' "huoneesta" .NOUN]
    1 [(1, 0, .nsubj), (1, 2, .obj), (1, 3, .obl)])

/-- `g₁` is the content-word skeleton of `g₂` along `t`: `t` maps the positions of `g₁` onto
the content words of `g₂`, the words that are not function words, and preserves every relation
among them, the solid arcs of Figure 7. -/
def IsContentSkeleton {m n : ℕ} (t : Fin m → Fin n) (g₁ : Graph UD.DepRel m)
    (g₂ : Graph UD.DepRel n) : Prop :=
  (∀ v w, g₂.label (t v) (t w) = g₁.label v w) ∧ (∀ v, ¬ IsFunctionWord (g₂.words (t v)).cat) ∧
    ∀ u, ¬ IsFunctionWord (g₂.words u).cat → ∃ v, t v = u

-- Figure 7, §4
theorem fig7_parallel :
    IsContentSkeleton ![1, 3, 5, 9] fig7fi.toGraph fig7en.toGraph ∧
      ContentWordsHigher fig7en.toGraph := by
  unfold IsContentSkeleton; decide

/-- The words of Figure 9, *Students who forgot to come failed the oral and written exam.* -/
abbrev fig9Words : List Word :=
  [Word.mk' "Students" .NOUN, Word.mk' "who" .PRON, Word.mk' "forgot" .VERB,
    Word.mk' "to" .PART, Word.mk' "come" .VERB, Word.mk' "failed" .VERB, Word.mk' "the" .DET,
    Word.mk' "oral" .ADJ, Word.mk' "and" .CCONJ, Word.mk' "written" .ADJ,
    Word.mk' "exam" .NOUN, Word.mk' "." .PUNCT]

/-- Figure 9, the basic representation: a spanning tree. -/
def fig9 : Tree UD.DepRel 12 :=
  .mk' (.ofArcs fig9Words 5 [(5, 0, .nsubj), (0, 2, .acl), (2, 1, .nsubj), (2, 4, .xcomp),
    (4, 3, .mark), (5, 10, .obj), (10, 6, .det), (10, 7, .amod), (7, 9, .conj), (9, 8, .cc),
    (5, 11, .punct)])

/-- Figure 9, the enhanced representation: the relative pronoun's subject relation gives way
to one from *forgot* to *students*, the controlled subject of *come* is made explicit, and the
modifier relation is propagated to *written*. -/
def fig9Enhanced : Graph UD.DepRel 12 :=
  .ofArcs fig9Words 5 [(5, 0, .nsubj), (0, 2, .acl), (2, 0, .nsubj), (4, 0, .nsubj),
    (2, 4, .xcomp), (4, 3, .mark), (5, 10, .obj), (10, 6, .det), (10, 7, .amod),
    (10, 9, .amod), (7, 9, .conj), (9, 8, .cc), (5, 11, .punct)]

-- §4.4
theorem fig9Enhanced_not_isTree :
    ¬ fig9Enhanced.IsTree ∧ (fig9Enhanced.parents 0).card = 3 ∧
      Relation.TransGen fig9Enhanced.Adj 0 0 := by
  decide

theorem fig9_unrepresented :
    HasUnrepresentedArg fig9.toGraph fig9Enhanced 0 ∧
      HasUnrepresentedArg fig9.toGraph fig9Enhanced 9 := by
  decide

end DeMarneffeNivre2019
