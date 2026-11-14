module

public import Linglib.Syntax.Minimalist.Theta.Realize
public import Linglib.Syntax.Minimalist.Derivation.Basic

/-!
# Marcolli and Larson (2025): Theta Theory, Operads and Coloring

The ditransitive *give* assigns agent, theme and goal, theme above goal in the hierarchy. Its
lexically anchored comb [satisfies the theta criterion](##giveComb_satisfiesCriterion). In *Mary
gave a book to John* the verb precedes its internal arguments because Internal Merge has moved it
to a non-theta position, its grid staying at the trace: the colored tree [is an unbalanced theta
structure](##gaveMoved_mem_language) that [realizes as Internal Merge of the verb followed by
External Merge of the subject](##realize_gaveMoved), and [no coloring lets the verb land in a
theta position](##gaveRaised_notMem_language).

## Implementation notes

The trace of the moved verb is a leaf anchored by the verb's trace, as the contraction quotient
of Internal Merge leaves it, colored by the verb's grid. Sentences take the non-theta root.

## TODO

* The balanced theta structures, cut at the first non-theta position on every path, and the
  head-function characterization of the bare structures; the Mandarin oblique object, moved twice.

## References

* [marcolli-larson-2025]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open ArgumentStructure

namespace MarcolliLarson2025

open Minimalist Minimalist.Theta SyntacticObject
open LexicalItem (Token)

/-- The internal theta hierarchy of *give*, in which theme outranks goal. -/
def giveHier : ThetaRole → ThetaRole → Prop :=
  fun a b ↦ a = .theme ∧ b = .goal

/-- The grid of *give*: agent, then the internal roles in hierarchy order. -/
abbrev giveGrid : List ThetaRole := [.agent, .theme, .goal]

/-- The spine of the *give* comb below the agent's residue: theme and goal discharge one vertex at
a time above the head leaf, anchored by `v`, which carries the full grid. -/
def giveSpine (book toJohn v : Token ⊕ Option Token) : Bud.Tree (Color (Token ⊕ Option Token)) :=
  .node (.free ([.agent].map .up)) (.leaf (.lex book [.down .theme]))
    (.node (.free ([.agent, .theme].map .up)) (.leaf (.lex toJohn [.down .goal]))
      (.leaf (.lex v (giveGrid.map .up))))

theorem isSpine_giveSpine (book toJohn v : Token ⊕ Option Token) :
    IsSpine giveHier [.agent] (giveSpine book toJohn v) :=
  .discharge (ρ := .theme) (by simp) rfl
    (.discharge (ρ := .goal) (by simp [giveHier]) rfl (.head rfl))

variable (mary gave book toJohn : Token)

/-- The *give* comb of *Mary gave a book to John* before movement. -/
def giveComb : Bud.Tree (Color (Token ⊕ Option Token)) :=
  .node .nontheta (.leaf (.lex (.inl mary) [.down .agent]))
    (giveSpine (.inl book) (.inl toJohn) (.inl gave))

theorem isComb_giveComb : IsComb giveHier (giveComb mary gave book toJohn) :=
  .mk [] rfl (isSpine_giveSpine ..)

theorem giveComb_mem_language : giveComb mary gave book toJohn ∈ (system giveHier).language :=
  ⟨Color.isTerminal_free, (isComb_giveComb ..).derives, by simp [giveComb, giveSpine]⟩

/-- The *give* comb discharges the verb's grid one role per vertex, so the verb's leaf is the
head and agent, theme and goal each go to one argument ([marcolli-larson-2025], (3.8)). -/
theorem giveComb_satisfiesCriterion : SatisfiesCriterion (giveComb mary gave book toJohn) :=
  (isComb_giveComb ..).satisfiesCriterion

theorem realize_giveComb :
    realize (giveComb mary gave book toJohn) =
      ↑(merge (.leaf mary) (merge (.leaf book) (merge (.leaf toJohn) (.leaf gave))) :
        SyntacticObject) :=
  rfl

/-! ### Movement to a non-theta position -/

/-- [marcolli-larson-2025]'s Example 4.7, *Mary gave a book to John*: Internal Merge has moved the
verb beside the agent's residue, keeping its grid under a non-theta root over the empty tree, and
the trace it leaves keeps the grid too. -/
def gaveMoved : Bud.Tree (Color (Token ⊕ Option Token)) :=
  .node .nontheta (.leaf (.lex (.inl mary) [.down .agent]))
    (.node (.free ([.agent].map .up))
      (.node .nontheta (.leaf (.lex (.inl gave) (giveGrid.map .up))) (.leaf .emptyTree))
      (giveSpine (.inl book) (.inl toJohn) (.inr (some gave))))

/-- The moved structure of *Mary gave a book to John* is an unbalanced theta structure, built by
colored Merge: the verb merges with the empty tree under a non-theta root, that landing site
attaches as an adjunct to the agent's residue, and the subject closes the projection
([marcolli-larson-2025], Example 4.7). -/
theorem gaveMoved_mem_language : gaveMoved mary gave book toJohn ∈ (system giveHier).language :=
  ⟨Color.isTerminal_free,
    .node (Bud.System.cherry_mem_ofCherries.2 ⟨_, rfl, .inl (.close [] .agent rfl rfl)⟩) .refl
      (.node (Bud.System.cherry_mem_ofCherries.2 ⟨_, rfl, .inr (.adjunct _)⟩)
        (.node (Bud.System.cherry_mem_ofCherries.2 ⟨_, rfl, .inl (.move _ (by simp))⟩) .refl .refl)
        ((isSpine_giveSpine ..).derives (by simp))),
    by simp [gaveMoved, giveSpine]⟩

/-- The moved structure realizes to Internal Merge of the verb in the object of the comb's spine,
followed by External Merge of the subject: the verb is pronounced in the landing site and leaves
its trace where its grid was injected ([marcolli-larson-2025], Example 4.7). -/
theorem realize_gaveMoved (hb : book ≠ gave) (hj : toJohn ≠ gave) :
    realize (gaveMoved mary gave book toJohn) = ↑(merge (.leaf mary)
      ((Step.im (.leaf gave)).apply (merge (.leaf book) (merge (.leaf toJohn) (.leaf gave))))) := by
  rw [Step.apply_im, deleteAccessible, headTrace, selHead_leaf, Option.elim,
    replace_merge_of_ne (leaf_ne_merge _ _ _).symm, replace_merge_of_ne (leaf_ne_merge _ _ _).symm,
    replace_of_toUnorderedTree_eq_leaf (toUnorderedTree_leaf book) (by simpa using hb),
    replace_of_toUnorderedTree_eq_leaf (toUnorderedTree_leaf toJohn) (by simpa using
        hj), replace_self,
    merge_comm _ (.leaf gave)]
  rfl

/-- Internal Merge cannot move the verb to a theta position: if the verb keeps its grid beside the
agent's residue, as the trace does, no color of the vertex joining them is a generator, since the
grid would be counted twice ([marcolli-larson-2025], Proposition 4.4). -/
theorem gaveRaised_notMem_language (c : Color (Token ⊕ Option Token)) :
    .node .nontheta (.leaf (.lex (.inl mary) [.down .agent]))
        (.node c (.leaf (.lex (.inl gave) (giveGrid.map .up)))
          (giveSpine (.inl book) (.inl toJohn) (.inr (some gave)))) ∉
      (system giveHier).language := by
  intro h
  obtain ⟨-, ⟨-, -, ⟨g₀, rfl, hg | hg⟩, -⟩, -⟩ := Bud.System.mem_ofCherries_language_iff.1 h <;>
    cases hg <;> simp_all [giveSpine]

/-! ### A bare theta structure the criterion rejects -/

variable (brian knows left : Token)

/-- The comb of *know* with its theme slot open, itself received as a theme. -/
def knowsComb : Bud.Tree (Color (Token ⊕ Option Token)) :=
  .node (.free [.down .theme]) (.leaf (.lex (.inl brian) [.down .experiencer]))
    (.node (.free ([.experiencer].map .up)) (.leaf (.free [.down .theme]))
      (.leaf (.lex (.inl knows) ([.experiencer, .theme].map .up))))

/-- The comb of *Mary left*, received as a theme. -/
def leftComb : Bud.Tree (Color (Token ⊕ Option Token)) :=
  .node (.free [.down .theme]) (.leaf (.lex (.inl mary) [.down .agent]))
    (.leaf (.lex (.inl left) ([.agent].map .up)))

/-- *Brian knows Mary left*, embedded as a theme: the comb of *Mary left* grafted at the theme
slot of the comb of *know*. -/
def knowsLeft : Bud.Tree (Color (Token ⊕ Option Token)) :=
  (knowsComb brian knows).graft 1 (leftComb mary left)

theorem knowsLeft_mem_language (hier : ThetaRole → ThetaRole → Prop) :
    knowsLeft mary brian knows left ∈ (bareSystem hier).language := by
  refine ⟨⟨List.cons_ne_nil _ _, Color.isTerminal_free⟩,
    .tail (.single ⟨knowsComb brian knows, ⟨?_, by simp [knowsComb]⟩, 0, rfl, rfl⟩)
      ⟨leftComb mary left, ⟨?_, by simp [leftComb]⟩, 1, rfl, rfl⟩, ?_⟩
  · exact .mk _ rfl (.discharge (ρ := .theme) (by simp) rfl (.head rfl))
  · exact .mk _ (ρE := .agent) rfl (.head rfl)
  · simp [knowsLeft, knowsComb, leftComb, Bud.Tree.graft_node]

example (hier : ThetaRole → ThetaRole → Prop) :
    knowsLeft mary brian knows left ∈ (system hier).language :=
  language_bareSystem_subset (knowsLeft_mem_language ..)

/-- [marcolli-larson-2025]'s Lemma 3.11 states that the bare theta structures satisfy the theta
criterion of its Definition 3.10, which its Theorem 3.14 then uses to single them out among the
unbalanced structures. But *Brian knows Mary left* is a bare theta structure whose leaves *know*
and *left* both carry giver grids, while the criterion allows a single head. -/
theorem knowsLeft_not_satisfiesCriterion :
    ¬ SatisfiesCriterion (knowsLeft mary brian knows left) := fun h ↦ by
  have h2 : ((knowsLeft mary brian knows left).inputs.map Color.receiver? :
      Multiset (Option ThetaRole)).count none = 2 := rfl
  have := h.count_none
  omega

end MarcolliLarson2025
