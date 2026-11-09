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

## Errata

* The bare theta structures need not satisfy the theta criterion, against the paper's lemma:
  [one comb filling an argument slot of another](##knowsLeft_not_satisfiesCriterion) leaves two
  leaves with giver grids. The proof establishes the recursive criterion of its later section.
* The criterion as printed asks only that each received role occur in the head's grid, which two
  agent arguments of an agent-theme head pass; its gloss asks for the bijection encoded here.
* The comb generators end with a role $\theta_{I,n}$ beyond the hierarchy
  $\theta_{I,1} > \dots > \theta_{I,n-1}$ the paper fixes for them.

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

/-- The internal theta hierarchy of *give*, in which theme outranks goal. -/
def giveHier : ThetaRole → ThetaRole → Prop :=
  fun a b ↦ a = .theme ∧ b = .goal

/-- The grid of *give*: agent, then the internal roles in hierarchy order. -/
abbrev giveGrid : List ThetaRole := [.agent, .theme, .goal]

/-- The spine of the *give* comb below the agent's residue: theme and goal discharge one vertex at
a time above the head leaf, anchored by `v`, which carries the full grid. -/
def giveSpine (book toJohn v : SyntacticObject) : Bud.Tree (Color SyntacticObject) :=
  .node (.free (upGrid [.agent])) (.leaf (.lex book [.down .theme]))
    (.node (.free (upGrid [.agent, .theme])) (.leaf (.lex toJohn [.down .goal]))
      (.leaf (.lex v (upGrid giveGrid))))

theorem isSpine_giveSpine (book toJohn v : SyntacticObject) :
    IsSpine giveHier [.agent] (giveSpine book toJohn v) :=
  .discharge (ρ := .theme) (by simp) (by simp)
    (.discharge (ρ := .goal) (by simp [giveHier]) (by simp) (.head (by simp)))

variable (mary gave book toJohn : LexicalItem.Token)

/-- The *give* comb of *Mary gave a book to John* before movement. -/
def giveComb : Bud.Tree (Color SyntacticObject) :=
  .node .nontheta (.leaf (.lex (.leaf mary) [.down .agent]))
    (giveSpine (.leaf book) (.leaf toJohn) (.leaf gave))

theorem isComb_giveComb : IsComb giveHier (giveComb mary gave book toJohn) :=
  .mk [] (by simp) (isSpine_giveSpine ..)

theorem giveComb_mem_language : giveComb mary gave book toJohn ∈ (system giveHier).language :=
  ⟨by simp [giveComb], (isComb_giveComb ..).derives, by simp [giveComb, giveSpine]⟩

/-- The *give* comb discharges the verb's grid one role per vertex, so the verb's leaf is the
head and agent, theme and goal each go to one argument ([marcolli-larson-2025], (3.8)). -/
theorem giveComb_satisfiesCriterion : SatisfiesCriterion (giveComb mary gave book toJohn) :=
  (isComb_giveComb ..).satisfiesCriterion

theorem realize_giveComb :
    realize (giveComb mary gave book toJohn) =
      some (merge (.leaf mary) (merge (.leaf book) (merge (.leaf toJohn) (.leaf gave)))) :=
  rfl

/-! ### Movement to a non-theta position -/

/-- [marcolli-larson-2025]'s Example 4.7, *Mary gave a book to John*: Internal Merge has moved the
verb beside the agent's residue, keeping its grid under a non-theta root over the empty tree, and
the trace it leaves keeps the grid too. -/
def gaveMoved : Bud.Tree (Color SyntacticObject) :=
  .node .nontheta (.leaf (.lex (.leaf mary) [.down .agent]))
    (.node (.free (upGrid [.agent]))
      (.node .nontheta (.leaf (.lex (.leaf gave) (upGrid giveGrid))) (.leaf .emptyTree))
      (giveSpine (.leaf book) (.leaf toJohn) (traceOf gave)))

/-- The moved structure of *Mary gave a book to John* is an unbalanced theta structure: the
landing site is an adjunct position over a movement generator ([marcolli-larson-2025], Example
4.7). -/
theorem gaveMoved_mem_language : gaveMoved mary gave book toJohn ∈ (system giveHier).language :=
  Bud.System.mem_ofCherries_language_iff.2
    ⟨by simp [gaveMoved],
      ⟨⟨_, rfl, .inl (.close [] .agent (by simp) (by simp [upGrid]))⟩, trivial,
        ⟨_, rfl, .inr (.adjunct _)⟩, ⟨⟨_, rfl, .inl (.move _ (by simp))⟩, trivial, trivial⟩,
        (isSpine_giveSpine ..).nodeLocal (by simp)⟩,
      by simp [gaveMoved, giveSpine]⟩

/-- The moved structure realizes to Internal Merge of the verb in the object of the comb's spine,
followed by External Merge of the subject: the verb is pronounced in the landing site and leaves
its trace where its grid was injected ([marcolli-larson-2025], Example 4.7). -/
theorem realize_gaveMoved (hb : book ≠ gave) (hj : toJohn ≠ gave) :
    realize (gaveMoved mary gave book toJohn) = some (merge (.leaf mary)
      ((Step.im (.leaf gave)).apply (merge (.leaf book) (merge (.leaf toJohn) (.leaf gave))))) := by
  rw [Step.apply_im, deleteAccessible, headTrace, selHead_leaf, Option.elim,
    replace_merge_of_ne (leaf_ne_merge _ _ _).symm, replace_merge_of_ne (leaf_ne_merge _ _ _).symm,
    replace_of_val_eq_leaf (leaf_val book) (by simpa using hb),
    replace_of_val_eq_leaf (leaf_val toJohn) (by simpa using hj), replace_self,
    merge_comm _ (.leaf gave)]
  rfl

/-- Internal Merge cannot move the verb to a theta position: if the verb keeps its grid beside the
agent's residue, as the trace does, no color of the vertex joining them is a generator, since the
grid would be counted twice ([marcolli-larson-2025], Proposition 4.4). -/
theorem gaveRaised_notMem_language (c : Color SyntacticObject) :
    .node .nontheta (.leaf (.lex (.leaf mary) [.down .agent]))
        (.node c (.leaf (.lex (.leaf gave) (upGrid giveGrid)))
          (giveSpine (.leaf book) (.leaf toJohn) (traceOf gave))) ∉
      (system giveHier).language := by
  intro h
  obtain ⟨-, ⟨-, -, ⟨g₀, rfl, hg | hg⟩, -⟩, -⟩ := Bud.System.mem_ofCherries_language_iff.1 h <;>
    cases hg <;> simp_all [giveSpine, upGrid, PolarizedRole.up, PolarizedRole.down]

/-! ### A bare theta structure the criterion rejects -/

variable (brian knows left : LexicalItem.Token)

/-- The comb of *know* with its theme slot open, itself received as a theme. -/
def knowsComb : Bud.Tree (Color SyntacticObject) :=
  .node (.free [.down .theme]) (.leaf (.lex (.leaf brian) [.down .experiencer]))
    (.node (.free (upGrid [.experiencer])) (.leaf (.free [.down .theme]))
      (.leaf (.lex (.leaf knows) (upGrid [.experiencer, .theme]))))

/-- The comb of *Mary left*, received as a theme. -/
def leftComb : Bud.Tree (Color SyntacticObject) :=
  .node (.free [.down .theme]) (.leaf (.lex (.leaf mary) [.down .agent]))
    (.leaf (.lex (.leaf left) (upGrid [.agent])))

/-- *Brian knows Mary left*, embedded as a theme: the comb of *Mary left* grafted at the theme
slot of the comb of *know*. -/
def knowsLeft : Bud.Tree (Color SyntacticObject) :=
  (knowsComb brian knows).graft 1 (leftComb mary left)

theorem inputs_knowsLeft : (knowsLeft mary brian knows left).inputs =
    [.lex (.leaf brian) [.down .experiencer], .lex (.leaf mary) [.down .agent],
      .lex (.leaf left) (upGrid [.agent]), .lex (.leaf knows) (upGrid [.experiencer, .theme])] :=
  rfl

theorem knowsLeft_mem_language (hier : ThetaRole → ThetaRole → Prop) :
    knowsLeft mary brian knows left ∈ (bareSystem hier).language := by
  refine ⟨⟨⟨_, by simp, rfl⟩, Color.isTerminal_free⟩,
    .tail (.single ⟨knowsComb brian knows, ⟨?_, _, by simp, rfl⟩, 0, rfl, rfl⟩)
      ⟨leftComb mary left, ⟨?_, _, by simp, rfl⟩, 1, rfl, rfl⟩, ?_⟩
  · exact .mk _ (by simp) (.discharge (ρ := .theme) (by simp) (by simp) (.head (by simp)))
  · exact .mk _ (ρE := .agent) (by simp) (.head (by simp))
  · simp [inputs_knowsLeft]

example (hier : ThetaRole → ThetaRole → Prop) :
    knowsLeft mary brian knows left ∈ (system hier).language :=
  language_bareSystem_subset (knowsLeft_mem_language ..)

/-- [marcolli-larson-2025]'s Lemma 3.11 states that the bare theta structures satisfy the theta
criterion of its Definition 3.10, which its Theorem 3.14 then uses to single them out among the
unbalanced structures. But *Brian knows Mary left* is a bare theta structure whose leaves *know*
and *left* both carry giver grids, while the criterion allows a single head. -/
theorem knowsLeft_not_satisfiesCriterion :
    ¬ SatisfiesCriterion (knowsLeft mary brian knows left) := fun h ↦ by
  have h2 : (knowsLeft mary brian knows left).inputs.countP (fun c ↦ c.receiver?.isNone) = 2 :=
    rfl
  have := h.countP_receiver?_isNone_le_one
  omega

end MarcolliLarson2025
