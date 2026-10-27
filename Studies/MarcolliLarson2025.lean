module

public import Linglib.Syntax.Minimalist.Theta.Basic
public import Linglib.Syntax.Minimalist.Theta.Realize

/-!
# Marcolli and Larson (2025): Theta Theory, Operads and Coloring

This file runs the theta bud system of `Syntax/Minimalist/Theta` on the paper's worked examples.
The ditransitive *Brian gave the book to Mary*, whose verb assigns agent, theme and goal with
theme before goal, is derivable as a bare comb, satisfies the theta criterion, and once anchored
in lexical items belongs to the language of unbalanced theta structures and realizes to its bare
Merge structure. A movement landing site admits only the non-theta root. Siloni's parasitic
assignment is a dual-receiver generator that the standard rules lack and the *se* marking adds.

## References

* [marcolli-larson-2025]
* [marcolli-chomsky-berwick-2025]
* [siloni-2012]
-/

@[expose] public section

open ArgumentStructure

namespace MarcolliLarson2025

open Minimalist Minimalist.Theta
open Bud.Tree (cherry)

/-- The example's internal theta hierarchy, in which theme outranks goal, per the ditransitive
grid the paper builds for *give*. -/
def giveHier : ThetaRole → ThetaRole → Prop :=
  fun a b ↦ a = .theme ∧ b = .goal

/-- The *give* comb, in which agent, theme and goal discharge one node at a time below the head
leaf carrying the full giver grid. -/
def giveComb : Bud.Tree (Color Unit) :=
  comb [] .agent [.theme, .goal]

theorem giveComb_derivable :
    (system (L := Unit) giveHier).Derives (.leaf .nontheta) giveComb :=
  comb_derivable [] .agent [.theme, .goal] (List.isChain_pair.mpr ⟨rfl, rfl⟩)

theorem giveComb_thetaLocal : giveComb.NodeLocal (ThetaLocal (L := Unit) giveHier) :=
  (Bud.System.ofCherries_derives_leaf_iff.1 giveComb_derivable).2

theorem giveComb_criterion : SatisfiesCriterion giveComb :=
  comb_satisfiesCriterion [] .agent [.theme, .goal]

/-- A movement landing site over the residual agent grid. -/
def moveRule : Bud.Tree (Color Unit) :=
  cherry .nontheta (.free (upGrid [.agent])) .emptyTree

theorem moveRule_mem : moveRule ∈ (system (L := Unit) giveHier).rules :=
  Bud.System.cherry_mem_ofCherries.2 ⟨[], rfl, .inl (.move _ (by simp))⟩

theorem eq_nontheta_of_cherry_mem {c : Color Unit}
    (h : cherry c (.free (upGrid [.agent])) .emptyTree ∈ (system giveHier).rules) :
    c = .nontheta :=
  (Bud.System.cherry_mem_ofCherries.1 h).eq_nontheta (.inr rfl)

/-! ### A language-specific generator: parasitic assignment

[siloni-2012]'s syntactic reciprocalization assigns a retained internal role together with the
external role to one argument, a last resort licensed by the *se* morphology. In the coloring
model this is a dual-receiver generator: one argument receives two roles against a dual-giver
residue, as in the ECM derivation where *Jean* ends with the matrix experiencer role and the
embedded verb's retained agent role. -/

/-- Parasitic assignment as a generator, at which a dual-receiver argument discharges a
dual-giver residue in one step. -/
def parasiticGen : Bud.Tree (Color Unit) :=
  cherry .nontheta (.free [.down .experiencer, .down .agent])
    (.free (upGrid [.experiencer, .agent]))

theorem parasiticGen_notMem : parasiticGen ∉ (system (L := Unit) giveHier).rules := by
  rw [parasiticGen, Bud.System.cherry_mem_ofCherries]
  rintro ⟨g₀, hc, hg | hg⟩ <;> cases hg <;>
    simp_all [upGrid, PolarizedRole.up, PolarizedRole.down]

/-- The *se*-marked grammar, the system extended by the parasitic generator. -/
def seSystem : Bud.System (Color Unit) :=
  { system giveHier with rules := insert parasiticGen (system giveHier).rules }

/-- With the marking, the dual-role discharge is derivable: *Jean* ends with both the matrix
experiencer role and the retained embedded agent role. -/
theorem parasiticGen_derivable : seSystem.Derives (.leaf .nontheta) parasiticGen :=
  Bud.System.Produces.single ⟨_, Set.mem_insert .., 0, rfl, rfl⟩

/-- Without the marking, the dual-role configuration is underivable: the structure is
movement-free and its root receives no role, so the sole-role invariant forbids the
dual-receiver argument. The sole-role requirement of [siloni-2012]'s "I"-reading account. -/
theorem parasiticGen_not_derivable :
    ¬ (system (L := Unit) giveHier).Derives (.leaf .nontheta) parasiticGen := by
  intro h
  have := derives_soleReceiver h
    (Color.soleReceiver_of_receiverCount_le (g := []) rfl (by simp [receiverCount]))
    (by simp [parasiticGen]) (.free [.down .experiencer, .down .agent])
    (by simp [parasiticGen]) _ rfl
  simp [receiverCount, PolarizedRole.down] at this

/-! ### Realization -/

theorem giveComb_adjunct_derivable :
    (system (L := Unit) giveHier).Derives (.leaf .nontheta)
      (.node .nontheta giveComb (.leaf .nontheta)) :=
  .node (Bud.System.cherry_mem_ofCherries.2 ⟨[], rfl, .inl (.adjunct [])⟩) giveComb_derivable .refl

variable (brian gave theBook toMary : LexicalItem.Token)

/-- The lexically anchored *give* comb. -/
def anchoredGiveComb : Bud.Tree (Color LexicalItem.Token) :=
  .node .nontheta (.leaf (.lex brian [.down .agent]))
    (.node (.free (upGrid [.agent])) (.leaf (.lex theBook [.down .theme]))
      (.node (.free (upGrid [.agent, .theme]))
        (.leaf (.lex toMary [.down .goal]))
        (.leaf (.lex gave (upGrid [.agent, .theme, .goal])))))

/-- The anchored *give* comb is an unbalanced theta structure: its root is initial, its leaves
are lexical, and each vertex discharges one role of the verb's grid. -/
theorem anchoredGiveComb_mem_language :
    anchoredGiveComb brian gave theBook toMary ∈ (system giveHier).language := by
  refine Bud.System.mem_ofCherries_language_iff.2
    ⟨by simp [anchoredGiveComb], ⟨?_, trivial, ⟨_, rfl, ?_⟩, trivial, ⟨_, rfl, ?_⟩, trivial, trivial⟩,
      by simp [anchoredGiveComb, Color.IsTerminal]⟩
  · exact ⟨[], rfl, .inl (.close [] .agent (by simp) (by simp [upGrid]))⟩
  · exact .inl (.discharge [.agent] .theme (by simp) (by simp) (by simp) (by simp [upGrid]))
  · exact .inl <| .discharge [.agent, .theme] .goal (by simp) (by simp [giveHier]) (by simp)
      (by simp [upGrid])

theorem realize_anchoredGiveComb :
    realize (anchoredGiveComb brian gave theBook toMary) =
      some ((SyntacticObject.leaf brian).merge
        ((SyntacticObject.leaf theBook).merge
          ((SyntacticObject.leaf toMary).merge
            (SyntacticObject.leaf gave)))) := rfl

theorem realize_anchored_move_landing :
    realize (.node .nontheta (anchoredGiveComb brian gave theBook toMary)
        (.leaf .emptyTree)) =
      realize (anchoredGiveComb brian gave theBook toMary) :=
  realize_node_emptyTree_right

end MarcolliLarson2025
