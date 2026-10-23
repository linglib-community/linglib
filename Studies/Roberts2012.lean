module

public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Entailment
public import Linglib.Semantics.Questions.Resolution
public import Linglib.Core.Data.Fintype.Sets
public import Linglib.Discourse.QUD.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.IntervalCases

/-!
# Roberts (2012): Information structure in discourse

This file formalizes the paper's worked discourse, two individuals, two foods and seven
questions forming a strategy of inquiry, on the substrate's alternative-set questions and
questions-under-discussion stacks. A world is the set of eating events that occurred, a
polar question is `Question.ofSet` of its one alternative and a wh-question the join of its
polar subquestions (1), so that the complete-answer partition (4), question entailment (8)
and the answer-composition facts (11) are derived, `completeAnswers_wh_inter`. The stack of
questions under discussion at a move (10g) is computed from the moves before it, the
questions accepted so far whose complete answer the context set fails to entail, `qud`; on
the eleven moves of the discourse it reproduces the paper's table of stacks, `qud_D₀`, each
well formed in its context set. The strategy of inquiry (12) is read off the same function,
the subquestions of a question being those accepted while it was the immediate question
under discussion, `subquestions`, and the tree so obtained is complete, `strat_complete`.
Answerhood (3) and relevance (15) are checked on the discourse's assertions.

## Implementation notes

Entailment between questions is inclusion of complete-answer sets; the substrate's lattice
order, entailment by resolution, runs the other way on the discourse's Hamblin questions
(`wh_le_q1`), as the paper notes it would off complete answers. The substrate's
inquisitive `Question.polar`, with alternatives a proposition and its complement, is a rival
yes/no convention, not the paper's singleton alternative set. The context set of a move is
the intersection of the assertions before it from a trivial initial common ground, so
contextual entailment is entailment relative to that set; a question determined to be
unanswerable, which the paper also retires, does not arise in the discourse.

## References

* [C. Roberts, *Information structure in discourse: towards an integrated formal theory of
  pragmatics* (2012)][roberts-2012]
* [C. L. Hamblin, *Questions in Montague English* (1973)][hamblin-1973b]
* [J. Groenendijk, M. Stokhof, *Studies on the semantics of questions and the pragmatics of
  answers* (1984)][groenendijk-stokhof-1984]
* [D. Büring, *On D-trees, beans, and B-accents* (2003)][buring-2003]
-/

@[expose] public section

namespace Roberts2012

open Question
open Discourse

-- `decide` on `Set`-subset goals over the finite world space.
attribute [local instance] Set.decidableSubsetOfFintype

/-! ### The world space -/

/-- The two individuals. -/
inductive Person | hilary | robin
  deriving DecidableEq, Fintype, Inhabited

/-- The two foods. -/
inductive Food | bagels | tofu
  deriving DecidableEq, Fintype, Inhabited

theorem Person.forall_person {p : Person → Prop} :
    (∀ u, p u) ↔ p .hilary ∧ p .robin :=
  ⟨λ h => ⟨h _, h _⟩, λ ⟨h1, h2⟩ u => by cases u <;> assumption⟩

theorem Food.forall_food {p : Food → Prop} :
    (∀ f, p f) ↔ p .bagels ∧ p .tofu :=
  ⟨λ h => ⟨h _, h _⟩, λ ⟨h1, h2⟩ f => by cases f <;> assumption⟩

theorem iInter_food_eq {α : Type*} {X : Food → Set α} :
    ⋂ f, X f = X .bagels ∩ X .tofu := by
  ext a
  simp [Food.forall_food]

/-- A world: the set of eating events that occurred in it. -/
abbrev World := Finset (Person × Food)

/-- `u` ate `f`: the worlds containing the event, the principal up-set of its minimal
world. -/
abbrev ate (u : Person) (f : Food) : Set World := Set.Ici {(u, f)}

theorem ate_subset_ate_iff {u u' : Person} {f f' : Food} :
    ate u f ⊆ ate u' f' ↔ u = u' ∧ f = f' := by
  simp [ate, Prod.ext_iff, eq_comm]

/-! ### The seven questions ((1), (2), (7)) -/

/-- Hilary ate the bagels. -/
abbrev hilaryBagels : Set World := ate .hilary .bagels
/-- Hilary ate the tofu. -/
abbrev hilaryTofu : Set World := ate .hilary .tofu
/-- Robin ate the bagels. -/
abbrev robinBagels : Set World := ate .robin .bagels
/-- Robin ate the tofu. -/
abbrev robinTofu : Set World := ate .robin .tofu

/-- "Did `u` eat `f`?": a yes/no question has its one proposition as alternative. -/
abbrev polar (u : Person) (f : Food) : Question World := Question.ofSet (ate u f)
/-- "What did `u` eat?": the join of its alternatives. -/
abbrev wh (u : Person) : Question World := ⨆ f, polar u f
/-- "Who ate what?", the discourse's move 1, joining alternatives over person–food pairs. -/
abbrev q_1 : Question World := ⨆ uf : Person × Food, polar uf.1 uf.2

/-- The questions of the discourse. -/
inductive Qn | one | a | ai | aii | b | bi | bii
  deriving DecidableEq, Fintype

/-- The denotation of each question. -/
def Qn.den : Qn → Question World
  | .one => q_1
  | .a => wh .hilary
  | .ai => polar .hilary .bagels
  | .aii => polar .hilary .tofu
  | .b => wh .robin
  | .bi => polar .robin .bagels
  | .bii => polar .robin .tofu

/-! ### Alternative enumerations -/

theorem ate_antichain (uf uf' : Person × Food)
    (h : ate uf.1 uf.2 ⊆ ate uf'.1 uf'.2) :
    ate uf.1 uf.2 = ate uf'.1 uf'.2 := by
  obtain ⟨h1, h2⟩ := ate_subset_ate_iff.mp h
  rw [h1, h2]

theorem alt_wh (u : Person) : alt (wh u) = Set.range (ate u) :=
  alt_iSup_ofSet (λ f f' h => ate_antichain (u, f) (u, f') h)

theorem alt_q_1 :
    alt q_1 = Set.range λ uf : Person × Food => ate uf.1 uf.2 :=
  alt_iSup_ofSet ate_antichain

theorem mem_alt_wh (u : Person) (f : Food) : ate u f ∈ alt (wh u) := by
  rw [alt_wh]; exact Set.mem_range_self f

theorem mem_alt_q1 (u : Person) (f : Food) : ate u f ∈ alt q_1 := by
  rw [alt_q_1]; exact Set.mem_range_self (u, f)

/-! ### Alternative inclusions

Subquestionhood in the discourse is alternative-set inclusion: each polar alternative is an
alternative of its wh-question, and each wh alternative is an alternative of the big
question. -/

theorem alt_polar_subset_wh (u : Person) (f : Food) :
    alt (polar u f) ⊆ alt (wh u) := by
  rw [alt_ofSet]
  exact Set.singleton_subset_iff.mpr (mem_alt_wh u f)

theorem alt_wh_subset_q1 (u : Person) : alt (wh u) ⊆ alt q_1 := by
  rw [alt_wh, alt_q_1]
  exact Set.range_comp_subset_range (Prod.mk u) λ uf => ate uf.1 uf.2

theorem alt_polar_subset_q1 (u : Person) (f : Food) :
    alt (polar u f) ⊆ alt q_1 :=
  (alt_polar_subset_wh u f).trans (alt_wh_subset_q1 u)

/-! ### The complete-answer partition (4) -/

theorem subset_corners_iff {σ A B : Set World} :
    (σ ⊆ A ∨ σ ⊆ Aᶜ) ∧ (σ ⊆ B ∨ σ ⊆ Bᶜ) ↔
      σ ⊆ A ∩ B ∨ σ ⊆ A ∩ Bᶜ ∨ σ ⊆ Aᶜ ∩ B ∨ σ ⊆ Aᶜ ∩ Bᶜ := by
  simp only [Set.subset_inter_iff]
  tauto

theorem completelyAnsweredBy_wh_iff {σ : Set World} {u : Person} :
    CompletelyAnsweredBy (wh u) σ ↔
      σ ⊆ ate u .bagels ∩ ate u .tofu ∨
      σ ⊆ ate u .bagels ∩ (ate u .tofu)ᶜ ∨
      σ ⊆ (ate u .bagels)ᶜ ∩ ate u .tofu ∨
      σ ⊆ (ate u .bagels)ᶜ ∩ (ate u .tofu)ᶜ := by
  rw [completelyAnsweredBy_iff_of_alt_eq_range (alt_wh u), Food.forall_food]
  exact subset_corners_iff

instance (C : Finset World) (S : Set World) [DecidablePred (· ∈ S)] :
    Decidable ((C : Set World) ⊆ S) :=
  decidable_of_iff (∀ w ∈ C, w ∈ S) (by simp [Set.subset_def])

/-- Whether a finite state completely answers a question of the discourse is decidable. -/
instance (C : Finset World) : ∀ q : Qn, Decidable (CompletelyAnsweredBy q.den (C : Set World))
  | .one => decidable_of_iff _ (completelyAnsweredBy_iff_of_alt_eq_range alt_q_1).symm
  | .a | .b => decidable_of_iff _ completelyAnsweredBy_wh_iff.symm
  | .ai | .aii | .bi | .bii => decidable_of_iff _ completelyAnsweredBy_ofSet_iff.symm

/-! ### Question entailment ((3), (8))

A question entails another when answering it yields a complete answer to the other: the
inclusion of complete-answer sets, which the paper tabulates for the seven questions. The
lattice order of the substrate reverses it (`wh_le_q1`, `not_q1_le_wh`). -/

theorem q1_entails_wh (u : Person) :
    completeAnswers q_1 ⊆ completeAnswers (wh u) :=
  completeAnswers_anti (alt_wh_subset_q1 u)

theorem wh_entails_polar (u : Person) (f : Food) :
    completeAnswers (wh u) ⊆ completeAnswers (polar u f) :=
  completeAnswers_anti (alt_polar_subset_wh u f)

theorem q1_entails_polar (u : Person) (f : Food) :
    completeAnswers q_1 ⊆ completeAnswers (polar u f) :=
  completeAnswers_anti (alt_polar_subset_q1 u f)

theorem wh_not_entails_q1 :
    ¬ completeAnswers (wh .hilary) ⊆ completeAnswers q_1 := λ h => by
  have := h (completelyAnsweredBy_wh_iff.mpr (Or.inl subset_rfl)) _ (mem_alt_q1 .robin .bagels)
  rcases this with h' | h' <;> exact absurd h' (by decide)

theorem polar_not_entails_wh :
    ¬ completeAnswers (polar .hilary .bagels) ⊆ completeAnswers (wh .hilary) := λ h => by
  have hma : CompletelyAnsweredBy (polar .hilary .bagels) (hilaryBagels : Set World) := λ p hp => by
    rw [alt_ofSet, Set.mem_singleton_iff] at hp
    subst hp
    exact Or.inl subset_rfl
  have := h hma _ (mem_alt_wh .hilary .tofu)
  rcases this with h' | h' <;> exact absurd h' (by decide)

theorem wh_le_q1 (u : Person) : wh u ≤ q_1 :=
  (isNormal_of_finite (Set.toFinite _)).le_of_alt_subset (alt_wh_subset_q1 u)

theorem not_q1_le_wh : ¬ q_1 ≤ wh .hilary := fun h ↦ by
  obtain ⟨_, ⟨f, rfl⟩, hf⟩ : ∃ a ∈ Set.range (ate .hilary), robinBagels ⊆ a := by
    rw [← alt_wh, ← mem_iff_exists_alt_subset (isNormal_of_finite (Set.toFinite _))]
    exact h (mem_of_mem_alt (mem_alt_q1 .robin .bagels))
  exact absurd (ate_subset_ate_iff.mp hf).1 (by decide)

/-! ### Answer composition (11)

The complete answers to a join are the meet of the complete answers,
`completeAnswers_iSup_ofSet`, so jointly answering the polar subquestions is answering the
wh-question and jointly answering the two wh-questions is answering the big question. -/

theorem completeAnswers_wh (u : Person) :
    completeAnswers (wh u) = ⋂ f, completeAnswers (polar u f) :=
  completeAnswers_iSup_ofSet (λ f f' h => ate_antichain (u, f) (u, f') h)

theorem completeAnswers_polar_inter (u : Person) :
    completeAnswers (polar u .bagels) ∩ completeAnswers (polar u .tofu)
      = completeAnswers (wh u) := by
  rw [completeAnswers_wh, iInter_food_eq]

theorem completeAnswers_wh_inter :
    completeAnswers (wh .hilary) ∩ completeAnswers (wh .robin) = completeAnswers q_1 := by
  rw [completeAnswers_iSup_ofSet ate_antichain]
  ext σ
  simp [completeAnswers_wh, Prod.forall, Person.forall_person]

/-! ### The discourse and its stacks (10g) -/

/-- A move: a setup move, which is a question, or a payoff move, which asserts that `u` ate
`f`. -/
inductive Move
  | ask (q : Qn)
  | assert (u : Person) (f : Food)

/-- The eleven moves of the discourse in order: each question is accepted and each polar
question answered yes. -/
def D₀ : List Move :=
  [.ask .one, .ask .a, .ask .ai, .assert .hilary .bagels, .ask .aii, .assert .hilary .tofu,
    .ask .b, .ask .bi, .assert .robin .bagels, .ask .bii, .assert .robin .tofu]

/-- The context set after a sequence of moves: the worlds in which every asserted event
occurred, from a trivial initial common ground. -/
def contextSet : List Move → Finset World
  | [] => Finset.univ
  | .ask _ :: ms => contextSet ms
  | .assert u f :: ms => (contextSet ms).filter λ w => (u, f) ∈ w

/-- The questions accepted in a sequence of moves, most recent first. -/
def asked : List Move → List Qn
  | [] => []
  | .ask q :: ms => asked ms ++ [q]
  | .assert _ _ :: ms => asked ms

/-- The questions under discussion after a sequence of moves: the accepted questions whose
complete answer the context set fails to entail, most recent first (10g.i). -/
def qud (ms : List Move) : List Qn :=
  (asked ms).filter λ q => decide (¬ CompletelyAnsweredBy q.den (contextSet ms : Set World))

/-- The paper's table of stacks: the questions under discussion at each of the eleven
moves, the immediate one first, and the empty stack after the last answer. -/
def table : ℕ → List Qn
  | 0 => []
  | 1 => [.one]
  | 2 => [.a, .one]
  | 3 => [.ai, .a, .one]
  | 4 => [.a, .one]
  | 5 => [.aii, .a, .one]
  | 6 => [.one]
  | 7 => [.b, .one]
  | 8 => [.bi, .b, .one]
  | 9 => [.b, .one]
  | 10 => [.bii, .b, .one]
  | _ => []

theorem qud_D₀ : ∀ k < 12, qud (D₀.take k) = table k := by decide

theorem wellFormed_wh (C : Set World) (u : Person) :
    [wh u, q_1].Pairwise (IsSubquestionOf C) :=
  List.pairwise_cons.mpr
    ⟨List.forall_mem_singleton.mpr (isSubquestionOf_of_alt_subset C (alt_wh_subset_q1 u)),
      List.pairwise_singleton ..⟩

theorem wellFormed_polar (C : Set World) (u : Person) (f : Food) :
    [polar u f, wh u, q_1].Pairwise (IsSubquestionOf C) :=
  List.pairwise_cons.mpr
    ⟨List.forall_mem_cons.mpr
        ⟨isSubquestionOf_of_alt_subset C (alt_polar_subset_wh u f),
          List.forall_mem_singleton.mpr
            (isSubquestionOf_of_alt_subset C (alt_polar_subset_q1 u f))⟩,
      wellFormed_wh C u⟩

theorem qud_wellFormed (k : ℕ) (hk : k < 12) :
    ((qud (D₀.take k)).map Qn.den).Pairwise
      (IsSubquestionOf (contextSet (D₀.take k) : Set World)) := by
  rw [qud_D₀ k hk]
  interval_cases k <;> first
    | exact List.Pairwise.nil
    | exact List.pairwise_singleton _ _
    | exact wellFormed_wh _ _
    | exact wellFormed_polar _ _ _

/-! ### The strategy of inquiry (12) -/

/-- The subquestions of a question in a sequence of moves: the questions accepted while it
was the immediate question under discussion. -/
def subquestions (ms : List Move) (q : Qn) : List Qn :=
  (List.range ms.length).filterMap λ k =>
    match ms[k]? with
    | some (Move.ask q') => if (qud (ms.take k)).head? = some q then some q' else none
    | _ => none

theorem subquestions_D₀ :
    subquestions D₀ .one = [.a, .b] ∧ subquestions D₀ .a = [.ai, .aii] ∧
      subquestions D₀ .b = [.bi, .bii] ∧
        ∀ q ∈ [Qn.ai, .aii, .bi, .bii], subquestions D₀ q = [] := by
  decide

/-- The strategy of inquiry the discourse realizes, read off its stacks. -/
def strat : Strategy World :=
  .node q_1 ((subquestions D₀ .one).map λ q =>
    .node q.den ((subquestions D₀ q).map λ q' => .leaf q'.den))

theorem strat_eq :
    strat = .node q_1
      [.node (wh .hilary) [.leaf (polar .hilary .bagels), .leaf (polar .hilary .tofu)],
        .node (wh .robin) [.leaf (polar .robin .bagels), .leaf (polar .robin .tofu)]] := by
  simp [strat, subquestions_D₀.1, subquestions_D₀.2.1, subquestions_D₀.2.2.1, Qn.den]

theorem wh_complete (u : Person) :
    Strategy.IsComplete (.node (wh u) [.leaf (polar u .bagels), .leaf (polar u .tofu)]) :=
  .node_pair (inf_le_left.trans (le_iSup (polar u) .bagels)) (.leaf _) (.leaf _)

theorem strat_complete : strat.IsComplete := by
  rw [strat_eq]
  exact .node_pair
    (inf_le_left.trans (iSup_le λ f =>
      le_iSup (λ uf : Person × Food => polar uf.1 uf.2) (.hilary, f)))
    (wh_complete .hilary) (wh_complete .robin)

theorem values_whTree (u : Person) :
    (RoseTree.node (wh u) [.leaf (polar u .bagels), .leaf (polar u .tofu)] : Strategy World).values
      = [wh u, polar u .bagels, polar u .tofu] := by
  simp [RoseTree.leaf]

theorem wh_wellFormed (C : Set World) (u : Person) :
    Strategy.WellFormed C (.node (wh u) [.leaf (polar u .bagels), .leaf (polar u .tofu)]) := by
  refine .node (λ c hc r hr => ?_) (λ c hc => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp only [RoseTree.leaf, RoseTree.values_node, List.map_nil, List.flatten_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      subst hr <;> exact isSubquestionOf_of_alt_subset C (alt_polar_subset_wh _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .leaf _ _

theorem strat_wellFormed (C : Set World) : strat.WellFormed C := by
  rw [strat_eq]
  refine .node (λ c hc r hr => ?_) (λ c hc => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rw [values_whTree] at hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl <;>
      exact isSubquestionOf_of_alt_subset C
        (by first | exact alt_wh_subset_q1 _ | exact alt_polar_subset_q1 _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact wh_wellFormed C _

/-! ### Answerhood (3)

A partial answer evaluates at least one alternative, positively or negatively; the negative
direction, ruling an alternative out, is the paper's point against confirm-only answerhood. -/

theorem neg_hilaryBagels_partiallyAnsweredBy_polar :
    PartiallyAnsweredBy (polar .hilary .bagels) (hilaryBagelsᶜ : Set World) :=
  partiallyAnsweredBy_compl_of_mem_alt (self_mem_alt_ofSet (ate .hilary .bagels))

theorem neg_hilaryBagels_partiallyAnsweredBy_wh :
    PartiallyAnsweredBy (wh .hilary) (hilaryBagelsᶜ : Set World) :=
  partiallyAnsweredBy_compl_of_mem_alt (mem_alt_wh .hilary .bagels)

theorem hilaryBagels_partiallyAnsweredBy_polar :
    PartiallyAnsweredBy (polar .hilary .bagels) (hilaryBagels : Set World) :=
  partiallyAnsweredBy_of_mem_alt (self_mem_alt_ofSet (ate .hilary .bagels))

theorem hilaryBagels_partiallyAnsweredBy_q1 :
    PartiallyAnsweredBy q_1 (hilaryBagels : Set World) :=
  partiallyAnsweredBy_of_mem_alt (mem_alt_q1 .hilary .bagels)

/-! ### Relevance (15)

Assertion-clause relevance throughout; the paper's clause for interrogative moves is
strategy membership, which `wh_relevant_to_q1` proxies by partial answerhood. -/

/-- The assertion "Hilary ate bagels": a declarative's alternative set is the singleton of
its content. -/
def hilaryBagels_assertion : Question World := Question.ofSet hilaryBagels

theorem hilaryBagels_relevant_to_q1 : hilaryBagels_assertion.IsRelevantTo {q_1} :=
  ⟨hilaryBagels, self_mem_alt_ofSet _, q_1, rfl, hilaryBagels_partiallyAnsweredBy_q1⟩

theorem wh_relevant_to_q1 : (wh .hilary).IsRelevantTo {q_1} :=
  ⟨hilaryBagels, mem_alt_wh .hilary .bagels, q_1, rfl, hilaryBagels_partiallyAnsweredBy_q1⟩

theorem hilaryBagels_relevant_to_strat :
    hilaryBagels_assertion.IsRelevantTo {q | q ∈ strat.values} :=
  ⟨hilaryBagels, self_mem_alt_ofSet _, q_1, by simp [strat_eq],
    hilaryBagels_partiallyAnsweredBy_q1⟩

end Roberts2012
