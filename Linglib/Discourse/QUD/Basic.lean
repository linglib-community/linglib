module

public import Linglib.Core.Data.RoseTree.Licensed
public import Linglib.Semantics.Questions.Basic
public import Linglib.Semantics.Questions.Entailment
public import Linglib.Semantics.Questions.Resolution

/-!
# Questions under discussion: stack and strategy

The questions under discussion form a stack of accepted but unanswered questions, a
`List (Question W)` with the immediate QUD at its head. The stack is well formed in a context set
`C` when each question is a contextual subquestion of every question below it
(`List.Pairwise (Question.IsSubquestionOf C)`, definition (10g)). A *strategy of inquiry* is a rose
tree of questions whose children are the subquestions pursued to answer their parent (12).

## Main definitions

* `Discourse.Strategy`: strategies of inquiry as `RoseTree (Question W)`.
* `Discourse.Strategy.WellFormed`: every question in a subtree is a contextual subquestion of the
  subtree's root.
* `Discourse.Strategy.IsComplete`: at every branching node, the meet of the children's questions
  entails the parent's.

## Implementation notes

Definition (10g) makes QUD a function from moves to ordered sets of questions; a list is one value
of that function. Clause (iii) is relative to a context set because entailment in (9) is contextual
throughout; the paper warns against strengthening it to question entailment, which the
bridging-question discourse (13) violates. The paper allows a lower answered question to discharge
the higher questions of its strategy; `List.tail` is the last-in-first-out special case, and the
conditions on removal are the caller's obligation.

Definition (12) leaves the well-formedness of `Strat(q)` to "rational considerations" and its
substrategies unordered; the ordered `RoseTree` follows Büring. Contextual subquestionhood
is not transitive, so `WellFormed` relates every question of a subtree to that subtree's root, not
only to its parent. `IsComplete` is the success criterion of the D₀ discussion, not a clause of
(12); its converse, the parent entailing the meet of the children, is what (13) rules out.

`Question.IsRelevantTo` (in `Semantics/Questions/Resolution.lean`) is existential, so weaker
than (15), which requires every complete answer to the move to contextually entail a partial
answer to the QUD; and it targets a set of questions where (15) targets only `last(QUD)`. The set
version is the relevance assumption of Ippolito, Kiss and Williams, used by the definedness
condition of discourse *only* in their (16); that the set holds subquestions of the QUD is the
caller's obligation. Ginzburg's KoS orders the QUD partially, with its own update rules, in
`Discourse/Gameboard/`.

## References

* [roberts-2012]
* [buring-2003]
* [ginzburg-2012]
* [beaver-roberts-simons-tonhauser-2017]
* [riester-2019]
* [ippolito-kiss-williams-2025]
-/

@[expose] public section

namespace Discourse

/-- A strategy of inquiry is a rose tree of questions whose children are the subquestions pursued to
answer their parent ([roberts-2012] definition (12); [buring-2003]'s d-trees). -/
abbrev Strategy (W : Type*) := RoseTree (Question W)

namespace Strategy

variable {W : Type*}

/-- A strategy is well formed in the context `C` when every question in a subtree is a contextual
subquestion of that subtree's root. These are the strategies obtained from the stacks of (10g)
([roberts-2012] definition (12)). -/
inductive WellFormed (C : Set W) : Strategy W → Prop
  | node {q : Question W} {cs : List (Strategy W)}
      (sub : ∀ c ∈ cs, ∀ r ∈ c.values, Question.IsSubquestionOf C r q)
      (children : ∀ c ∈ cs, WellFormed C c) : WellFormed C (.node q cs)

theorem WellFormed.leaf (C : Set W) (q : Question W) : WellFormed C (.leaf q : Strategy W) :=
  .node nofun nofun

@[simp] theorem wellFormed_node_iff {C : Set W} {q : Question W} {cs : List (Strategy W)} :
    WellFormed C (.node q cs) ↔
      (∀ c ∈ cs, ∀ r ∈ c.values, Question.IsSubquestionOf C r q) ∧ ∀ c ∈ cs, WellFormed C c :=
  ⟨fun | .node h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .node h₁ h₂⟩

theorem WellFormed.isSubquestionOf_root {C : Set W} : ∀ {t : Strategy W}, WellFormed C t →
    ∀ r ∈ t.values, Question.IsSubquestionOf C r t.value
  | .node _ _, .node h _, r, hr => by
    rw [RoseTree.values_node, List.mem_cons, List.mem_flatten] at hr
    rcases hr with rfl | ⟨l, hl, hrl⟩
    · exact .refl _ _
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
      exact h c hc r hrl

/-- A strategy is complete when at every branching node the meet of the children's questions
entails the parent's question, so that resolving all the subquestions resolves the parent. Leaves
are complete. -/
def IsComplete (t : Strategy W) : Prop :=
  t.Licensed fun q qs ↦ qs ≠ [] → (qs : Multiset (Question W)).inf ≤ q

@[simp] theorem isComplete_node_iff {q : Question W} {cs : List (Strategy W)} :
    IsComplete (.node q cs) ↔
      (cs ≠ [] → ((cs.map RoseTree.value : Multiset (Question W))).inf ≤ q) ∧
        ∀ c ∈ cs, IsComplete c := by
  rw [IsComplete, RoseTree.licensed_node_iff, ne_eq, List.map_eq_nil_iff]
  rfl

theorem IsComplete.node {q : Question W} {cs : List (Strategy W)}
    (complete : cs ≠ [] → ((cs.map RoseTree.value : Multiset (Question W))).inf ≤ q)
    (children : ∀ c ∈ cs, IsComplete c) : IsComplete (.node q cs) :=
  isComplete_node_iff.mpr ⟨complete, children⟩

theorem IsComplete.leaf (q : Question W) : IsComplete (.leaf q : Strategy W) :=
  .node (fun h => absurd rfl h) nofun

theorem IsComplete.node_pair {q : Question W} {s t : Strategy W}
    (h : s.value ⊓ t.value ≤ q) (hs : s.IsComplete) (ht : t.IsComplete) :
    IsComplete (.node q [s, t]) :=
  .node (fun _ => by simpa using h) (by simp [hs, ht])

end Strategy

variable {W : Type*}


end Discourse
