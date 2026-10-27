module

public import Linglib.Discourse.CommonGround
public import Linglib.Logic.Modal.Basic

/-!
# Group knowledge

In epistemic logic an agent *knows* a proposition at a world when it is true at every world the
agent cannot tell apart from it. A group's *everyone*, *distributed* and *common knowledge* are
necessity along the union, the intersection and the transitive closure of the union of its
members' relations, and common knowledge [is the infinite conjunction of iterated knowledge by
everyone](##commonKnowledge_iff_forall_iterate). Belief is the same operator along a KD45 frame.
A common ground is *grounded in* common knowledge when the worlds it leaves open are exactly those
at which every proposition it accepts is common knowledge.

## Main definitions

* `ModalLogic.CommonKnowledge`: common knowledge in a group.
* `Filter.GroundedIn`: a common ground grounded in common knowledge.

## References

* [fagin-halpern-moses-vardi-1995] — group knowledge and its reachability semantics
* [halpern-2003] — the same operators in the uncertainty setting
* [fagin-halpern-1994] — the probabilistic extension, `Studies/FaginHalpern1994.lean`
* [hintikka-1962] — knowledge as necessity
* [lederman-2014] — common knowledge as reachability (UNVERIFIED: Appendix 2.B)
* [stalnaker-2002] — common ground as common knowledge
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W E : Type*} {Rs : E → SetRel W W} {i : E} {G : Set E} {p : W → Prop} {w : W}

variable (Rs G) in
/-- `p` is common knowledge among `G` at `w` when it holds at every world reachable from `w`
by a chain of worlds each accessible to some member from the one before. -/
def CommonKnowledge (p : W → Prop) (w : W) : Prop := □[transGen (⋃ i ∈ G, Rs i)] p w

theorem box_of_commonKnowledge (hi : i ∈ G) (h : CommonKnowledge Rs G p w) : □[Rs i] p w :=
  box_restrict p ((Set.subset_biUnion_of_mem (u := Rs) hi).trans subset_transGen) w h

theorem commonKnowledge_iff_forall_iterate :
    CommonKnowledge Rs G p w ↔ ∀ n, (□[⋃ i ∈ G, Rs i])^[n + 1] p w :=
  box_transGen_iff _

theorem commonKnowledge_imp (hi : i ∈ G) [(Rs i).IsRefl] (h : CommonKnowledge Rs G p w) : p w :=
  box_T (box_of_commonKnowledge hi h)

end ModalLogic

namespace Filter

variable {W E : Type*}

/-- A common ground `cg` is grounded in common knowledge among `G` when its context set
`cg.ker` is exactly the set of worlds at which every proposition it accepts is common knowledge
[stalnaker-2002]. -/
def GroundedIn (cg : Filter W) (Rs : E → SetRel W W) (G : Set E) : Prop :=
  ∀ w, w ∈ cg.ker ↔ ∀ p ∈ cg, ModalLogic.CommonKnowledge Rs G (· ∈ p) w

theorem GroundedIn.commonKnowledge {cg : Filter W} {Rs : E → SetRel W W} {G : Set E}
    (h : cg.GroundedIn Rs G) {w : W} (hw : w ∈ cg.ker) {p : Set W} (hp : p ∈ cg) :
    ModalLogic.CommonKnowledge Rs G (· ∈ p) w :=
  (h w).1 hw p hp

end Filter
