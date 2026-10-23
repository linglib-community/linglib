module

public import Linglib.Discourse.CommonGround
public import Linglib.Logic.Modal.Basic

/-!
# Multi-agent epistemic logic

The group knowledge operators of [fagin-halpern-moses-vardi-1995] over agent-indexed
accessibility `Rs : E → SetRel W W` are boxes along lattice combinations of the agents'
relations: agent `i` knows `p` at `w` when `□[Rs i] p w`, everyone in `G` knows it when
`□[⋃ i ∈ G, Rs i] p w`, it is distributed knowledge when `□[⋂ i ∈ G, Rs i] p w`, and the
hierarchy `C_G ≤ E_G ≤ Kᵢ ≤ D_G` is antitonicity in the relation (`ModalLogic.box_restrict`).
Common knowledge is the box along the transitive closure of the union: `p` holds at every world
reachable by a chain of members' accessibility ([lederman-2014] Appendix 2.B's construction),
equivalently the infinite conjunction `E_G p ∧ E_G (E_G p) ∧ ⋯`
(`commonKnowledge_iff_forall_iterate`). Belief is the same operator over a KD45 frame
(`ModalLogic.IsKD45Frame`).

## Main definitions

* `ModalLogic.CommonKnowledge`: `C_G`.
* `Filter.GroundedIn`: a common ground whose context set is exactly what is common
  knowledge ([stalnaker-2002]).

## References

* [fagin-halpern-moses-vardi-1995] — group knowledge and its reachability semantics
* [halpern-2003] — the same operators in the uncertainty setting
* [fagin-halpern-1994] — the probabilistic extension, `Studies/FaginHalpern1994.lean`
* [hintikka-1962] — knowledge as `□`
* [stalnaker-2002] — common ground as common knowledge
-/

@[expose] public section

namespace ModalLogic

open SetRel

variable {W E : Type*} {Rs : E → SetRel W W} {i : E} {G : Set E} {p : W → Prop} {w : W}

variable (Rs G) in
/-- Common knowledge among `G`: `p` holds at every world reachable from `w` by a chain of
members' accessibility. -/
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

/-- A common ground `cg : Filter W` is grounded in common knowledge when its context set
`cg.ker` is exactly the set of worlds where each accepted proposition is common knowledge
among `G` ([stalnaker-2002]). -/
def GroundedIn (cg : Filter W) (Rs : E → SetRel W W) (G : Set E) : Prop :=
  ∀ w, w ∈ cg.ker ↔ ∀ p ∈ cg, ModalLogic.CommonKnowledge Rs G (· ∈ p) w

theorem GroundedIn.commonKnowledge {cg : Filter W} {Rs : E → SetRel W W} {G : Set E}
    (h : cg.GroundedIn Rs G) {w : W} (hw : w ∈ cg.ker) {p : Set W} (hp : p ∈ cg) :
    ModalLogic.CommonKnowledge Rs G (· ∈ p) w :=
  (h w).1 hw p hp

end Filter
