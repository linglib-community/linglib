/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Syntax.Minimalist.Workspace.Merge.SyntacticObject

/-!
# Derivations on the workspace

A derivation step applies an algebraic Merge at the current object, beside a spectator workspace of
the items still to come. When it matches no accessible term of the spectators, and an Internal
Merge raises a uniquely accessible proper term, [the step is the algebraic Merge on the
workspace](##Minimalist.Step.mergeOp_workspace), and [an admissible derivation is the iterated
algebraic Merge](##Minimalist.Derivation.mergeOpList_initial) on the workspace of its initial
object and its items. A Merge step is also MERGE on the workspace as a multiset, [Internal Merge
leaving the trace of the mover's head](##Minimalist.Step.apply_im_eq_mergeWith).

## TODO

* Extend `Step.Admissible` and `Step.mergeOp_workspace` to `extract` and `remerge`, the two stages
  of Internal Merge, on the workspace of the object, its stack and the items still to come.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.6) and §1.4 (Lemma 1.4.1,
  Proposition 1.4.2)
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open ConnesKreimer

/-- An object with a unique accessible proper term is a Merge. -/
theorem exists_eq_merge_of_count_terms {mover current : SyntacticObject}
    (h : current.terms.count mover = 1) (hne : current ≠ mover) : ∃ l r, current = merge l r := by
  induction current using ind with
  | leaf tok =>
    rw [terms_leaf] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (by omega))).symm hne
  | trace =>
    rw [terms_trace] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (by omega))).symm hne
  | traceOf tok =>
    rw [terms_traceOf] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (by omega))).symm hne
  | merge l r _ _ => exact ⟨l, r, rfl⟩

end Minimalist.SyntacticObject

namespace Minimalist

open SyntacticObject ConnesKreimer

/-! ### Steps as algebraic Merges

A step merges the current object with the items it introduces, beside a spectator workspace of the
items still to come. When it matches no accessible term of the spectators, and an Internal Merge
raises a uniquely accessible proper term, the step is the algebraic Merge on the workspace. The two
stages of Internal Merge, `extract` and `remerge`, act on the stack beside the object, which this
workspace leaves out, so they are not admissible here. -/

/-- A step applies an algebraic Merge at the current object, External Merge with the item or the
    unit stage followed by External Merge of the remainder with the mover. -/
noncomputable def Step.mergeOp (step : Step)
    (current : SyntacticObject) :
    ConnesKreimer ℤ (UnorderedTree Vertex) →ₗ[ℤ] ConnesKreimer ℤ (UnorderedTree Vertex) :=
  match step with
  | .em _ item => Merge.traceMergeOp traceEncoder Vertex.bare current.toUnorderedTree item.toSyntacticObject.toUnorderedTree
  | .im mover _ => Merge.traceMergeOp traceEncoder Vertex.bare (deleteAccessible mover current).toUnorderedTree
      mover.toUnorderedTree ∘ₗ Merge.traceMergeOpUnit traceEncoder mover.toUnorderedTree
  | .extract mover => Merge.traceMergeOpUnit traceEncoder mover.toUnorderedTree
  | .remerge _ => 0

/-- A step at the current object is admissible beside a spectator workspace `W` when it matches
    no accessible term of `W`, and an Internal Merge raises a uniquely accessible proper term that
    is not a trace. -/
def Step.Admissible (current : SyntacticObject)
    (W : Workspace) : Step → Prop
  | .em _ item => ∀ U ∈ W, current ∉ U.terms ∧ ↑item ∉ U.terms
  | .im mover _ => mover.toUnorderedTree.value.isLeft ∧ current.terms.count mover = 1 ∧ current ≠ mover ∧
      ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms
  | .extract _ | .remerge _ => False

/-- An admissible step is the algebraic Merge on the workspace of the current object, the items
    it introduces, and the spectators. -/
theorem Step.mergeOp_workspace {step : Step}
    {current : SyntacticObject} {W : Workspace} (h : step.Admissible current W) :
    step.mergeOp current (ConnesKreimer.of' (({current} + step.items + W).map SyntacticObject.toUnorderedTree))
      = ConnesKreimer.of' (({step.apply current} + W).map SyntacticObject.toUnorderedTree) := by
  cases step with
  | em side item =>
    rw [Step.apply_em, merge_comm]
    exact traceMergeOp_node_residual traceEncoder current ↑item h
  | im mover _ =>
    obtain ⟨hm, hc, hne, hW⟩ := h
    exact traceMergeOp_im_residual hm hc hne hW
  | extract _ | remerge _ => exact h.elim

/-- The algebraic Merges of a list of steps from the current object, composed in order. -/
noncomputable def Step.mergeOpList :
    List Step → SyntacticObject →
      ConnesKreimer ℤ (UnorderedTree Vertex) →ₗ[ℤ] ConnesKreimer ℤ (UnorderedTree Vertex)
  | [], _ => LinearMap.id
  | step :: steps, current => Step.mergeOpList steps (step.apply current) ∘ₗ step.mergeOp current

/-- Every step of a list is admissible beside the items still to come. -/
def Step.AdmissibleList : List Step → SyntacticObject → Prop
  | [], _ => True
  | step :: steps, current =>
      step.Admissible current (Step.itemsList steps) ∧
        Step.AdmissibleList steps (step.apply current)

/-- Admissible steps compose to the algebraic Merge from the workspace of the current object and
    the items they introduce to the object they build. -/
theorem Step.mergeOpList_workspace :
    ∀ (steps : List Step) (current : SyntacticObject), Step.AdmissibleList steps current →
      Step.mergeOpList steps current
          (ConnesKreimer.of' (({current} + Step.itemsList steps).map SyntacticObject.toUnorderedTree))
        = ConnesKreimer.of' {(steps.foldl (fun so step => step.apply so) current).toUnorderedTree}
  | [], current, _ => by
    simp [Step.mergeOpList]
  | step :: steps, current, ⟨h, hs⟩ => by
    rw [Step.mergeOpList, LinearMap.comp_apply, Step.itemsList_cons, ← add_assoc,
      Step.mergeOp_workspace h, List.foldl_cons]
    exact Step.mergeOpList_workspace steps (step.apply current) hs

/-- Admissible steps leave the stack alone and build what they build on the object. -/
theorem Step.foldl_run_of_admissibleList :
    ∀ (steps : List Step) (current : SyntacticObject) (st : List SyntacticObject),
      Step.AdmissibleList steps current →
      steps.foldl (fun c step ↦ step.run c) ⟨current, st⟩
        = ⟨steps.foldl (fun so step ↦ step.apply so) current, st⟩
  | [], _, _, _ => rfl
  | step :: steps, current, st, ⟨h, hs⟩ => by
    have : step.run ⟨current, st⟩ = ⟨step.apply current, st⟩ := by
      cases step with
      | em _ _ | im _ _ => rfl
      | extract _ | remerge _ => exact h.elim
    rw [List.foldl_cons, List.foldl_cons, this]
    exact Step.foldl_run_of_admissibleList steps _ st hs

variable {τ : SyntacticObject → Option LexicalItem.Token}

/-! ### Steps as MERGE

A Merge step is MERGE on the workspace of the current object, the items it introduces and the
spectators: External Merge leaving copies (`Workspace.merge`), and Internal Merge leaving the trace
of the mover's head (`Workspace.mergeWith`). Of the two stages of Internal Merge, `extract`
contracts and puts the mover's copy on the stack, and `remerge` is MERGE of that copy and the
current object on the workspace that holds the stack. -/

/-- External Merge is MERGE of the item and the current object. -/
theorem Step.apply_em_eq_merge (side : Edge) (item : PlanarSyntacticObject)
    (current : SyntacticObject) (W : Workspace) :
    {(Step.em side item).apply current τ} + W =
      ({current} + (Step.em side item).items + W).merge ↑item current := by
  have h : ({current} + {↑item} + W : Workspace) = ({↑item} + {current}) + W := by abel
  rw [Step.apply_em, Step.items, Workspace.merge_def, h, Multiset.insert_eq_cons,
    ← Multiset.singleton_add, add_tsub_cancel_left, add_comm]

/-- Internal Merge is MERGE of the mover and the current object leaving the trace of the mover's
    head. -/
theorem Step.apply_im_eq_mergeWith (side : Edge) {mover current : SyntacticObject} {W : Workspace}
    (hmc : mover ∈ current.terms) (hne : current ≠ mover) (hW : ∀ U ∈ W, mover ∉ U.terms) :
    {(Step.im mover side).apply current τ} + W =
      ({current} + W).mergeWith (·.headTrace τ) mover current := by
  rw [Workspace.mergeWith_internal hmc hne hW, add_comm, merge_comm]
  rfl

/-- Merging the copy on top of the stack back is MERGE of the copy and the current object, on the
    workspace of the object, its stack and the spectators. -/
theorem Step.run_remerge_eq_merge (side : Edge) (current m : SyntacticObject)
    (st : List SyntacticObject) (W : Workspace) :
    {((Step.remerge side).run ⟨current, m :: st⟩ τ).current} +
        ↑((Step.remerge side).run ⟨current, m :: st⟩ τ).stack + W =
      ({current} + ↑(m :: st) + W).merge m current := by
  show {merge m current} + ↑st + W = _
  have h : ({current} + ↑(m :: st) + W : Workspace) = ({m} + {current}) + (↑st + W) := by
    rw [← Multiset.cons_coe, ← Multiset.singleton_add]; abel
  rw [Workspace.merge_def, h, Multiset.insert_eq_cons, ← Multiset.singleton_add,
    add_tsub_cancel_left]
  abel

namespace Derivation

/-- A derivation is admissible when each of its steps is, beside the items still to come. -/
def Admissible (d : Derivation) : Prop := Step.AdmissibleList d.steps d.initial

/-- An admissible derivation is the iterated algebraic Merge on the workspace of its initial object
    and its items: the composite of its steps' Merges sends that workspace to its final object. -/
theorem mergeOpList_initial {d : Derivation} (hd : d.Admissible) :
    Step.mergeOpList d.steps d.initial
        (ConnesKreimer.of' (({d.initial} + d.items).map SyntacticObject.toUnorderedTree))
      = ConnesKreimer.of' {d.final.toUnorderedTree} :=
  (Step.mergeOpList_workspace d.steps d.initial hd).trans <| by
    rw [final, run, Step.foldl_run_of_admissibleList d.steps d.initial [] hd]

end Derivation

end Minimalist
