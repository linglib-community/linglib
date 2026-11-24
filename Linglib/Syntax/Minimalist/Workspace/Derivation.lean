/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Syntax.Minimalist.Workspace.Algebra

/-!
# Derivations on the workspace

A derivation step applies an algebraic Merge at a configuration, the current object and a stack of
extracted copies, beside a spectator workspace of the items still to come. When it matches no
accessible term of the other components, and Internal Merge or its unit stage raises a uniquely
accessible proper term, [the step is the algebraic Merge on the
workspace](##Minimalist.Step.mergeOp_run) of the object, the stack and the spectators, for External
Merge, Internal Merge and its two stages alike, and [a derivation admissible on its configurations
is the iterated algebraic Merge](##Minimalist.Derivation.mergeOpList_run) on the workspace of its
initial object and its items. A Merge step is also MERGE on the workspace as a multiset,
[Internal Merge leaving the trace of the mover's head](##Minimalist.Step.apply_im_eq_mergeWith).

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
    rw [terms_labelledTrace] at h
    exact absurd (Multiset.mem_singleton.mp (Multiset.count_pos.mp (h ▸ Nat.one_pos))).symm hne
  | merge l r _ _ => exact ⟨l, r, rfl⟩

end Minimalist.SyntacticObject

namespace Minimalist

open SyntacticObject ConnesKreimer

/-! ### Steps as algebraic Merges

A step acts on a configuration, the current object and a stack of extracted copies, beside a
spectator workspace of the items still to come. External Merge, Internal Merge, and the two stages
of Internal Merge, `extract` and `remerge`, are each an algebraic Merge on the workspace of the
object, the stack and the spectators, when the step matches no accessible term of the other
components. -/

/-- A step applies an algebraic Merge at a configuration: External Merge with the item, the unit
    stage followed by External Merge of the remainder with the mover, the unit stage alone, or
    External Merge of the copy on top of the stack with the current object. -/
noncomputable def Step.mergeOp (step : Step) (c : Derivation.Cfg SyntacticObject) :
    ConnesKreimer ℤ SyntacticObject →ₗ[ℤ] ConnesKreimer ℤ SyntacticObject :=
  match step, c.stack with
  | .em _ item, _ => Workspace.traceMergeOp c.current item.toSyntacticObject
  | .im mover _, _ =>
      Workspace.traceMergeOp (deleteAccessible mover c.current) mover ∘ₗ
        Workspace.traceMergeOpUnit mover
  | .extract mover, _ => Workspace.traceMergeOpUnit mover
  | .remerge _, m :: _ => Workspace.traceMergeOp m c.current
  | .remerge _, [] => 0

/-- A Merge step at the current object is admissible beside a spectator workspace `W` when it
    matches no accessible term of `W`, and an Internal Merge raises a uniquely accessible proper
    term that is not a trace. The two stages of Internal Merge are not Merge steps. -/
def Step.Admissible (current : SyntacticObject)
    (W : Workspace) : Step → Prop
  | .em _ item => ∀ U ∈ W, current ∉ U.terms ∧ ↑item ∉ U.terms
  | .im mover _ => ¬ mover.IsTrace ∧ current.terms.count mover = 1 ∧
      current ≠ mover ∧
      ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms
  | .extract _ | .remerge _ => False

/-- A step at a configuration is admissible beside a spectator workspace `W` when it matches no
    accessible term of the stack or of `W`: a Merge step is admissible beside the stack and `W`,
    `extract` takes a uniquely accessible proper term that is not a trace, and `remerge` finds a
    copy on the stack. -/
def Step.AdmissibleAt (c : Derivation.Cfg SyntacticObject) (W : Workspace) : Step → Prop
  | .extract mover => ¬ mover.IsTrace ∧ c.current.terms.count mover = 1 ∧ c.current ≠ mover ∧
      ∀ U ∈ (↑c.stack + W : Workspace), mover ∉ U.terms
  | .remerge _ => ∃ m st, c.stack = m :: st ∧
      ∀ U ∈ (↑st + W : Workspace), m ∉ U.terms ∧ c.current ∉ U.terms
  | step => step.Admissible c.current (↑c.stack + W)

/-- A Merge step keeps the stack. -/
theorem Step.Admissible.run_eq {step : Step} {current : SyntacticObject} {W : Workspace}
    (h : step.Admissible current W) (st : List SyntacticObject) :
    step.run ⟨current, st⟩ = ⟨step.apply current, st⟩ := by
  cases step with
  | em _ _ | im _ _ => rfl
  | extract _ | remerge _ => exact h.elim

/-- A Merge step admissible beside `W` is admissible at the configuration with an empty stack. -/
theorem Step.Admissible.admissibleAt {step : Step} {current : SyntacticObject} {W : Workspace}
    (h : step.Admissible current W) : step.AdmissibleAt ⟨current, []⟩ W := by
  cases step with
  | em side item =>
    show (Step.em side item).Admissible current (↑([] : List SyntacticObject) + W)
    rwa [Multiset.coe_nil, zero_add]
  | im mover side =>
    show (Step.im mover side).Admissible current (↑([] : List SyntacticObject) + W)
    rwa [Multiset.coe_nil, zero_add]
  | extract _ | remerge _ => exact h.elim

/-- An admissible step is the algebraic Merge on the workspace of the current object, the stack,
    the items it introduces and the spectators. -/
theorem Step.mergeOp_run {step : Step} {c : Derivation.Cfg SyntacticObject} {W : Workspace}
    (h : step.AdmissibleAt c W) :
    step.mergeOp c (ConnesKreimer.of' ({c.current} + ↑c.stack + step.items + W : Workspace)) =
      ConnesKreimer.of' ({(step.run c).current} + ↑(step.run c).stack + W : Workspace) := by
  obtain ⟨current, stack⟩ := c
  cases step with
  | em side item =>
    have e : ({current} + ↑stack + {↑item} + W : Workspace) =
        ({current, ↑item} + (↑stack + W) : Workspace) := by
      rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      abel
    show Workspace.traceMergeOp current ↑item
        (ConnesKreimer.of' ({current} + ↑stack + {↑item} + W : Workspace)) =
      ConnesKreimer.of' ({merge ↑item current} + ↑stack + W : Workspace)
    rw [e, Workspace.traceMergeOp_of'_add h, merge_comm, add_assoc]
  | im mover side =>
    obtain ⟨hm, hc, hne, hW⟩ := h
    show Workspace.traceMergeOp (deleteAccessible mover current) mover
      (Workspace.traceMergeOpUnit mover
        (ConnesKreimer.of' ({current} + ↑stack + 0 + W : Workspace))) =
      ConnesKreimer.of' ({merge (deleteAccessible mover current) mover} + ↑stack + W : Workspace)
    rw [add_zero, add_assoc, Workspace.traceMergeOp_traceMergeOpUnit_of'_add hm hc hne hW,
      add_assoc]
  | extract mover =>
    obtain ⟨hm, hc, hne, hW⟩ := h
    show Workspace.traceMergeOpUnit mover
        (ConnesKreimer.of' ({current} + ↑stack + 0 + W : Workspace)) =
      ConnesKreimer.of' ({deleteAccessible mover current} + ↑(mover :: stack) + W : Workspace)
    rw [add_zero, add_assoc, Workspace.traceMergeOpUnit_of'_add hm hc hne hW]
    congr 1
    rw [← Multiset.cons_coe, Multiset.insert_eq_cons, ← Multiset.singleton_add,
      ← Multiset.singleton_add]
    abel
  | remerge side =>
    obtain ⟨m, st, rfl, hW⟩ := h
    have e : ({current} + ↑(m :: st) + 0 + W : Workspace) =
        ({m, current} + (↑st + W) : Workspace) := by
      rw [← Multiset.cons_coe, Multiset.insert_eq_cons, ← Multiset.singleton_add,
        ← Multiset.singleton_add]
      abel
    show Workspace.traceMergeOp m current
        (ConnesKreimer.of' ({current} + ↑(m :: st) + 0 + W : Workspace)) =
      ConnesKreimer.of' ({merge m current} + ↑st + W : Workspace)
    rw [e, Workspace.traceMergeOp_of'_add hW, add_assoc]

/-- An admissible Merge step is the algebraic Merge on the workspace of the current object, the
    items it introduces, and the spectators. -/
theorem Step.mergeOp_workspace {step : Step}
    {current : SyntacticObject} {W : Workspace} (h : step.Admissible current W) :
    step.mergeOp ⟨current, []⟩ (ConnesKreimer.of' ({current} + step.items + W)) =
      ConnesKreimer.of' ({step.apply current} + W) := by
  simpa [h.run_eq] using Step.mergeOp_run h.admissibleAt

/-- The algebraic Merges of a list of steps from a configuration, composed in order. -/
noncomputable def Step.mergeOpList : List Step → Derivation.Cfg SyntacticObject →
    ConnesKreimer ℤ SyntacticObject →ₗ[ℤ] ConnesKreimer ℤ SyntacticObject
  | [], _ => LinearMap.id
  | step :: steps, c => Step.mergeOpList steps (step.run c) ∘ₗ step.mergeOp c

/-- Every Merge step of a list is admissible beside the items still to come. -/
def Step.AdmissibleList : List Step → SyntacticObject → Prop
  | [], _ => True
  | step :: steps, current =>
      step.Admissible current (Step.itemsList steps) ∧
        Step.AdmissibleList steps (step.apply current)

/-- Every step of a list is admissible at the configuration it is run at, beside the items still
    to come. -/
def Step.AdmissibleListAt : List Step → Derivation.Cfg SyntacticObject → Prop
  | [], _ => True
  | step :: steps, c =>
      step.AdmissibleAt c (Step.itemsList steps) ∧ Step.AdmissibleListAt steps (step.run c)

theorem Step.AdmissibleList.admissibleListAt :
    ∀ (steps : List Step) (current : SyntacticObject), Step.AdmissibleList steps current →
      Step.AdmissibleListAt steps ⟨current, []⟩
  | [], _, _ => trivial
  | step :: steps, current, ⟨h, hs⟩ => by
    refine ⟨h.admissibleAt, ?_⟩
    rw [h.run_eq]
    exact Step.AdmissibleList.admissibleListAt steps _ hs

/-- Admissible steps compose to the algebraic Merge from the workspace of a configuration and the
    items they introduce to the workspace of the configuration they reach. -/
theorem Step.mergeOpList_run :
    ∀ (steps : List Step) (c : Derivation.Cfg SyntacticObject), Step.AdmissibleListAt steps c →
      Step.mergeOpList steps c
          (ConnesKreimer.of' ({c.current} + ↑c.stack + Step.itemsList steps : Workspace)) =
        ConnesKreimer.of' ({(steps.foldl (fun c step ↦ step.run c) c).current} +
          ↑(steps.foldl (fun c step ↦ step.run c) c).stack : Workspace)
  | [], c, _ => by
    simp [Step.mergeOpList]
  | step :: steps, c, ⟨h, hs⟩ => by
    rw [Step.mergeOpList, LinearMap.comp_apply, Step.itemsList_cons, ← add_assoc,
      Step.mergeOp_run h, List.foldl_cons]
    exact Step.mergeOpList_run steps (step.run c) hs

/-- Admissible Merge steps leave the stack alone and build what they build on the object. -/
theorem Step.foldl_run_of_admissibleList :
    ∀ (steps : List Step) (current : SyntacticObject) (st : List SyntacticObject),
      Step.AdmissibleList steps current →
      steps.foldl (fun c step ↦ step.run c) ⟨current, st⟩
        = ⟨steps.foldl (fun so step ↦ step.apply so) current, st⟩
  | [], _, _, _ => rfl
  | step :: steps, current, st, ⟨h, hs⟩ => by
    rw [List.foldl_cons, List.foldl_cons, h.run_eq]
    exact Step.foldl_run_of_admissibleList steps _ st hs

/-- Admissible Merge steps compose to the algebraic Merge from the workspace of the current object
    and the items they introduce to the object they build. -/
theorem Step.mergeOpList_workspace (steps : List Step) (current : SyntacticObject)
    (h : Step.AdmissibleList steps current) :
    Step.mergeOpList steps ⟨current, []⟩ (ConnesKreimer.of' ({current} + Step.itemsList steps)) =
      ConnesKreimer.of' {steps.foldl (fun so step => step.apply so) current} := by
  simpa [Step.foldl_run_of_admissibleList steps current [] h] using
    Step.mergeOpList_run steps ⟨current, []⟩ (Step.AdmissibleList.admissibleListAt steps current h)

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
      ({current} + (Step.em side item).items + W : Workspace).merge ↑item current := by
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

/-- A derivation is admissible when each of its steps is a Merge step admissible beside the items
    still to come. -/
def Admissible (d : Derivation) : Prop := Step.AdmissibleList d.steps d.initial

/-- A derivation is admissible on its configurations when each of its steps, the stages of
    Internal Merge among them, is admissible at the configuration it is run at. -/
def AdmissibleAt (d : Derivation) : Prop := Step.AdmissibleListAt d.steps ⟨d.initial, []⟩

theorem Admissible.admissibleAt {d : Derivation} (hd : d.Admissible) : d.AdmissibleAt :=
  Step.AdmissibleList.admissibleListAt d.steps d.initial hd

/-- A derivation admissible on its configurations is the iterated algebraic Merge on the workspace
    of its initial object and its items: the composite of its steps' Merges sends that workspace
    to its final object beside the copies left on the stack. -/
theorem mergeOpList_run {d : Derivation} (hd : d.AdmissibleAt) :
    Step.mergeOpList d.steps ⟨d.initial, []⟩ (ConnesKreimer.of' ({d.initial} + d.items)) =
      ConnesKreimer.of' ({d.final} + ↑d.run.stack : Workspace) := by
  have h := Step.mergeOpList_run d.steps ⟨d.initial, []⟩ hd
  rw [Multiset.coe_nil, add_zero] at h
  exact h

/-- An admissible derivation is the iterated algebraic Merge on the workspace of its initial object
    and its items: the composite of its steps' Merges sends that workspace to its final object. -/
theorem mergeOpList_initial {d : Derivation} (hd : d.Admissible) :
    Step.mergeOpList d.steps ⟨d.initial, []⟩ (ConnesKreimer.of' ({d.initial} + d.items)) =
      ConnesKreimer.of' {d.final} :=
  (Step.mergeOpList_workspace d.steps d.initial hd).trans <| by
    rw [final, run, Step.foldl_run_of_admissibleList d.steps d.initial [] hd]

end Derivation

end Minimalist
