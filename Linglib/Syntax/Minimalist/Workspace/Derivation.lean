/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Syntax.Minimalist.Workspace.NoComplexityLoss
public import Linglib.Syntax.Minimalist.Workspace.MinimalYield

/-!
# Economy of derivations

An admissible derivation step relates the workspace of the current object, its items and the
items still to come to the workspace of the object it builds and those items. When its operands
are not traces, that transformation satisfies No Complexity Loss graded by the size `σ` and
Minimal Yield under trace counting (§1.6 of Marcolli, Chomsky and Berwick). An External Merge step
is the term of Merge taking both objects whole and leaving the spectators uncut, so its component
map loses no complexity. Along an admissible derivation the workspaces of its stages therefore
form a chain of economical transformations.

## Main definitions

* `Minimalist.Derivation.workspaces`: the workspaces of a derivation's stages.

## Main results

* `Minimalist.Step.noComplexityLoss`, `Step.minimalYield`: an admissible step whose operands are
  not traces is economical.
* `Minimalist.Derivation.isChain_noComplexityLoss`, `isChain_minimalYield`: so is
  every step of an admissible derivation.
* `Minimalist.Derivation.isChain_merge`: every step of an admissible derivation is MERGE, an
  Internal Merge step leaving the trace of the mover's head.

## References

* [marcolli-chomsky-berwick-2025]
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

theorem Step.value_isLeft_apply {step : Step} {current : SyntacticObject} {W : Workspace}
    (h : step.Admissible current W) : (step.apply current).val.value.isLeft := by
  cases step with
  | em side item => cases side <;> simp [Step.apply]
  | im mover _ => simp [Step.apply]
  | extract _ | remerge _ => exact h.elim

private theorem numTraces_lt_numNodes {S : SyntacticObject} (h : S.val.value.isLeft) :
    S.val.numTraces < S.val.numNodes := by
  obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp h
  exact UnorderedTree.numTraces_lt_numNodes_of_rootInl _ a ha

/-! ### External Merge as a term of Merge

External Merge of `S` and `S'` beside spectators `W` is the term of Merge taking `S` and `S'`
whole and leaving every spectator uncut. -/

section ExternalMerge

variable (S S' : UnorderedTree Vertex) (W : Multiset (UnorderedTree Vertex))

/-- The term of Merge taking `S` and `S'` whole and leaving the spectators uncut. -/
private def emTerm : CutChoice Vertex :=
  ({S, S'} : Multiset (UnorderedTree Vertex)).map (fun T ↦ (T, ({T}, 0))) +
    W.map fun T ↦ (T, (0, {T}))

private theorem emTerm_mem :
    emTerm S S' W ∈ forestCutChoicesG (cutSummandsCN traceEncoder) ({S, S'} + W) :=
  add_mem_forestCutChoicesG (map_whole_mem_forestCutChoicesG _)
    (map_uncut_mem_forestCutChoicesG fun T _ ↦ zero_mem_cutSummandsCN _ T)

private theorem emTerm_crown : (emTerm S S' W).crown = {S, S'} := by simp [emTerm]

private theorem emTerm_trunk : (emTerm S S' W).trunk = W := by simp [emTerm]

private theorem emTerm_whole_or_uncut : ∀ x ∈ emTerm S S' W, x.2.1 = 0 ∨ x.2.2 = 0 := by
  simp only [emTerm, Multiset.mem_add, Multiset.mem_map]
  rintro x (⟨T, -, rfl⟩ | ⟨T, -, rfl⟩)
  exacts [.inr rfl, .inl rfl]

variable {S S'} in
private theorem emTerm_lexical (hS : S.value.isLeft) (hS' : S'.value.isLeft) :
    ∀ x ∈ emTerm S S' W, x.2.1 ≠ 0 → ∃ a, x.1.value = Sum.inl a := by
  simp only [emTerm, Multiset.mem_add, Multiset.mem_map]
  rintro x (⟨T, hT, rfl⟩ | ⟨T, -, rfl⟩) h
  · rcases Multiset.mem_cons.mp hT with rfl | hT
    · exact Sum.isLeft_iff.mp hS
    · exact Multiset.mem_singleton.mp hT ▸ Sum.isLeft_iff.mp hS'
  · exact absurd rfl h

end ExternalMerge

variable {step : Step} {current : SyntacticObject} {W : Workspace}

/-- The trace cut extracting the mover of an admissible Internal Merge. -/
private theorem mem_cutSummandsCN_mover {mover : SyntacticObject} (hm : mover.val.value.isLeft)
    (h : current.terms.count mover = 1) (hne : current ≠ mover) :
    ({mover.val}, (deleteAccessible mover current).val) ∈ cutSummandsCN traceEncoder current.val :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1 = {mover.val}) <| by
    rw [cutSummandsCN_filter_mover hm h hne]
    exact Multiset.mem_singleton_self _

/-- An admissible step whose operands are not traces satisfies No Complexity Loss under the size `σ`
(the book's (1.6.10)). -/
theorem Step.noComplexityLoss (h : step.Admissible current W) (hcur : current.val.value.isLeft)
    (hitems : ∀ i ∈ step.items, i.val.value.isLeft) :
    NoComplexityLoss (fun T ↦ Forest.accessibleSize {T})
      (({current} + step.items + W).map Subtype.val)
      (({step.apply current} + W).map Subtype.val) := by
  cases step with
  | em side item =>
    simp only [Step.items, Multiset.mem_singleton, forall_eq] at hitems
    have hs := emTerm_mem current.val (item : SyntacticObject).val (W.map Subtype.val)
    have hm := UnorderedTree.accessibleCount_merge none current.val (item : SyntacticObject).val
      (numTraces_lt_numNodes hcur) (numTraces_lt_numNodes hitems)
    have := NoComplexityLoss.of_componentMap hs
      (X := UnorderedTree.node Vertex.bare {current.val, (item : SyntacticObject).val})
      ((NoComplexityLoss.map_componentMap_merge_iff hs
        (hasExtractionCost_accessibleSize_cutSummandsCN hs (emTerm_lexical _ hcur hitems))
        (fun T ↦ by simp) (emTerm_crown ..)
        (by simp only [Forest.accessibleSize_singleton, hm]; omega)
        (by simp only [Forest.accessibleSize_singleton, hm]; omega)).mpr
        (emTerm_whole_or_uncut _ _ _))
    rw [emTerm_trunk] at this
    rw [Step.apply_em, merge_comm]
    simp only [Step.items, Multiset.map_add, Multiset.map_singleton, merge_val]
    rwa [Multiset.singleton_add]
  | im mover _ =>
    obtain ⟨hm, hc, hne, -⟩ := h
    have hp := mem_cutSummandsCN_mover hm hc hne
    have hσ := cutSummandsCN_accessibleSize traceEncoder (Sum.isLeft_iff.mp hcur).choose_spec hp
    have hmerge := UnorderedTree.accessibleCount_merge none (deleteAccessible mover current).val
      mover.val (numTraces_lt_numNodes (by
        rw [cutSummandsCN_trunk_value traceEncoder _ _ hp]; exact hcur))
      (numTraces_lt_numNodes hm)
    simp only [Multiset.map_singleton, Multiset.sum_singleton,
      Forest.accessibleSize_singleton] at hσ
    refine ⟨{(current.val, (merge (deleteAccessible mover current) mover).val)} +
      (W.map Subtype.val).map fun U ↦ (U, U), ?_, ?_, ?_⟩
    · simp [Step.items, Multiset.map_map]
    · simp only [Step.apply_im, Multiset.map_add, Multiset.map_singleton, Multiset.mem_add,
        Multiset.mem_singleton, Multiset.mem_map]
      rintro x (rfl | ⟨U, hU, rfl⟩)
      exacts [.inl rfl, .inr hU]
    · simp only [NoComplexityLoss.Map, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_map]
      rintro x (rfl | ⟨U, -, rfl⟩)
      · simp only [merge_val, Forest.accessibleSize_singleton, hmerge]
        omega
      · exact le_rfl
  | extract _ | remerge _ => exact h.elim

/-- An admissible step whose operands are not traces satisfies Minimal Yield under trace
    counting. -/
theorem Step.minimalYield (h : step.Admissible current W) (hcur : current.val.value.isLeft)
    (hitems : ∀ i ∈ step.items, i.val.value.isLeft) :
    MinimalYield UnorderedTree.accessibleCount (({current} + step.items + W).map Subtype.val)
      (({step.apply current} + W).map Subtype.val) := by
  cases step with
  | em side item =>
    rw [Step.apply_em, merge_comm]
    simp only [Step.items, Multiset.mem_singleton, forall_eq] at hitems
    simp only [Step.items, Multiset.map_add, Multiset.map_singleton, merge_val]
    exact (MinimalYield.em_pair_accessibleCount none (numTraces_lt_numNodes hcur)
      (numTraces_lt_numNodes hitems)).add_right _
  | im mover _ =>
    obtain ⟨hm, hc, hne, -⟩ := h
    have hp := mem_cutSummandsCN_mover hm hc hne
    obtain ⟨l, r, rfl⟩ := exists_eq_merge_of_count_terms hc hne
    simp only [Step.items, add_zero, Step.apply_im, Multiset.map_add, Multiset.map_singleton,
      merge_val, Multiset.pair_comm (deleteAccessible mover (merge l r)).val] at hp ⊢
    exact (MinimalYield.im_accessibleCount_of_cut none none traceEncoder _ _ hp mover.val
      rfl).add_right _
  | extract _ | remerge _ => exact h.elim

/-- The workspaces after each of a list of steps hold the object built so far beside the items
    still to come. -/
noncomputable def Step.workspacesAfter : List Step → SyntacticObject → List Workspace
  | [], _ => []
  | step :: steps, current =>
      ({step.apply current} + Step.itemsList steps) ::
        Step.workspacesAfter steps (step.apply current)

private theorem isChain_of_step {R : Workspace → Workspace → Prop} {P : SyntacticObject → Prop}
    (hR : ∀ {step : Step} {current : SyntacticObject} {W : Workspace}, step.Admissible current W →
      P current → (∀ i ∈ step.items, P i) →
        R ({current} + step.items + W) ({step.apply current} + W))
    (hP : ∀ {step : Step} {current : SyntacticObject} {W : Workspace},
      step.Admissible current W → P (step.apply current)) :
    ∀ (steps : List Step) (current : SyntacticObject), Step.AdmissibleList steps current →
      P current → (∀ i ∈ Step.itemsList steps, P i) →
      List.IsChain R (({current} + Step.itemsList steps) :: Step.workspacesAfter steps current)
  | [], _, _, _, _ => .singleton _
  | step :: steps, current, ⟨h, hs⟩, hcur, hitems => by
    rw [Step.itemsList_cons] at hitems ⊢
    refine .cons_cons ?_ (isChain_of_step hR hP steps _ hs (hP h)
      fun i hi ↦ hitems i (Multiset.mem_add.mpr (.inr hi)))
    rw [← add_assoc]
    exact hR h hcur fun i hi ↦ hitems i (Multiset.mem_add.mpr (.inl hi))

namespace Derivation

/-- The workspaces of a derivation's stages hold the initial object beside its items, then after
    each step the object built so far beside the items still to come. -/
noncomputable def workspaces (d : Derivation) : List Workspace :=
  ({d.initial} + d.items) :: Step.workspacesAfter d.steps d.initial

/-- Each step of an admissible derivation is MERGE on the workspaces of its stages: an External
    Merge step leaving copies, and an Internal Merge step leaving the trace of the mover's head. -/
theorem isChain_merge {d : Derivation} (hd : d.Admissible) :
    d.workspaces.IsChain fun W W' : Workspace ↦ ∃ P Q : SyntacticObject,
      W' = W.merge P Q ∨ W' = W.mergeWith (·.headTrace) P Q := by
  refine isChain_of_step (P := fun _ ↦ True) (fun {step current W} h _ _ ↦ ?_) (fun _ ↦ trivial)
    d.steps d.initial hd trivial fun _ _ ↦ trivial
  cases step with
  | em side item => exact ⟨↑item, current, .inl (Step.apply_em_eq_merge side item current W)⟩
  | im mover side =>
    obtain ⟨-, hc, hne, hW⟩ := h
    refine ⟨mover, current, .inr ?_⟩
    rw [Step.items, add_zero]
    exact Step.apply_im_eq_mergeWith side (Multiset.count_pos.1 (by omega)) hne
      fun U hU ↦ (hW U hU).2
  | extract _ | remerge _ => exact h.elim

/-- Every step of an admissible derivation whose initial object and items are not traces satisfies
    No Complexity Loss, graded by the size `σ`. -/
theorem isChain_noComplexityLoss {d : Derivation} (hd : d.Admissible)
    (hinit : d.initial.val.value.isLeft) (hitems : ∀ i ∈ d.items, i.val.value.isLeft) :
    d.workspaces.IsChain (fun W W' : Workspace ↦ NoComplexityLoss
      (fun T ↦ Forest.accessibleSize {T}) (W.map Subtype.val) (W'.map Subtype.val)) :=
  isChain_of_step (P := fun S ↦ S.val.value.isLeft)
    (fun h hcur hi ↦ Step.noComplexityLoss h hcur hi) Step.value_isLeft_apply d.steps d.initial hd
    hinit hitems

/-- Every step of an admissible derivation whose initial object and items are not traces satisfies
    Minimal Yield under trace counting. -/
theorem isChain_minimalYield {d : Derivation} (hd : d.Admissible)
    (hinit : d.initial.val.value.isLeft) (hitems : ∀ i ∈ d.items, i.val.value.isLeft) :
    d.workspaces.IsChain (fun W W' : Workspace ↦
      MinimalYield UnorderedTree.accessibleCount (W.map Subtype.val) (W'.map Subtype.val)) :=
  isChain_of_step (P := fun S ↦ S.val.value.isLeft) (fun h hcur hi ↦ Step.minimalYield h hcur hi)
    Step.value_isLeft_apply d.steps d.initial hd hinit hitems

end Derivation

end Minimalist
