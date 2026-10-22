/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Computability.Edge
public import Linglib.Syntax.Minimalist.Merge.SyntacticObject

/-!
# Derivations

An ordered derivation is an initial syntactic object with a sequence of steps. External Merge adds
an item, and Internal Merge raises a mover, re-merging it with the current object in which its
occurrences are replaced by the trace of its head; Internal Merge also comes in two stages,
`extract` and `remerge`, through a stack of copies. An admissible derivation is the iterated
algebraic Merge on the workspace of its initial object and its items. The side on which a step
places its daughter is a linearization datum that only externalization reads.

## Main definitions

* `Minimalist.Step`, `Step.apply`, `Step.run`, `Step.mover?`, `Step.IsMerge`, `Step.mergeOp`,
  `Step.Admissible`
* `Minimalist.Derivation`, `Derivation.Cfg`, `Derivation.run`, `final`, `stageAt`, `movedItems`,
  `mover?`, `take`, `append`, `leftward`, `items`, `lexTokens`, `Admissible`
* `Minimalist.Derivation.Cfg.yield`: the tokens a configuration pronounces.

## Main results

* `Minimalist.Step.apply_em`: the sides build the same object.
* `Minimalist.Step.run_im`: Internal Merge is an extraction followed by merging back.
* `Minimalist.Step.mergeOp_workspace`: an admissible step is the algebraic Merge
  on the workspace.
* `Minimalist.Derivation.mergeOpList_initial`: an admissible derivation is the
  iterated algebraic Merge.
* `Minimalist.Derivation.stageAt_append_of_le`, `movedItems_append`: extension
  keeps the early stages and the movers.
* `Minimalist.Derivation.stageAt_leftward`, `movedItems_leftward`: the sides
  change no stage and no mover.

## Implementation notes

* Which item heads the mover is a theory's choice, so the steps and stages take the trace encoder
  as a parameter, by default the head by selection.
* `node` is noncomputable, so `Step.apply` and `Derivation.final` are too; the movers are read
  off the steps.

## TODO

* Extend `Step.Admissible` and `Step.mergeOp_workspace` to `extract` and `remerge`, the two stages
  of Internal Merge, on the workspace of the object, its stack and the items still to come.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.6) and §1.4 (Lemma 1.4.1,
  Proposition 1.4.2)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject


/-! ### Steps -/

/-- A derivation step. A Merge step attaches its new daughter on an `Edge` of the mother, a
linearization datum that externalization reads and the derived object ignores. `im` records only
the mover; the trace it leaves is that of its head under the trace encoder the step is applied
with. Internal Merge is also available in its two stages, `extract` and `remerge`
([marcolli-chomsky-berwick-2025] Proposition 1.4.2), so that several copies can wait on the stack
of the workspace. -/
inductive Step where
  /-- External Merge, the new item as the daughter on `side`. -/
  | em (side : Edge) (item : SyntacticObject)
  /-- Internal Merge raises `mover` to the daughter on `side`, the left unless stated otherwise,
  leaving the trace of its head in its place. -/
  | im (mover : SyntacticObject) (side : Edge := .left)
  /-- The unit stage of Internal Merge puts a copy of `mover` on top of the stack, leaving the
  trace of its head in its place. -/
  | extract (mover : SyntacticObject)
  /-- The copy on top of the stack merges back as the daughter on `side`. -/
  | remerge (side : Edge := .left)

/-- A configuration of a derivation is the object under construction and the stack of copies
extracted from it, the top first. -/
structure Derivation.Cfg (α : Type*) where
  /-- The object under construction. -/
  current : α
  /-- The extracted copies not yet merged back, the top first. -/
  stack : List α

namespace Derivation.Cfg

variable {α β : Type*}

/-- A map applied to the object and to every copy on the stack. -/
def map (f : α → β) (c : Cfg α) : Cfg β := ⟨f c.current, c.stack.map f⟩

@[simp] theorem map_current (f : α → β) (c : Cfg α) : (c.map f).current = f c.current := rfl

@[simp] theorem map_stack (f : α → β) (c : Cfg α) : (c.map f).stack = c.stack.map f := rfl

/-- The tokens a configuration pronounces, its object's and those of the copies on its stack. -/
def yield (c : Cfg SyntacticObject) : Multiset LexicalItem.Token :=
  c.current.yield + (c.stack.map SyntacticObject.yield).sum

@[simp] theorem yield_map (f : α → SyntacticObject) (c : Cfg α) :
    (c.map f).yield = (f c.current).yield + (c.stack.map fun x ↦ (f x).yield).sum := by
  simp [yield, map, Function.comp_def]

end Derivation.Cfg

/-- The object a step builds from the current one, the copies on the stack aside. External Merge
    adds the item on the given side, Internal Merge merges the remainder and the mover, leaving
    the trace of its head under `τ`, and an extraction leaves the remainder. `remerge` needs the
    stack (`Step.run`). -/
noncomputable def Step.apply (step : Step) (current : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  match step with
  | .em .left item => merge item current
  | .em .right item => merge current item
  | .im mover _ => merge (deleteAccessible mover current τ) mover
  | .extract mover => deleteAccessible mover current τ
  | .remerge _ => current

/-- A step on a configuration. An extraction pushes the mover's copy onto the stack, `remerge`
    merges the copy on top back by External Merge, and the other steps leave the stack alone. -/
noncomputable def Step.run (step : Step) (c : Derivation.Cfg SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Derivation.Cfg SyntacticObject :=
  match step, c.stack with
  | .extract mover, st => ⟨step.apply c.current τ, mover :: st⟩
  | .remerge side, m :: st => ⟨(Step.em side m).apply c.current τ, st⟩
  | _, st => ⟨step.apply c.current τ, st⟩

variable {τ : SyntacticObject → Option LexicalItem.Token}

theorem Step.apply_em_left (item current : SyntacticObject) :
    (Step.em .left item).apply current τ = merge item current := rfl

theorem Step.apply_em_right (item current : SyntacticObject) :
    (Step.em .right item).apply current τ = merge current item := rfl

theorem Step.apply_im (mover : SyntacticObject) (side : Edge) (current : SyntacticObject) :
    (Step.im mover side).apply current τ = merge (deleteAccessible mover current τ) mover := rfl

/-- The sides build the same object; they differ only at externalization. -/
theorem Step.apply_em (side : Edge) (item current : SyntacticObject) :
    (Step.em side item).apply current τ = merge item current := by
  cases side
  · rfl
  · exact merge_comm current item

/-- A step is a Merge, external or internal, rather than one of the two stages of Internal
Merge. -/
def Step.IsMerge : Step → Prop
  | .em _ _ | .im _ _ => True
  | .extract _ | .remerge _ => False

instance : DecidablePred Step.IsMerge :=
  fun s ↦ by cases s <;> unfold Step.IsMerge <;> infer_instance

/-- The mover of an Internal-Merge step or an extraction. -/
def Step.mover? : Step → Option SyntacticObject
  | .im mover _ | .extract mover => some mover
  | .em _ _ | .remerge _ => none

@[simp] theorem Step.mover?_em (side : Edge) (item : SyntacticObject) :
    (Step.em side item).mover? = none := rfl

@[simp] theorem Step.mover?_im (mover : SyntacticObject) (side : Edge) :
    (Step.im mover side).mover? = some mover :=
  rfl

/-- The step with its new daughter on the left. -/
def Step.leftward : Step → Step
  | .em _ item => .em .left item
  | .im mover _ => .im mover
  | .extract mover => .extract mover
  | .remerge _ => .remerge

@[simp] theorem Step.leftward_em (side : Edge) (item : SyntacticObject) :
    (Step.em side item).leftward = .em .left item := rfl

@[simp] theorem Step.leftward_im (mover : SyntacticObject) (side : Edge) :
    (Step.im mover side).leftward = .im mover :=
  rfl

@[simp] theorem Step.mover?_leftward (step : Step) : step.leftward.mover? = step.mover? := by
  cases step <;> rfl

/-- A step and its leftward form build the same object. -/
theorem Step.apply_leftward (step : Step) (current : SyntacticObject) :
    step.leftward.apply current τ = step.apply current τ := by
  cases step with
  | em side item => rw [Step.leftward_em, Step.apply_em, Step.apply_em]
  | _ => rfl

/-- A step and its leftward form reach the same configuration. -/
theorem Step.run_leftward (step : Step) (c : Derivation.Cfg SyntacticObject) :
    step.leftward.run c τ = step.run c τ := by
  obtain ⟨cur, _ | ⟨m, st⟩⟩ := c <;> cases step <;>
    first | rfl | simp only [Step.run, Step.leftward, Step.apply_em]

/-- Internal Merge is an extraction followed by merging the copy back
    ([marcolli-chomsky-berwick-2025] Proposition 1.4.2). -/
theorem Step.run_im (mover : SyntacticObject) (side : Edge) (c : Derivation.Cfg SyntacticObject) :
    (Step.im mover side).run c τ = (Step.remerge side).run ((Step.extract mover).run c τ) τ := by
  obtain ⟨cur, st⟩ := c
  show (⟨_, st⟩ : Derivation.Cfg SyntacticObject) = ⟨_, st⟩
  rw [Step.apply_em, Step.apply_im, merge_comm]
  rfl

/-! ### Derivations as workspace Merges

A step merges the current object with the items it introduces, beside a spectator workspace of the
items still to come. When it matches no accessible term of the spectators, and an Internal Merge
raises a uniquely accessible proper term, the step is the algebraic Merge on the workspace
(`Step.mergeOp_workspace`), and a derivation is the iterated algebraic Merge on the workspace of its
initial object and its items (`mergeOpList_initial`). The two stages of Internal Merge, `extract`
and `remerge`, act on the stack beside the object, which this workspace leaves out, so they are not
admissible here. -/

/-- The item an External Merge step introduces. -/
def Step.items : Step → Workspace
  | .em _ item => {item}
  | .im _ _ | .extract _ | .remerge _ => 0

/-- The items a list of steps introduces. -/
def Step.itemsList (steps : List Step) : Workspace :=
  (steps.map Step.items).sum

@[simp] theorem Step.itemsList_nil : Step.itemsList [] = 0 := rfl

@[simp] theorem Step.itemsList_cons (step : Step) (steps : List Step) :
    Step.itemsList (step :: steps) = step.items + Step.itemsList steps := by
  simp [Step.itemsList]

/-- A step applies an algebraic Merge at the current object, External Merge with the item or the
    unit stage followed by External Merge of the remainder with the mover. -/
noncomputable def Step.mergeOp (step : Step)
    (current : SyntacticObject) :
    ConnesKreimer ℤ (UnorderedTree Vertex) →ₗ[ℤ] ConnesKreimer ℤ (UnorderedTree Vertex) :=
  match step with
  | .em _ item => Merge.mergeOpC traceEncoder Vertex.bare current.val item.val
  | .im mover _ => Merge.mergeOpC traceEncoder Vertex.bare (deleteAccessible mover current).val
      mover.val ∘ₗ Merge.mergeOpUnitC traceEncoder mover.val
  | .extract mover => Merge.mergeOpUnitC traceEncoder mover.val
  | .remerge _ => 0

/-- A step at the current object is admissible beside a spectator workspace `W` when it matches
    no accessible term of `W`, and an Internal Merge raises a uniquely accessible proper term that
    is not a trace. -/
def Step.Admissible (current : SyntacticObject)
    (W : Workspace) : Step → Prop
  | .em _ item => ∀ U ∈ W, current ∉ U.terms ∧ item ∉ U.terms
  | .im mover _ => mover.val.value.isLeft ∧ current.terms.count mover = 1 ∧ current ≠ mover ∧
      ∀ U ∈ W, deleteAccessible mover current ∉ U.terms ∧ mover ∉ U.terms
  | .extract _ | .remerge _ => False

/-- An admissible step is the algebraic Merge on the workspace of the current object, the items
    it introduces, and the spectators. -/
theorem Step.mergeOp_workspace {step : Step}
    {current : SyntacticObject} {W : Workspace} (h : step.Admissible current W) :
    step.mergeOp current (ConnesKreimer.of' (({current} + step.items + W).map Subtype.val))
      = ConnesKreimer.of' (({step.apply current} + W).map Subtype.val) := by
  cases step with
  | em side item =>
    rw [Step.apply_em, merge_comm]
    exact mergeOpC_node_residual traceEncoder current item h
  | im mover _ =>
    obtain ⟨hm, hc, hne, hW⟩ := h
    exact mergeOpC_im_residual hm hc hne hW
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
          (ConnesKreimer.of' (({current} + Step.itemsList steps).map Subtype.val))
        = ConnesKreimer.of' {(steps.foldl (fun so step => step.apply so) current).val}
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

/-! ### Derivations -/

/-- An initial syntactic object with a sequence of steps. -/
structure Derivation where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SyntacticObject
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List Step

namespace Derivation

/-- The configuration after every step, under the trace encoder `τ`. -/
noncomputable def run (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Cfg SyntacticObject :=
  d.steps.foldl (fun c step ↦ step.run c τ) ⟨d.initial, []⟩

/-- The object after every step, under the trace encoder `τ`. -/
noncomputable def final (d : Derivation)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  (d.run τ).current

/-- The number of derivation steps. -/
def length (d : Derivation) : Nat := d.steps.length

/-- The movers of the `im` and `extract` steps. -/
def movedItems (d : Derivation) : List SyntacticObject := d.steps.filterMap Step.mover?

/-- The mover of step `i`, when that step is an Internal Merge or an extraction. -/
def mover? (d : Derivation) (i : ℕ) : Option SyntacticObject := d.steps[i]? >>= Step.mover?

/-- The first `n` steps. -/
def take (d : Derivation) (n : Nat) : Derivation := ⟨d.initial, d.steps.take n⟩

/-- The derivation continued by `steps`. -/
def append (d : Derivation) (steps : List Step) : Derivation := ⟨d.initial, d.steps ++ steps⟩

/-- The object after the first `n` steps, under the trace encoder `τ`. -/
noncomputable def stageAt (d : Derivation) (n : Nat)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  (d.take n).final τ

@[simp] theorem stageAt_zero (d : Derivation) : d.stageAt 0 τ = d.initial := by
  simp [stageAt, final, run, take]

theorem stageAt_length (d : Derivation) : d.stageAt d.steps.length τ = d.final τ := by
  simp [stageAt, take, List.take_length]

@[simp] theorem final_take (d : Derivation) (n : Nat) : (d.take n).final τ = d.stageAt n τ := rfl

/-! ### Extension

The early stages and the movers of an extended derivation are the original's. -/

@[simp] theorem length_append (d : Derivation) (steps : List Step) :
    (d.append steps).length = d.length + steps.length := by
  simp [length, append]

@[simp] theorem append_assoc (d : Derivation) (steps steps' : List Step) :
    (d.append steps).append steps' = d.append (steps ++ steps') := by
  simp [append]

/-- The first `n ≤ d.length` steps of an extension are `d`'s. -/
theorem take_append_of_le {d : Derivation} {n : Nat} (h : n ≤ d.length) (steps : List Step) :
    (d.append steps).take n = d.take n := by
  simp [take, append, List.take_append_of_le_length h]

@[simp] theorem take_length (d : Derivation) : d.take d.length = d := by
  simp [take, length]

@[simp] theorem take_length_append (d : Derivation) (steps : List Step) :
    (d.append steps).take d.length = d := by
  unfold take append
  rw [length, List.take_left]

theorem stageAt_append_of_le {d : Derivation} {n : Nat} (h : n ≤ d.length) (steps : List Step) :
    (d.append steps).stageAt n τ = d.stageAt n τ := by
  rw [← final_take, ← final_take, take_append_of_le h]

theorem run_append (d : Derivation) (steps : List Step) :
    (d.append steps).run τ = steps.foldl (fun c step ↦ step.run c τ) (d.run τ) := by
  simp [run, append, List.foldl_append]

@[simp] theorem movedItems_append (d : Derivation) (steps : List Step) :
    (d.append steps).movedItems = d.movedItems ++ steps.filterMap Step.mover? := by
  simp [movedItems, append, List.filterMap_append]

/-- A step at index `i` has a mover only if `i` indexes a step. -/
theorem lt_length_of_mem_mover? {d : Derivation} {i : Nat} {m : SyntacticObject}
    (h : m ∈ d.mover? i) : i < d.length := by
  by_contra hlt
  rw [mover?, List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at h
  simp at h

/-- The mover of a step is one of the derivation's movers. -/
theorem mem_movedItems_of_mem_mover? {d : Derivation} {i : Nat} {m : SyntacticObject}
    (h : m ∈ d.mover? i) : m ∈ d.movedItems := by
  obtain ⟨step, hs, hm⟩ := Option.bind_eq_some_iff.1 h
  exact List.mem_filterMap.2 ⟨step, List.mem_of_getElem? hs, hm⟩

/-- The early steps of an extension have the original's movers. -/
theorem mover?_append_of_lt {d : Derivation} {i : Nat} (h : i < d.length) (steps : List Step) :
    (d.append steps).mover? i = d.mover? i := by
  simp only [mover?, append, List.getElem?_append_left h]

/-! ### The sides of Merge

The node being commutative, the derived object does not depend on the sides at which the steps
attach their daughters; `leftward` is the normal form, and the stages and movers of a derivation
are those of its normal form. -/

/-- The derivation with every new daughter on the left. -/
def leftward (d : Derivation) : Derivation := ⟨d.initial, d.steps.map Step.leftward⟩

@[simp] theorem run_leftward (d : Derivation) : d.leftward.run τ = d.run τ := by
  simp only [run, leftward, List.foldl_map, Step.run_leftward]

@[simp] theorem final_leftward (d : Derivation) : d.leftward.final τ = d.final τ := by
  rw [final, final, run_leftward]

@[simp] theorem stageAt_leftward (d : Derivation) (n : Nat) :
    d.leftward.stageAt n τ = d.stageAt n τ := by
  rw [stageAt, stageAt, ← final_leftward (d := d.take n)]
  simp only [take, leftward, List.map_take]

@[simp] theorem movedItems_leftward (d : Derivation) : d.leftward.movedItems = d.movedItems := by
  simp [movedItems, leftward, List.filterMap_map]

/-- The items a derivation introduces by External Merge. -/
def items (d : Derivation) : Workspace := Step.itemsList d.steps

/-- The tokens a derivation merges: those of its initial object and of every item it merges
externally. -/
def lexTokens (d : Derivation) : Multiset LexicalItem.Token :=
  d.initial.yield + (d.items.map SyntacticObject.yield).sum

theorem lexTokens_append (d : Derivation) (steps : List Step) :
    (d.append steps).lexTokens =
      d.lexTokens + ((Step.itemsList steps).map SyntacticObject.yield).sum := by
  simp [lexTokens, items, append, Step.itemsList, List.map_append, List.sum_append, add_assoc]

/-- A derivation is admissible when each of its steps is, beside the items still to come. -/
def Admissible (d : Derivation) : Prop := Step.AdmissibleList d.steps d.initial

/-- An admissible derivation is the iterated algebraic Merge on the workspace of its initial object
    and its items: the composite of its steps' Merges sends that workspace to its final object. -/
theorem mergeOpList_initial {d : Derivation} (hd : d.Admissible) :
    Step.mergeOpList d.steps d.initial (ConnesKreimer.of' (({d.initial} + d.items).map Subtype.val))
      = ConnesKreimer.of' {d.final.val} :=
  (Step.mergeOpList_workspace d.steps d.initial hd).trans <| by
    rw [final, run, Step.foldl_run_of_admissibleList d.steps d.initial [] hd]

end Derivation

/-! ### Carrier tests -/

private def demoTok (i : Nat) : SyntacticObject := SyntacticObject.leaf ⟨.of .N [], i⟩

example :
    (Derivation.mk (demoTok 0)
      [Step.em .left (demoTok 1), Step.im (demoTok 1), Step.em .right (demoTok 2),
        Step.im (demoTok 2) .right]).movedItems = [demoTok 1, demoTok 2] := by
  simp [Derivation.movedItems, demoTok]

example : (Derivation.mk (demoTok 0) [Step.em .left (demoTok 1)]).length = 1 := rfl

/-- Extension keeps the movers and adds the new ones. -/
example :
    ((Derivation.mk (demoTok 0) [Step.em .left (demoTok 1)]).append
      [Step.im (demoTok 1)]).movedItems = [demoTok 1] := by
  simp [Derivation.movedItems, Derivation.append, demoTok]

/-- Raising the item a derivation has just merged is admissible, so `mergeOpList_initial` applies
    to it. -/
example :
    (Derivation.mk (demoTok 0) [Step.em .left (demoTok 1), Step.im (demoTok 1)]).Admissible := by
  have hne : merge (demoTok 1) (demoTok 0) ≠ demoTok 1 := fun h ↦ by
    have := congrArg (fun s : SyntacticObject ↦ s.val.numNodes) h
    simp [demoTok] at this
  simp only [Derivation.Admissible, Step.AdmissibleList, Step.Admissible, Step.itemsList_cons,
    Step.itemsList_nil, Step.items, Step.apply_em_left, add_zero, Multiset.notMem_zero,
    IsEmpty.forall_iff, implies_true, and_true, true_and, ne_eq, hne, not_false_eq_true]
  refine ⟨rfl, ?_⟩
  rw [terms_merge, Multiset.count_cons_of_ne hne.symm]
  simp [demoTok]

end Minimalist
