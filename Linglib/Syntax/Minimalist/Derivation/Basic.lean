/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Computability.Edge
public import Linglib.Syntax.Minimalist.Workspace.Basic

/-!
# Derivations

An ordered derivation is an initial syntactic object with a sequence of steps. External Merge adds
an item built in its own workspace, and Internal Merge raises a mover, re-merging it with the
current object in which its occurrences are replaced by the trace of its head; [it is also an
extraction followed by merging the copy back](##Minimalist.Step.run_im), the two stages `extract`
and `remerge` passing through a stack of copies. [A Merge step is MERGE on the
workspace](##Minimalist.Step.apply_im_eq_mergeWith), and that an admissible derivation is the
iterated algebraic Merge is proved in `Workspace/Derivation.lean`. The side on which a step places
its daughter, and the order of an item's daughters, are linearization data that [the derived object
ignores](##Minimalist.Step.apply_em) and only the replay reads.

## Implementation notes

* Which item heads the mover is a theory's choice, so the steps and stages take the trace encoder
  as a parameter, by default the head by selection.

## References

* [marcolli-chomsky-berwick-2025], §1.4 (Proposition 1.4.2)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject


/-! ### Steps -/

/-- A derivation step. A Merge step attaches its new daughter on an `Edge` of the mother, and an
External Merge step merges its item as built in its own workspace, with the order of its daughters:
linearization data that externalization reads and the derived object ignores. `im` records only
the mover; the trace it leaves is that of its head under the trace encoder the step is applied
with. Internal Merge is also available in its two stages, `extract` and `remerge`
([marcolli-chomsky-berwick-2025] Proposition 1.4.2), so that several copies can wait on the stack
of the workspace. -/
inductive Step where
  /-- External Merge, the new item as the daughter on `side`. -/
  | em (side : Edge) (item : LinearizedSyntacticObject)
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
    adds the item, Internal Merge merges the remainder and the mover, leaving the trace of its head
    under `τ`, and an extraction leaves the remainder. `remerge` needs the stack (`Step.run`). -/
def Step.apply (step : Step) (current : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  match step with
  | .em _ item => merge item current
  | .im mover _ => merge (deleteAccessible mover current τ) mover
  | .extract mover => deleteAccessible mover current τ
  | .remerge _ => current

/-- A step on a configuration. An extraction pushes the mover's copy onto the stack, `remerge`
    merges the copy on top back by External Merge, and the other steps leave the stack alone. -/
def Step.run (step : Step) (c : Derivation.Cfg SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Derivation.Cfg SyntacticObject :=
  match step, c.stack with
  | .extract mover, st => ⟨step.apply c.current τ, mover :: st⟩
  | .remerge _, m :: st => ⟨merge m c.current, st⟩
  | _, st => ⟨step.apply c.current τ, st⟩

variable {τ : SyntacticObject → Option LexicalItem.Token}

theorem Step.apply_em_right (item : LinearizedSyntacticObject) (current : SyntacticObject) :
    (Step.em .right item).apply current τ = merge current item := merge_comm _ _

theorem Step.apply_im (mover : SyntacticObject) (side : Edge) (current : SyntacticObject) :
    (Step.im mover side).apply current τ = merge (deleteAccessible mover current τ) mover := rfl

/-- The sides build the same object; they differ only at externalization. -/
theorem Step.apply_em (side : Edge) (item : LinearizedSyntacticObject) (current : SyntacticObject) :
    (Step.em side item).apply current τ = merge item current := rfl

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

@[simp] theorem Step.mover?_em (side : Edge) (item : LinearizedSyntacticObject) :
    (Step.em side item).mover? = none := rfl

@[simp] theorem Step.mover?_im (mover : SyntacticObject) (side : Edge) :
    (Step.im mover side).mover? = some mover :=
  rfl

/-- A step with mover `m` builds an object whose terms are among those of the remainder merged
with `m`: an Internal Merge builds exactly that, and an extraction the remainder alone. -/
theorem Step.terms_current_run_subset {step : Step} {m : SyntacticObject} (h : m ∈ step.mover?)
    (c : Derivation.Cfg SyntacticObject) :
    (step.run c τ).current.terms ⊆ (merge (deleteAccessible m c.current τ) m).terms := by
  cases step with
  | em _ _ | remerge _ => cases h
  | im mover side => obtain rfl := Option.some.inj h; exact fun _ hu ↦ hu
  | extract mover =>
    obtain rfl := Option.some.inj h
    exact fun u hu ↦ by
      rw [terms_merge]; exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl hu))

/-- A step with mover `m` leaves a configuration that pronounces the remainder and `m`, in its
object or on its stack. -/
theorem Step.yield_add_yield_le_yield_run {step : Step} {m : SyntacticObject}
    (h : m ∈ step.mover?) (c : Derivation.Cfg SyntacticObject) :
    (deleteAccessible m c.current τ).yield + m.yield ≤ (step.run c τ).yield := by
  obtain ⟨cur, st⟩ := c
  cases step with
  | em _ _ | remerge _ => cases h
  | im mover side =>
    obtain rfl := Option.some.inj h
    exact (Multiset.le_add_right _ (st.map yield).sum).trans_eq <| by
      simp [Derivation.Cfg.yield, Step.run, Step.apply]
  | extract mover =>
    obtain rfl := Option.some.inj h
    exact (Multiset.le_add_right _ (st.map yield).sum).trans_eq <| by
      simp [Derivation.Cfg.yield, Step.run, Step.apply, add_assoc]

/-- The step with its new daughter on the left. -/
def Step.leftward : Step → Step
  | .em _ item => .em .left item
  | .im mover _ => .im mover
  | .extract mover => .extract mover
  | .remerge _ => .remerge

@[simp] theorem Step.leftward_em (side : Edge) (item : LinearizedSyntacticObject) :
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
  obtain ⟨cur, _ | ⟨m, st⟩⟩ := c <;> cases step <;> rfl

/-- Internal Merge is an extraction followed by merging the copy back
    ([marcolli-chomsky-berwick-2025] Proposition 1.4.2). -/
theorem Step.run_im (mover : SyntacticObject) (side : Edge) (c : Derivation.Cfg SyntacticObject) :
    (Step.im mover side).run c τ = (Step.remerge side).run ((Step.extract mover).run c τ) τ := by
  obtain ⟨cur, st⟩ := c
  show (⟨_, st⟩ : Derivation.Cfg SyntacticObject) = ⟨_, st⟩
  rw [Step.apply_im, merge_comm]
  rfl

/-! ### Items -/

/-- The item an External Merge step introduces. -/
def Step.items : Step → Workspace
  | .em _ item => {↑item}
  | .im _ _ | .extract _ | .remerge _ => 0

/-- The items a list of steps introduces. -/
def Step.itemsList (steps : List Step) : Workspace :=
  (steps.map Step.items).sum

@[simp] theorem Step.itemsList_nil : Step.itemsList [] = 0 := rfl

@[simp] theorem Step.itemsList_cons (step : Step) (steps : List Step) :
    Step.itemsList (step :: steps) = step.items + Step.itemsList steps := by
  simp [Step.itemsList]

/-! ### Steps as MERGE

A Merge step is MERGE on the workspace of the current object, the items it introduces and the
spectators: External Merge leaving copies (`Workspace.merge`), and Internal Merge leaving the trace
of the mover's head (`Workspace.mergeWith`). Of the two stages of Internal Merge, `extract`
contracts and puts the mover's copy on the stack, and `remerge` is MERGE of that copy and the
current object on the workspace that holds the stack. -/

/-- External Merge is MERGE of the item and the current object. -/
theorem Step.apply_em_eq_merge (side : Edge) (item : LinearizedSyntacticObject)
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

/-! ### Derivations -/

/-- An initial syntactic object with a sequence of steps. -/
structure Derivation where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SyntacticObject
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List Step

namespace Derivation

/-- The configuration after every step, under the trace encoder `τ`. -/
def run (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Cfg SyntacticObject :=
  d.steps.foldl (fun c step ↦ step.run c τ) ⟨d.initial, []⟩

/-- The object after every step, under the trace encoder `τ`. -/
def final (d : Derivation)
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
def stageAt (d : Derivation) (n : Nat)
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

@[simp] theorem take_append_drop (d : Derivation) (n : Nat) :
    (d.take n).append (d.steps.drop n) = d := by
  simp [take, append]

/-- The first `i + 1` steps are the first `i` and step `i`. -/
theorem take_succ {d : Derivation} {i : Nat} {step : Step} (h : d.steps[i]? = some step) :
    d.take (i + 1) = (d.take i).append [step] := by
  simp [take, append, List.take_add_one, h]

theorem run_append (d : Derivation) (steps : List Step) :
    (d.append steps).run τ = steps.foldl (fun c step ↦ step.run c τ) (d.run τ) := by
  simp [run, append, List.foldl_append]

/-- The configuration after `i + 1` steps is step `i` run on the configuration after `i`. -/
theorem run_take_succ {d : Derivation} {i : Nat} {step : Step} (h : d.steps[i]? = some step) :
    (d.take (i + 1)).run τ = step.run ((d.take i).run τ) τ := by
  rw [take_succ h, run_append]; rfl

theorem stageAt_append_of_le {d : Derivation} {n : Nat} (h : n ≤ d.length) (steps : List Step) :
    (d.append steps).stageAt n τ = d.stageAt n τ := by
  rw [← final_take, ← final_take, take_append_of_le h]

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

/-- An initial segment merges no token the derivation does not. -/
theorem lexTokens_take_le (d : Derivation) (n : Nat) : (d.take n).lexTokens ≤ d.lexTokens := by
  conv_rhs => rw [← d.take_append_drop n, lexTokens_append]
  exact Multiset.le_add_right _ _

end Derivation

/-! ### Relabelling -/

section Map

variable (f : LexicalItem.Token → LexicalItem.Token)

/-- The step with its tokens relabelled by `f`. -/
def Step.map : Step → Step
  | .em side item => .em side (item.map f)
  | .im mover side => .im (mover.map f) side
  | .extract mover => .extract (mover.map f)
  | .remerge side => .remerge side

@[simp] theorem Step.mover?_map (step : Step) :
    (step.map f).mover? = step.mover?.map (SyntacticObject.map f) := by
  cases step <;> rfl

namespace Derivation

/-- The derivation with its tokens relabelled by `f`. -/
def map (d : Derivation) : Derivation := ⟨d.initial.map f, d.steps.map (Step.map f)⟩

variable (d : Derivation)

@[simp] theorem length_map : (d.map f).length = d.length := List.length_map _

@[simp] theorem take_map (n : Nat) : (d.map f).take n = (d.take n).map f := by
  simp [map, take, List.map_take]

@[simp] theorem append_map (steps : List Step) :
    (d.append steps).map f = (d.map f).append (steps.map (Step.map f)) := by
  simp [map, append]

variable {f} {τ' : SyntacticObject → Option LexicalItem.Token}

theorem _root_.Minimalist.Step.run_map (hf : Function.Injective f)
    (hτ : ∀ s, τ' (s.map f) = (τ s).map f) (step : Step) (c : Cfg SyntacticObject) :
    (step.map f).run (c.map (SyntacticObject.map f)) τ' =
      (step.run c τ).map (SyntacticObject.map f) := by
  rcases c with ⟨cur, _ | ⟨m, st⟩⟩ <;> cases step <;>
    simp [Step.map, Step.run, Step.apply, Cfg.map, deleteAccessible, replace_map hf,
      headTrace_map hτ]

/-- A relabelled derivation reaches the relabelled configuration, under an injective relabelling
the trace encoder commutes with. -/
theorem run_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f) :
    (d.map f).run τ' = (d.run τ).map (SyntacticObject.map f) := by
  have key : ∀ (steps : List Step) (c : Cfg SyntacticObject),
      (steps.map (Step.map f)).foldl (fun c step ↦ step.run c τ')
          (c.map (SyntacticObject.map f)) =
        (steps.foldl (fun c step ↦ step.run c τ) c).map (SyntacticObject.map f) := by
    intro steps
    induction steps with
    | nil => intro c; rfl
    | cons step steps ih =>
      intro c
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, Step.run_map hf hτ, ih]
  exact key d.steps ⟨d.initial, []⟩

theorem stageAt_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (n : Nat) : (d.map f).stageAt n τ' = (d.stageAt n τ).map f := by
  rw [stageAt, stageAt, take_map, final, final, run_map (d.take n) hf hτ, Cfg.map_current]

variable (f)

theorem movedItems_map : (d.map f).movedItems = d.movedItems.map (SyntacticObject.map f) := by
  simp [movedItems, map, List.filterMap_map, List.map_filterMap]

theorem mover?_map (i : ℕ) : (d.map f).mover? i = (d.mover? i).map (SyntacticObject.map f) := by
  rw [mover?, mover?, map]
  simp only [List.getElem?_map]
  cases d.steps[i]? <;> simp

end Derivation

end Map

end Minimalist
