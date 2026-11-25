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
and `remerge` passing through a stack of copies. That a Merge step is MERGE on the workspace, and
an admissible derivation the iterated algebraic Merge, is proved in `Workspace/Derivation.lean`.
The side on which a step places
its daughter, and the order of an item's daughters, are linearization data that [the derived object
ignores](##Minimalist.Step.apply_em) and only the replay reads.

## Implementation notes

* Which item heads the mover is a theory's choice, so the steps and stages take the trace encoder
  as a parameter, by default the head by selection.
* The traces of a derivation are labelled in a type `ι`, tokens by default. A derivation labelled
  in `ℕ` runs under `Derivation.moverIndex`, which numbers a trace by its mover's place among the
  movers, so that a mover holding a trace names it by that number.

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
inductive Step (ι : Type := LexicalItem.Token) where
  /-- External Merge, the new item as the daughter on `side`. -/
  | em (side : Edge) (item : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
  /-- Internal Merge raises `mover` to the daughter on `side`, the left unless stated otherwise,
  leaving the trace of its head in its place. -/
  | im (mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) (side : Edge := .left)
  /-- The unit stage of Internal Merge puts a copy of `mover` on top of the stack, leaving the
  trace of its head in its place. -/
  | extract (mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
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

variable {α β : Type*} {ι : Type}

/-- A map applied to the object and to every copy on the stack. -/
def map (f : α → β) (c : Cfg α) : Cfg β := ⟨f c.current, c.stack.map f⟩

@[simp] theorem map_current (f : α → β) (c : Cfg α) : (c.map f).current = f c.current := rfl

@[simp] theorem map_stack (f : α → β) (c : Cfg α) : (c.map f).stack = c.stack.map f := rfl

/-- The tokens a configuration pronounces, its object's and those of the copies on its stack. -/
def yield (c : Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) : Multiset
    LexicalItem.Token :=
  c.current.yield + (c.stack.map SyntacticObject.yield).sum

@[simp] theorem yield_map (f : α → SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (c : Cfg α) :
    (c.map f).yield = (f c.current).yield + (c.stack.map fun x ↦ (f x).yield).sum := by
  simp [yield, map, Function.comp_def]

end Derivation.Cfg

variable {ι : Type} [DecidableEq ι] [TraceLabel LexicalItem.Token ι]

/-- The object a step builds from the current one, the copies on the stack aside. External Merge
    adds the item, Internal Merge merges the remainder and the mover, leaving the trace of its head
    under `τ`, and an extraction leaves the remainder. `remerge` needs the stack (`Step.run`). -/
def Step.apply (step : Step ι)
    (current : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι :=
        TraceLabel.encoder) : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) :=
  match step with
  | .em _ item => merge item current
  | .im mover _ => merge (deleteAccessible mover current τ) mover
  | .extract mover => deleteAccessible mover current τ
  | .remerge _ => current

/-- A step on a configuration. An extraction pushes the mover's copy onto the stack, `remerge`
    merges the copy on top back by External Merge, and the other steps leave the stack alone. -/
def Step.run (step : Step ι)
    (c : Derivation.Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)))
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι :=
        TraceLabel.encoder) :
    Derivation.Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :=
  match step, c.stack with
  | .extract mover, st => ⟨step.apply c.current τ, mover :: st⟩
  | .remerge _, m :: st => ⟨merge m c.current, st⟩
  | _, st => ⟨step.apply c.current τ, st⟩

variable {τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι}

theorem Step.apply_em_right
    (item : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (current : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (Step.em .right item).apply current τ = merge current item := merge_comm _ _

theorem Step.apply_im (mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (side : Edge)
    (current : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (Step.im mover side).apply current τ = merge (deleteAccessible mover current τ) mover := rfl

/-- The sides build the same object; they differ only at externalization. -/
theorem Step.apply_em (side : Edge)
    (item : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (current : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (Step.em side item).apply current τ = merge item current := rfl

/-- A step is a Merge, external or internal, rather than one of the two stages of Internal
Merge. -/
def Step.IsMerge : Step ι → Prop
  | .em _ _ | .im _ _ => True
  | .extract _ | .remerge _ => False

instance : DecidablePred (Step.IsMerge (ι := ι)) :=
  fun s ↦ by cases s <;> unfold Step.IsMerge <;> infer_instance

/-- The mover of an Internal-Merge step or an extraction. -/
def Step.mover? : Step ι → Option (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
  | .im mover _ | .extract mover => some mover
  | .em _ _ | .remerge _ => none

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.mover?_em (side : Edge)
    (item : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (Step.em side item).mover? = none := rfl

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.mover?_im (mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (side : Edge) :
    (Step.im mover side).mover? = some mover :=
  rfl

/-- A step with mover `m` builds an object whose terms are among those of the remainder merged
with `m`: an Internal Merge builds exactly that, and an extraction the remainder alone. -/
theorem Step.terms_current_run_subset {step : Step ι}
    {m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : m ∈ step.mover?)
    (c : Derivation.Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) :
    (step.run c τ).current.terms ⊆ (merge (deleteAccessible m c.current τ) m).terms := by
  cases step with
  | em _ _ | remerge _ => cases h
  | im mover side => obtain rfl := Option.some.inj h; exact fun _ hu ↦ hu
  | extract mover =>
    obtain rfl := Option.some.inj h
    exact fun u hu ↦ by
      rw [terms_merge]; exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl hu))

/-- The step with its new daughter on the left. -/
def Step.leftward : Step ι → Step ι
  | .em _ item => .em .left item
  | .im mover _ => .im mover
  | .extract mover => .extract mover
  | .remerge _ => .remerge

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.leftward_em (side : Edge)
    (item : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (Step.em side item).leftward = .em .left item := rfl

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.leftward_im
    (mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) (side : Edge) :
    (Step.im mover side).leftward = .im mover :=
  rfl

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.mover?_leftward (step : Step ι) : step.leftward.mover? = step.mover? := by
  cases step <;> rfl

/-- A step and its leftward form build the same object. -/
theorem Step.apply_leftward (step : Step ι)
    (current : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    step.leftward.apply current τ = step.apply current τ := by
  cases step with
  | em side item => rw [Step.leftward_em, Step.apply_em, Step.apply_em]
  | _ => rfl

/-- A step and its leftward form reach the same configuration. -/
theorem Step.run_leftward (step : Step ι)
    (c : Derivation.Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) :
    step.leftward.run c τ = step.run c τ := by
  obtain ⟨cur, _ | ⟨m, st⟩⟩ := c <;> cases step <;> rfl

/-- Internal Merge is an extraction followed by merging the copy back
    ([marcolli-chomsky-berwick-2025] Proposition 1.4.2). -/
theorem Step.run_im (mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (side : Edge)
    (c : Derivation.Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) :
    (Step.im mover side).run c τ = (Step.remerge side).run ((Step.extract mover).run c τ) τ := by
  obtain ⟨cur, st⟩ := c
  show (⟨_, st⟩ : Derivation.Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) =
      ⟨_, st⟩
  rw [Step.apply_im, merge_comm]
  rfl

/-! ### Items -/

/-- The item an External Merge step introduces. -/
def Step.items : Step ι → Forest (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
  | .em _ item => {↑item}
  | .im _ _ | .extract _ | .remerge _ => 0

/-- The items a list of steps introduces. -/
def Step.itemsList (steps : List (Step ι)) : Forest
    (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :=
  (steps.map Step.items).sum

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.itemsList_nil : Step.itemsList ([] : List (Step ι)) = 0 := rfl

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem Step.itemsList_cons (step : Step ι) (steps : List (Step ι)) :
    Step.itemsList (step :: steps) = step.items + Step.itemsList steps := by
  simp [Step.itemsList]

/-! ### Derivations -/

/-- An initial syntactic object with a sequence of steps. -/
structure Derivation (ι : Type := LexicalItem.Token) where
  /-- The initial syntactic object (a lexical item, in canonical derivations). -/
  initial : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)
  /-- The ordered sequence of Merge/Move steps. -/
  steps : List (Step ι)

namespace Derivation

/-- The movers of the `im` and `extract` steps. -/
def movedItems (d : Derivation ι) : List
    (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :=
  d.steps.filterMap Step.mover?

/-- The place of an object among the objects the derivation moves, the first for an object moved
more than once: the encoder under which a derivation with traces labelled in `ℕ` numbers the trace
of each mover. -/
def moverIndex (d : Derivation ι) (m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    : Option ℕ :=
  d.movedItems.idxOf? m

/-- The configuration after every step, under the trace encoder `τ`. -/
def run (d : Derivation ι)
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι :=
        TraceLabel.encoder) :
    Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :=
  d.steps.foldl (fun c step ↦ step.run c τ) ⟨d.initial, []⟩

/-- The object after every step, under the trace encoder `τ`. -/
def final (d : Derivation ι)
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι :=
        TraceLabel.encoder) :
    SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) :=
  (d.run τ).current

/-- The number of derivation steps. -/
def length (d : Derivation ι) : Nat := d.steps.length

/-- The mover of step `i`, when that step is an Internal Merge or an extraction. -/
def mover? (d : Derivation ι) (i : ℕ) : Option
    (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :=
  d.steps[i]? >>= Step.mover?

/-- The first `n` steps. -/
def take (d : Derivation ι) (n : Nat) : Derivation ι := ⟨d.initial, d.steps.take n⟩

/-- The derivation continued by `steps`. -/
def append (d : Derivation ι) (steps : List (Step ι)) : Derivation ι :=
  ⟨d.initial, d.steps ++ steps⟩

/-- The object after the first `n` steps, under the trace encoder `τ`. -/
def stageAt (d : Derivation ι) (n : Nat)
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι :=
        TraceLabel.encoder) :
    SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) :=
  (d.take n).final τ

@[simp] theorem stageAt_zero (d : Derivation ι) : d.stageAt 0 τ = d.initial := by
  simp [stageAt, final, run, take]

theorem stageAt_length (d : Derivation ι) : d.stageAt d.steps.length τ = d.final τ := by
  simp [stageAt, take, List.take_length]

@[simp] theorem final_take (d : Derivation ι) (n : Nat) : (d.take n).final τ = d.stageAt n τ := rfl

/-! ### Extension

The early stages and the movers of an extended derivation are the original's. -/

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem length_append (d : Derivation ι) (steps : List (Step ι)) :
    (d.append steps).length = d.length + steps.length := by
  simp [length, append]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem append_assoc (d : Derivation ι) (steps steps' : List (Step ι)) :
    (d.append steps).append steps' = d.append (steps ++ steps') := by
  simp [append]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- The first `n ≤ d.length` steps of an extension are `d`'s. -/
theorem take_append_of_le {d : Derivation ι} {n : Nat} (h : n ≤ d.length) (steps : List (Step ι)) :
    (d.append steps).take n = d.take n := by
  simp [take, append, List.take_append_of_le_length h]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem take_length (d : Derivation ι) : d.take d.length = d := by
  simp [take, length]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem take_length_append (d : Derivation ι) (steps : List (Step ι)) :
    (d.append steps).take d.length = d := by
  unfold take append
  rw [length, List.take_left]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem take_append_drop (d : Derivation ι) (n : Nat) :
    (d.take n).append (d.steps.drop n) = d := by
  simp [take, append]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- The first `i + 1` steps are the first `i` and step `i`. -/
theorem take_succ {d : Derivation ι} {i : Nat} {step : Step ι} (h : d.steps[i]? = some step) :
    d.take (i + 1) = (d.take i).append [step] := by
  simp [take, append, List.take_add_one, h]

theorem run_append (d : Derivation ι) (steps : List (Step ι)) :
    (d.append steps).run τ = steps.foldl (fun c step ↦ step.run c τ) (d.run τ) := by
  simp [run, append, List.foldl_append]

/-- The configuration after `i + 1` steps is step `i` run on the configuration after `i`. -/
theorem run_take_succ {d : Derivation ι} {i : Nat} {step : Step ι} (h : d.steps[i]? = some step) :
    (d.take (i + 1)).run τ = step.run ((d.take i).run τ) τ := by
  rw [take_succ h, run_append]; rfl

theorem stageAt_append_of_le {d : Derivation ι} {n : Nat} (h : n ≤ d.length)
    (steps : List (Step ι)) :
    (d.append steps).stageAt n τ = d.stageAt n τ := by
  rw [← final_take, ← final_take, take_append_of_le h]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem movedItems_append (d : Derivation ι) (steps : List (Step ι)) :
    (d.append steps).movedItems = d.movedItems ++ steps.filterMap Step.mover? := by
  simp [movedItems, append, List.filterMap_append]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- A step at index `i` has a mover only if `i` indexes a step. -/
theorem lt_length_of_mem_mover? {d : Derivation ι} {i : Nat}
    {m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : m ∈ d.mover? i) : i < d.length := by
  by_contra hlt
  rw [mover?, List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at h
  simp at h

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- The mover of a step is one of the derivation's movers. -/
theorem mem_movedItems_of_mem_mover? {d : Derivation ι} {i : Nat}
    {m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : m ∈ d.mover? i) : m ∈ d.movedItems := by
  obtain ⟨step, hs, hm⟩ := Option.bind_eq_some_iff.1 h
  exact List.mem_filterMap.2 ⟨step, List.mem_of_getElem? hs, hm⟩

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- The early steps of an extension have the original's movers. -/
theorem mover?_append_of_lt {d : Derivation ι} {i : Nat} (h : i < d.length)
    (steps : List (Step ι)) :
    (d.append steps).mover? i = d.mover? i := by
  simp only [mover?, append, List.getElem?_append_left h]

/-! ### The sides of Merge

The node being commutative, the derived object does not depend on the sides at which the steps
attach their daughters; `leftward` is the normal form, and the stages and movers of a derivation
are those of its normal form. -/

/-- The derivation with every new daughter on the left. -/
def leftward (d : Derivation ι) : Derivation ι := ⟨d.initial, d.steps.map Step.leftward⟩

@[simp] theorem run_leftward (d : Derivation ι) : d.leftward.run τ = d.run τ := by
  simp only [run, leftward, List.foldl_map, Step.run_leftward]

@[simp] theorem final_leftward (d : Derivation ι) : d.leftward.final τ = d.final τ := by
  rw [final, final, run_leftward]

@[simp] theorem stageAt_leftward (d : Derivation ι) (n : Nat) :
    d.leftward.stageAt n τ = d.stageAt n τ := by
  rw [stageAt, stageAt, ← final_leftward (d := d.take n)]
  simp only [take, leftward, List.map_take]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
@[simp] theorem movedItems_leftward (d : Derivation ι) : d.leftward.movedItems = d.movedItems := by
  simp [movedItems, leftward, List.filterMap_map]

/-- The items a derivation introduces by External Merge. -/
def items (d : Derivation ι) : Forest (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    := Step.itemsList d.steps

/-- The tokens a derivation merges: those of its initial object and of every item it merges
externally. -/
def lexTokens (d : Derivation ι) : Multiset LexicalItem.Token :=
  d.initial.yield + (d.items.map SyntacticObject.yield).sum

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
theorem lexTokens_append (d : Derivation ι) (steps : List (Step ι)) :
    (d.append steps).lexTokens =
      d.lexTokens + ((Step.itemsList steps).map SyntacticObject.yield).sum := by
  simp [lexTokens, items, append, Step.itemsList, List.map_append, List.sum_append, add_assoc]

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- An initial segment merges no token the derivation does not. -/
theorem lexTokens_take_le (d : Derivation ι) (n : Nat) : (d.take n).lexTokens ≤ d.lexTokens := by
  conv_rhs => rw [← d.take_append_drop n, lexTokens_append]
  exact Multiset.le_add_right _ _

end Derivation

end Minimalist
