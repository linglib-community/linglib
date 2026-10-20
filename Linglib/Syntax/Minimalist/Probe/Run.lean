/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Interval.Finset.Defs

/-!
# The Agree operation

In Deal's interaction and satisfaction theory, Agree inspects the goals in the probe's domain one
at a time. A goal that interacts with the probe has its interacting features copied to the probe
and is flagged as a goal; a goal that satisfies the probe is flagged as its satisfier and ends the
search; and a goal bearing a feature marked for dynamic interaction changes the interaction
condition for the goals after it. `Probe.runWith` is this loop over any state the two tests read,
`Probe.run` its case for a fixed probe, and `Probe.Spec.run` its case for feature sets, Deal's
algorithm (30).

For a fixed probe, a search that meets no interacting goal leaves the state unchanged, so Agree
fails without penalty as Preminger argues; the single-goal search of `Probe/Basic.lean` is the case
in which every interacting goal satisfies the probe; and Multiple Agree is the case of an insatiable
probe.

## Main definitions

* `Minimalist.Probe.runWith`: the Agree loop over a state that the interaction and satisfaction
  tests read, returning a `Minimalist.Probe.Result`, the state, the flagged goals and the
  satisfier.
* `Minimalist.Probe.run`: Agree for a fixed probe and a copying operation.
* `Minimalist.Probe.inspected`: the goals up to and including the first satisfier.
* `Minimalist.Probe.Spec`, `Minimalist.Probe.Spec.run`: interaction and satisfaction feature sets,
  and Agree over goals exposing feature sets with dynamic interaction.

## Main results

* `Minimalist.Probe.run_halt`, `Minimalist.Probe.run_goals`, `Minimalist.Probe.run_state`: a fixed
  probe halts on the goal its search finds, flags the interacting inspected goals, and copies from
  them in order.
* `Minimalist.Probe.run_goals_eq_agree`, `Minimalist.Probe.insatiable_run_goals`: single-goal Agree
  and Multiple Agree as special cases.
* `Minimalist.Probe.Spec.run_halt`: a specification halts on the first goal bearing a satisfaction
  feature, whatever the dynamic interaction.

## Implementation notes

Movement, the M subfeatures of lines 5–6 and 9–10 of (30), is not modelled. Line 13 installs the
closure of one feature marked for dynamic interaction; when a goal bears several, `Spec.run`
installs the features all of them dominate, which on a chain of features is the closure of the most
specific one.

## References

* [deal-2025a]
* [deal-2024]
* [hiraiwa-2001]
* [preminger-2014]
-/

@[expose] public section

namespace Minimalist

variable {α σ F : Type*}

/-- The result of running a probe over a goal sequence, the state after copying from every
interacting goal, the goals flagged as interacting, in search order, and the goal flagged as the
satisfier, if any. -/
structure Probe.Result (α σ : Type*) where
  /-- The state after copying from every interacting goal. -/
  state : σ
  /-- The goals the probe interacted with, in search order. -/
  goals : List α
  /-- The goal that satisfied the probe, if the search was satisfied. -/
  halt : Option α

namespace Probe

/-- The Agree loop over a goal sequence. Each goal in turn is flagged and copied from if it
interacts in the current state, ends the search if it satisfies in that state, and otherwise moves
the state by `update` before the next goal. -/
def runWith (int sat : σ → α → Bool) (copy update : α → σ → σ) : σ → List α → Result α σ
  | s, [] => ⟨s, [], none⟩
  | s, a :: as =>
    let s' := if int s a then copy a s else s
    let flag := if int s a then [a] else []
    if sat s a then ⟨s', flag, some a⟩
    else
      let r := runWith int sat copy update (update a s') as
      ⟨r.state, flag ++ r.goals, r.halt⟩

/-- The Agree operation of a fixed probe over an ordered goal sequence. -/
def run (p : Probe α) (copy : α → σ → σ) : σ → List α → Result α σ :=
  runWith (fun _ ↦ p.int) (fun _ ↦ p.sat) copy fun _ s ↦ s

/-- The goals a probe inspects, those before the first satisfying goal together with it. -/
def inspected (p : Probe α) (goals : List α) : List α :=
  goals.takeWhile (!p.sat ·) ++ (p.search goals).toList

variable {p : Probe α} {copy : α → σ → σ} {s : σ} {goals : List α}

@[simp] theorem run_nil : p.run copy s [] = ⟨s, [], none⟩ := rfl

theorem run_cons (a : α) (as : List α) :
    p.run copy s (a :: as) =
      if p.sat a then ⟨if p.int a then copy a s else s, if p.int a then [a] else [], some a⟩
      else
        let r := p.run copy (if p.int a then copy a s else s) as
        ⟨r.state, (if p.int a then [a] else []) ++ r.goals, r.halt⟩ := rfl

/-- The satisfier of the fold is the goal the search finds. -/
@[simp] theorem run_halt : (p.run copy s goals).halt = p.search goals := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [run_cons]
    cases hs : p.sat a
    · simpa [search, hs] using ih
    · simp [search, hs]

/-- The flagged goals are the inspected goals that interact. -/
@[simp] theorem run_goals : (p.run copy s goals).goals = (p.inspected goals).filter p.int := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [run_cons]
    cases hs : p.sat a <;> cases hi : p.int a <;> simp [inspected, search, hs, hi, ih]

/-- The state is the fold of `copy` over the flagged goals. -/
theorem run_state :
    (p.run copy s goals).state = (p.run copy s goals).goals.foldl (fun s a ↦ copy a s) s := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [run_cons]
    cases p.sat a <;> cases p.int a <;> simp [ih]

/-- An inspected goal is a member of the sequence. -/
theorem mem_of_mem_inspected {a : α} (ha : a ∈ p.inspected goals) : a ∈ goals := by
  rcases List.mem_append.mp ha with h | h
  · exact List.takeWhile_subset _ h
  · cases hs : p.search goals with
    | none => simp [hs] at h
    | some b =>
      simp only [hs, Option.toList_some, List.mem_singleton] at h
      exact h ▸ mem_of_search_eq_some hs

/-- A probe that interacts with no goal leaves the state unchanged. -/
theorem run_state_eq_of_forall_not_int (h : ∀ a ∈ goals, ¬ p.int a) :
    (p.run copy s goals).state = s := by
  rw [run_state, run_goals, List.filter_eq_nil_iff.mpr]
  · rfl
  · exact fun a ha hi ↦ h a (mem_of_mem_inspected ha) hi

/-- When every interacting goal satisfies the probe, the flagged goals are the single goal the
probe Agrees with. -/
theorem run_goals_eq_agree (h : ∀ a, p.int a → p.sat a) :
    (p.run copy s goals).goals = (p.agree goals).toList := by
  rw [run_goals, inspected, List.filter_append, List.filter_eq_nil_iff.mpr, List.nil_append]
  · cases hs : p.search goals with
    | none => simp [agree, hs]
    | some a =>
      simp only [Option.toList_some, List.filter_cons, List.filter_nil, agree, hs,
        Option.filter_some]
      cases p.int a <;> rfl
  · intro a ha hi
    exact absurd (h a hi) (by simpa using List.mem_takeWhile_imp ha)

/-- A relativized probe flags the goal it finds. -/
theorem relativized_run_goals (f : α → Bool) :
    ((relativized f).run copy s goals).goals = ((relativized f).search goals).toList := by
  rw [run_goals_eq_agree (fun _ h ↦ h), relativized_agree]

/-- An insatiable probe flags every interacting goal, Multiple Agree ([hiraiwa-2001]). -/
theorem insatiable_run_goals (f : α → Bool) :
    ((insatiable f).run copy s goals).goals = goals.filter f := by
  rw [run_goals, inspected, List.takeWhile_eq_self_iff.mpr (by simp),
    search_eq_none_iff.mpr (by simp [insatiable])]
  simp [insatiable]

/-! ### Feature specifications -/

/-- A probe specification over a feature type, the features the probe interacts with and the
features that satisfy it, `[INT:int, SAT:sat]` in [deal-2025a]'s notation. -/
structure Spec (F : Type*) where
  /-- The features the probe copies. -/
  int : Finset F
  /-- The features that halt the probe's search. -/
  sat : Finset F

namespace Spec

variable [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- The probe a specification denotes over goals exposing feature sets, interacting with a goal
iff it bears a feature of the interaction specification and satisfied iff it bears one of the
satisfaction specification. -/
def toProbe : Probe α :=
  ⟨fun a ↦ decide (feats a ∩ sp.int).Nonempty, fun a ↦ decide (feats a ∩ sp.sat).Nonempty⟩

@[simp] theorem toProbe_int (a : α) :
    (sp.toProbe feats).int a = decide (feats a ∩ sp.int).Nonempty := rfl

@[simp] theorem toProbe_sat (a : α) :
    (sp.toProbe feats).sat a = decide (feats a ∩ sp.sat).Nonempty := rfl

section Dynamic

variable [Preorder F] [LocallyFiniteOrderTop F] (dyn : Finset F)

/-- After a goal, the interaction condition becomes the features dominated by every feature of the
goal marked for dynamic interaction, and stays unchanged if the goal bears none. -/
def dynamicUpdate (a : α) (int : Finset F) : Finset F :=
  if h : (feats a ∩ dyn).Nonempty then (feats a ∩ dyn).inf' h Finset.Ici else int

/-- The Agree operation (30) of [deal-2025a] over goals exposing feature sets, `dyn` the features
marked for dynamic interaction. The state is the features copied so far and the current interaction
condition, which starts as `sp.int`. -/
def run (goals : List α) : Result α (Finset F × Finset F) :=
  runWith (fun s a ↦ decide (feats a ∩ s.2).Nonempty) (fun _ a ↦ decide (feats a ∩ sp.sat).Nonempty)
    (fun a s ↦ (s.1 ∪ (feats a ∩ s.2), s.2)) (fun a s ↦ (s.1, dynamicUpdate feats dyn a s.2))
    (∅, sp.int) goals

/-- A specification halts on the first goal bearing a satisfaction feature, whatever the dynamic
interaction. -/
theorem run_halt (goals : List α) :
    (sp.run feats dyn goals).halt = (sp.toProbe feats).search goals := by
  suffices ∀ s : Finset F × Finset F, (runWith (fun s a ↦ decide (feats a ∩ s.2).Nonempty)
      (fun _ a ↦ decide (feats a ∩ sp.sat).Nonempty) (fun a s ↦ (s.1 ∪ (feats a ∩ s.2), s.2))
      (fun a s ↦ (s.1, dynamicUpdate feats dyn a s.2)) s goals).halt =
        (sp.toProbe feats).search goals from this _
  induction goals with
  | nil => intro; rfl
  | cons a as ih =>
    intro s
    by_cases hs : (feats a ∩ sp.sat).Nonempty
    · simp [runWith, search, hs]
    · simpa [runWith, search, hs] using ih _

end Dynamic

end Spec

end Probe

end Minimalist
