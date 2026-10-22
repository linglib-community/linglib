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
and is flagged as interacting; a goal that satisfies the probe is flagged as its satisfier and ends
the search; and a goal bearing a feature marked for dynamic interaction changes the interaction
condition for the goals after it. `Probe.Dynamic.agree` is this operation for a probe that depends
on a state, `Probe.agree` its case for a fixed probe, and `Probe.Spec.agree` its case for feature
sets, Deal's algorithm (30).

For a fixed probe, a search that meets no interacting goal leaves the state unchanged, so Agree
fails without penalty as Preminger argues; the single goal of `Probe.goal` is the case in which
every interacting goal satisfies the probe; and Multiple Agree is the case of an insatiable probe.

## Main definitions

* `Minimalist.Probe.Result`: the state Agree leaves, the goals flagged as interacting, and the
  satisfier.
* `Minimalist.Probe.Dynamic`, `Minimalist.Probe.Dynamic.agree`: a probe depending on a state, and
  its Agree operation.
* `Minimalist.Probe.agree`: Agree for a fixed probe and a copying operation.
* `Minimalist.Probe.inspected`: the goals up to and including the first satisfier.
* `Minimalist.Probe.Spec`, `Minimalist.Probe.Spec.agree`: interaction and satisfaction feature
  sets, and Agree over goals exposing feature sets with dynamic interaction.

## Main results

* `Minimalist.Probe.Dynamic.agree_satisfier`: when satisfaction ignores the state, the satisfier is
  the first goal that satisfies the probe.
* `Minimalist.Probe.agree_interacted`, `Minimalist.Probe.agree_state`: a fixed probe flags the
  interacting inspected goals and copies from them in order.
* `Minimalist.Probe.agree_interacted_eq_goal`, `Minimalist.Probe.insatiable_agree_interacted`:
  single-goal Agree and Multiple Agree as special cases.
* `Minimalist.Probe.Spec.agree_empty`: without dynamic interaction a specification Agrees as the
  probe it denotes.
* `Minimalist.Probe.Spec.dynamicUpdate_subset_Ici`: dynamic interaction narrows the interaction
  condition to the features a dynamic feature dominates.
* `Minimalist.Probe.Spec.foldl_dynamicUpdate`, `Minimalist.Probe.Spec.mem_agree_interacted_iff`:
  the interaction condition a goal meets is the one the last goal before it bearing a dynamic
  feature sets, so the goals Agree flags are fixed by their position in the search.

## Implementation notes

Movement, the M subfeatures of lines 5–6 and 9–10 of (30), is not modelled; `Spec.attract` gives
movement a search of its own instead. Line 13 installs the closure of one feature marked for
dynamic interaction; when a goal bears several, `Spec.dynamicUpdate` installs the features all of
them dominate, which on a chain of features is the closure of the most specific one.

## References

* [deal-2025a]
* [deal-2024]
* [hiraiwa-2001]
* [preminger-2014]
-/

@[expose] public section

namespace Minimalist

variable {α σ F : Type*}

/-- The result of Agree over a goal sequence, the state after copying from every interacting goal,
the goals flagged as interacting, in search order, and the goal flagged as the satisfier, if
any. -/
structure Probe.Result (α σ : Type*) where
  /-- The state after copying from every interacting goal. -/
  state : σ
  /-- The goals flagged as interacting, in search order. -/
  interacted : List α
  /-- The goal flagged as satisfying the probe, if the search was satisfied. -/
  satisfier : Option α

namespace Probe

/-- A probe that depends on a state, as a probe under dynamic interaction depends on what it has
met. -/
abbrev Dynamic (σ α : Type*) := σ → Probe α

namespace Dynamic

variable (P : Dynamic σ α) (copy update : α → σ → σ)

/-- Agree for a probe that depends on a state. Each goal in turn is flagged and copied from if it
interacts with the probe of the current state, ends the search if it satisfies it, and otherwise
moves the state by `update` before the next goal. -/
def agree : σ → List α → Result α σ
  | s, [] => ⟨s, [], none⟩
  | s, a :: as =>
    let s' := if (P s).int a then copy a s else s
    let flag := if (P s).int a then [a] else []
    if (P s).sat a then ⟨s', flag, some a⟩
    else
      let r := agree (update a s') as
      ⟨r.state, flag ++ r.interacted, r.satisfier⟩

variable {P copy update} {s : σ} {goals : List α}

@[simp] theorem agree_nil : P.agree copy update s [] = ⟨s, [], none⟩ := rfl

theorem agree_cons (a : α) (as : List α) :
    P.agree copy update s (a :: as) =
      if (P s).sat a then
        ⟨if (P s).int a then copy a s else s, if (P s).int a then [a] else [], some a⟩
      else
        let r := P.agree copy update (update a (if (P s).int a then copy a s else s)) as
        ⟨r.state, (if (P s).int a then [a] else []) ++ r.interacted, r.satisfier⟩ := rfl

/-- When satisfaction does not depend on the state, the satisfier is the first goal that
satisfies the probe. -/
theorem agree_satisfier {sat : α → Bool} (h : ∀ s, (P s).sat = sat) :
    (P.agree copy update s goals).satisfier = goals.find? sat := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [agree_cons, h]
    cases ha : sat a <;> simp [ha, ih]

end Dynamic

/-- Agree for a fixed probe over an ordered goal sequence, copying from every interacting goal up
to the first satisfier. -/
def agree (p : Probe α) (copy : α → σ → σ) : σ → List α → Result α σ :=
  Dynamic.agree (fun _ ↦ p) copy fun _ s ↦ s

/-- The goals a probe inspects, those before the first satisfying goal together with it. -/
def inspected (p : Probe α) (goals : List α) : List α :=
  goals.takeWhile (!p.sat ·) ++ (p.search goals).toList

variable {p : Probe α} {copy : α → σ → σ} {s : σ} {goals : List α}

@[simp] theorem agree_nil : p.agree copy s [] = ⟨s, [], none⟩ := rfl

theorem agree_cons (a : α) (as : List α) :
    p.agree copy s (a :: as) =
      if p.sat a then ⟨if p.int a then copy a s else s, if p.int a then [a] else [], some a⟩
      else
        let r := p.agree copy (if p.int a then copy a s else s) as
        ⟨r.state, (if p.int a then [a] else []) ++ r.interacted, r.satisfier⟩ := rfl

/-- The satisfier is the goal the search finds. -/
@[simp] theorem agree_satisfier : (p.agree copy s goals).satisfier = p.search goals :=
  Dynamic.agree_satisfier fun _ ↦ rfl

/-- The goals flagged as interacting are the inspected goals that interact. -/
@[simp] theorem agree_interacted :
    (p.agree copy s goals).interacted = (p.inspected goals).filter p.int := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [agree_cons]
    cases hs : p.sat a <;> cases hi : p.int a <;> simp [inspected, search, hs, hi, ih]

/-- The state is the fold of `copy` over the goals flagged as interacting. -/
theorem agree_state :
    (p.agree copy s goals).state =
      (p.agree copy s goals).interacted.foldl (fun s a ↦ copy a s) s := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [agree_cons]
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
theorem agree_state_eq_of_forall_not_int (h : ∀ a ∈ goals, ¬ p.int a) :
    (p.agree copy s goals).state = s := by
  rw [agree_state, agree_interacted, List.filter_eq_nil_iff.mpr]
  · rfl
  · exact fun a ha hi ↦ h a (mem_of_mem_inspected ha) hi

/-- When every interacting goal satisfies the probe, the only inspected goal that interacts is the
goal of the probe. -/
theorem inspected_filter_int_eq_goal (h : ∀ a, p.int a → p.sat a) :
    (p.inspected goals).filter p.int = (p.goal goals).toList := by
  rw [inspected, List.filter_append, List.filter_eq_nil_iff.mpr, List.nil_append]
  · cases hs : p.search goals with
    | none => simp [goal, hs]
    | some a =>
      simp only [Option.toList_some, List.filter_cons, List.filter_nil, goal, hs,
        Option.filter_some]
      cases p.int a <;> rfl
  · intro a ha hi
    exact absurd (h a hi) (by simpa using List.mem_takeWhile_imp ha)

/-- When every interacting goal satisfies the probe, the only goal flagged as interacting is the
goal of the probe. -/
theorem agree_interacted_eq_goal (h : ∀ a, p.int a → p.sat a) :
    (p.agree copy s goals).interacted = (p.goal goals).toList := by
  rw [agree_interacted, inspected_filter_int_eq_goal h]

/-- A relativized probe flags the goal it finds. -/
theorem relativized_agree_interacted (f : α → Bool) :
    ((relativized f).agree copy s goals).interacted = ((relativized f).search goals).toList := by
  rw [agree_interacted_eq_goal (fun _ h ↦ h), relativized_goal]

/-- An insatiable probe flags every interacting goal, Multiple Agree ([hiraiwa-2001]). -/
theorem insatiable_agree_interacted (f : α → Bool) :
    ((insatiable f).agree copy s goals).interacted = goals.filter f := by
  rw [agree_interacted, inspected, List.takeWhile_eq_self_iff.mpr (by simp),
    search_eq_none_iff.mpr (by simp [insatiable])]
  simp [insatiable]

/-! ### Feature specifications -/

/-- A probe specification over a feature type, the features the probe interacts with and the
features that satisfy it, `[INT:int, SAT:sat]` in [deal-2025a]'s notation. -/
@[ext]
structure Spec (F : Type*) where
  /-- The features the probe copies. -/
  int : Finset F
  /-- The features that halt the probe's search. -/
  sat : Finset F

namespace Spec

/-- Specifications are ordered by inclusion of both feature sets. -/
instance : PartialOrder (Spec F) :=
  PartialOrder.lift (fun sp ↦ (sp.int, sp.sat)) fun _ _ h ↦ Spec.ext_iff.2 (Prod.ext_iff.1 h)

theorem le_def {sp sp' : Spec F} : sp ≤ sp' ↔ sp.int ⊆ sp'.int ∧ sp.sat ⊆ sp'.sat := Iff.rfl

/-- The specification with no features, a head without that probe. -/
instance : OrderBot (Spec F) where
  bot := ⟨∅, ∅⟩
  bot_le _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

@[simp] theorem bot_int : (⊥ : Spec F).int = ∅ := rfl
@[simp] theorem bot_sat : (⊥ : Spec F).sat = ∅ := rfl

/-- The join of two specifications interacts with and is satisfied by the features of either, a
disjunctive probe. -/
instance [DecidableEq F] : Lattice (Spec F) :=
  { (inferInstance : PartialOrder (Spec F)) with
    sup := fun sp sp' ↦ ⟨sp.int ∪ sp'.int, sp.sat ∪ sp'.sat⟩
    le_sup_left := fun _ _ ↦ ⟨Finset.subset_union_left, Finset.subset_union_left⟩
    le_sup_right := fun _ _ ↦ ⟨Finset.subset_union_right, Finset.subset_union_right⟩
    sup_le := fun _ _ _ h h' ↦ ⟨Finset.union_subset h.1 h'.1, Finset.union_subset h.2 h'.2⟩
    inf := fun sp sp' ↦ ⟨sp.int ∩ sp'.int, sp.sat ∩ sp'.sat⟩
    inf_le_left := fun _ _ ↦ ⟨Finset.inter_subset_left, Finset.inter_subset_left⟩
    inf_le_right := fun _ _ ↦ ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
    le_inf := fun _ _ _ h h' ↦ ⟨Finset.subset_inter h.1 h'.1, Finset.subset_inter h.2 h'.2⟩ }

@[simp] theorem sup_int [DecidableEq F] (sp sp' : Spec F) : (sp ⊔ sp').int = sp.int ∪ sp'.int :=
  rfl
@[simp] theorem sup_sat [DecidableEq F] (sp sp' : Spec F) : (sp ⊔ sp').sat = sp.sat ∪ sp'.sat :=
  rfl

/-- The state of Agree for a specification, the features copied so far and the current
interaction condition. -/
structure State (F : Type*) where
  /-- The features copied to the probe so far. -/
  copied : Finset F
  /-- The current interaction condition. -/
  int : Finset F

variable [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- The interaction features a goal bears, which Agree copies from it. -/
def intFeatures (a : α) : Finset F := feats a ∩ sp.int

/-- The satisfaction features a goal bears. -/
def satFeatures (a : α) : Finset F := feats a ∩ sp.sat

/-- The probe a specification denotes over goals exposing feature sets, interacting with a goal
iff it bears a feature of the interaction specification and satisfied iff it bears one of the
satisfaction specification. -/
def toProbe : Probe α :=
  ⟨fun a ↦ decide (sp.intFeatures feats a).Nonempty,
    fun a ↦ decide (sp.satFeatures feats a).Nonempty⟩

@[simp] theorem toProbe_int (a : α) :
    (sp.toProbe feats).int a = decide (sp.intFeatures feats a).Nonempty := rfl

@[simp] theorem toProbe_sat (a : α) :
    (sp.toProbe feats).sat a = decide (sp.satFeatures feats a).Nonempty := rfl

section Dynamic

variable [Preorder F] [LocallyFiniteOrderTop F] (dyn : Finset F)

/-- After a goal, the interaction condition becomes the features dominated by every feature of the
goal marked for dynamic interaction, and stays unchanged if the goal bears none. -/
def dynamicUpdate (a : α) (int : Finset F) : Finset F :=
  if h : (feats a ∩ dyn).Nonempty then (feats a ∩ dyn).inf' h Finset.Ici else int

/-- Agree (30) of [deal-2025a] over goals exposing feature sets, `dyn` the features marked for
dynamic interaction. The probe interacts by the current interaction condition, which starts as
`sp.int`. -/
def agree (goals : List α) : Result α (State F) :=
  Dynamic.agree (fun st ↦ ({ sp with int := st.int } : Spec F).toProbe feats)
    (fun a st ↦ ⟨st.copied ∪ (feats a ∩ st.int), st.int⟩)
    (fun a st ↦ ⟨st.copied, dynamicUpdate feats dyn a st.int⟩) ⟨∅, sp.int⟩ goals

/-- A specification halts on the first goal bearing a satisfaction feature, whatever the dynamic
interaction. -/
theorem agree_satisfier (goals : List α) :
    (sp.agree feats dyn goals).satisfier = (sp.toProbe feats).search goals :=
  Dynamic.agree_satisfier fun _ ↦ rfl

/-- Dynamic interaction narrows the interaction condition to the features that a dynamic feature
of the goal dominates. -/
theorem dynamicUpdate_subset_Ici {a : α} {x : F} (hx : x ∈ feats a ∩ dyn) (int : Finset F) :
    dynamicUpdate feats dyn a int ⊆ Finset.Ici x := by
  unfold dynamicUpdate
  split
  · exact Finset.inf'_le _ hx
  · exact (‹¬ (feats a ∩ dyn).Nonempty› ⟨x, hx⟩).elim

@[simp] theorem dynamicUpdate_empty (a : α) (int : Finset F) :
    dynamicUpdate feats ∅ a int = int := by
  simp [dynamicUpdate]

/-- Without dynamic interaction, a specification Agrees as the probe it denotes, copying the
interaction-specified features of each interacting goal. -/
theorem agree_empty (goals : List α) :
    sp.agree feats ∅ goals =
      let r := (sp.toProbe feats).agree (fun a c ↦ c ∪ sp.intFeatures feats a) ∅ goals
      ⟨⟨r.state, sp.int⟩, r.interacted, r.satisfier⟩ := by
  simp only [agree, dynamicUpdate_empty]
  generalize (∅ : Finset F) = c
  induction goals generalizing c with
  | nil => rfl
  | cons a as ih =>
    rw [Dynamic.agree_cons, Probe.agree_cons]
    dsimp only [toProbe, intFeatures, satFeatures] at ih ⊢
    split_ifs <;> dsimp only <;> rw [ih]

/-- A goal bearing a feature marked for dynamic interaction resets the interaction condition,
whatever it was. -/
theorem dynamicUpdate_eq_of_nonempty {a : α} (h : (feats a ∩ dyn).Nonempty) (int int' : Finset F) :
    dynamicUpdate feats dyn a int = dynamicUpdate feats dyn a int' := by
  simp [dynamicUpdate, h]

theorem dynamicUpdate_eq_self {a : α} (h : ¬ (feats a ∩ dyn).Nonempty) (int : Finset F) :
    dynamicUpdate feats dyn a int = int := by
  simp [dynamicUpdate, h]

/-- After a sequence of goals the interaction condition is the one the last goal bearing a dynamic
feature sets, and the initial condition if no goal bears one. -/
theorem foldl_dynamicUpdate (int : Finset F) (l : List α) :
    l.foldl (fun i a ↦ dynamicUpdate feats dyn a i) int =
      ((l.filter fun a ↦ (feats a ∩ dyn).Nonempty).getLast?).elim int
        fun b ↦ dynamicUpdate feats dyn b int := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.filter_append]
    by_cases h : (feats a ∩ dyn).Nonempty
    · rw [dynamicUpdate_eq_of_nonempty feats dyn h _ int]
      simp [h]
    · simp [h, dynamicUpdate_eq_self feats dyn h]

private theorem mem_interacted_iff {a : α} (st : State F) (goals : List α) :
    a ∈ (Dynamic.agree (fun st ↦ ({ sp with int := st.int } : Spec F).toProbe feats)
      (fun a st ↦ ⟨st.copied ∪ (feats a ∩ st.int), st.int⟩)
      (fun a st ↦ ⟨st.copied, dynamicUpdate feats dyn a st.int⟩) st goals).interacted ↔
    ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ (∀ b ∈ l₁, ¬ (sp.toProbe feats).sat b) ∧
      (feats a ∩ l₁.foldl (fun i b ↦ dynamicUpdate feats dyn b i) st.int).Nonempty := by
  induction goals generalizing st with
  | nil => simp
  | cons x xs ih =>
    rw [Dynamic.agree_cons]
    have hint : (({ sp with int := st.int } : Spec F).toProbe feats).int x =
        decide (feats x ∩ st.int).Nonempty := rfl
    by_cases hs : (sp.toProbe feats).sat x
    · rw [ite_eq_left (show (({ sp with int := st.int } : Spec F).toProbe feats).sat x from hs)]
      dsimp only
      constructor
      · intro ha
        rw [hint] at ha
        split_ifs at ha with hx
        · obtain rfl := List.mem_singleton.1 ha
          exact ⟨[], xs, rfl, by simp, by simpa using hx⟩
        · simp at ha
      · rintro ⟨_ | ⟨y, l₁⟩, l₂, he, hl₁, ha⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          rw [hint, ite_eq_left (by simpa using ha)]
          exact List.mem_singleton_self _
        · obtain ⟨rfl, -⟩ := List.cons.inj he
          exact absurd hs (hl₁ _ (List.mem_cons_self ..))
    · rw [ite_eq_right (show ¬ (({ sp with int := st.int } : Spec F).toProbe feats).sat x from hs)]
      dsimp only
      rw [List.mem_append, ih]
      have hupd : ∀ st' : State F, st'.int = st.int →
          (dynamicUpdate feats dyn x st'.int) = dynamicUpdate feats dyn x st.int :=
        fun _ h ↦ h ▸ rfl
      constructor
      · rintro (ha | ⟨l₁, l₂, rfl, hl₁, ha⟩)
        · rw [hint] at ha
          split_ifs at ha with hx
          · obtain rfl := List.mem_singleton.1 ha
            exact ⟨[], xs, rfl, by simp, by simpa using hx⟩
          · simp at ha
        · refine ⟨x :: l₁, l₂, rfl, ?_, ?_⟩
          · rintro b (_ | ⟨_, hb⟩)
            · exact hs
            · exact hl₁ b hb
          · rw [List.foldl_cons]
            convert ha using 3
            split_ifs <;> rfl
      · rintro ⟨_ | ⟨y, l₁⟩, l₂, he, hl₁, ha⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          left
          rw [hint, ite_eq_left (by simpa using ha)]
          exact List.mem_singleton_self _
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          right
          refine ⟨l₁, l₂, rfl, fun b hb ↦ hl₁ b (List.mem_cons_of_mem _ hb), ?_⟩
          rw [List.foldl_cons] at ha
          convert ha using 3
          split_ifs <;> rfl

/-- Agree with dynamic interaction flags a goal iff no goal before it satisfies the probe and it
bears a feature of the interaction condition the goals before it leave, which
`foldl_dynamicUpdate` reads off the last of them bearing a dynamic feature. -/
theorem mem_agree_interacted_iff {a : α} (goals : List α) :
    a ∈ (sp.agree feats dyn goals).interacted ↔
      ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ (∀ b ∈ l₁, ¬ (sp.toProbe feats).sat b) ∧
        (feats a ∩ l₁.foldl (fun i b ↦ dynamicUpdate feats dyn b i) sp.int).Nonempty :=
  mem_interacted_iff sp feats dyn ⟨∅, sp.int⟩ goals

end Dynamic

end Spec

end Probe

end Minimalist
