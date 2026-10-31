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
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.UpperLower.Closure

/-!
# The Agree operation

In Deal's interaction and satisfaction theory, Agree inspects the goals in the probe's domain one
at a time. A goal that interacts with the probe has its interacting features copied to the probe
and is flagged as interacting; a goal that satisfies the probe is flagged as its satisfier and ends
the search; and a goal bearing a feature marked for dynamic interaction changes the interaction
condition for the goals after it. `Probe.Dynamic.agree` is this operation for a probe that depends
on a state, `Probe.agree` its case for a fixed probe, and `Probe.Spec.agree` its case for feature
specifications, Deal's algorithm (30).

For a fixed probe, a search that meets no interacting goal leaves the state unchanged, so Agree
fails without penalty as Preminger argues; the single goal of `Probe.goal` is the case in which
every interacting goal satisfies the probe; and Multiple Agree is the case of an insatiable probe.

This is the one Agree of the library. A theory of Agree supplies a probe, which fixes what the
search finds, and a copying operation, which fixes what Agree does to the state: valuation of
feature bundles (`Minimalist.FeatureState.value`), the value of a case
(`Minimalist.agreeValue`), or the features a probe accumulates (`Probe.Spec.agree`). When the
state is the list of goals itself, Agree replaces each entry it interacts with (`Probe.agreeList`).
When copying joins the state with what each goal contributes, the order of the goals does not
matter: [Agree joins the initial state with the contributions of the goals it flags](##Minimalist.Probe.agree_sup_state).

## Main definitions

* `Minimalist.Probe.Result`: the state Agree leaves, the goals flagged as interacting, and the
  satisfier.
* `Minimalist.Probe.Dynamic`, `Minimalist.Probe.Dynamic.agree`: a probe depending on a state, and
  its Agree operation.
* `Minimalist.Probe.agree`: Agree for a fixed probe and a copying operation.
* `Minimalist.Probe.inspected`: the goals up to and including the first satisfier.
* `Minimalist.Probe.agreeList`: Agree over the entries of a list that is itself the state.
* `Minimalist.Probe.Spec`: interaction and satisfaction conditions, each a finite set of feature
  bundles presenting the upper set of bundles containing one of them.
* `Minimalist.Probe.Spec.ofFeatures`: the conditions met by bearing any one of some features.
* `Minimalist.Probe.Spec.ofGeometry`, `Minimalist.Probe.Spec.relativized`: `[INT:f, SAT:g]` over a
  feature geometry, interaction copying `f` and the features it dominates.
* `Minimalist.Probe.Spec.agree`: Agree over goals exposing feature sets, with dynamic interaction.

## Main results

* `Minimalist.Probe.Dynamic.agree_satisfier`: when satisfaction ignores the state, the satisfier is
  the first goal that satisfies the probe.
* `Minimalist.Probe.agree_interacted`, `Minimalist.Probe.agree_state`: a fixed probe flags the
  interacting inspected goals and copies from them in order.
* `Minimalist.Probe.agree_interacted_eq_goal`, `Minimalist.Probe.insatiable_agree_interacted`:
  single-goal Agree and Multiple Agree as special cases.
* `Minimalist.Probe.Spec.agree_empty`: without dynamic interaction a specification Agrees as the
  probe it denotes.
* `Minimalist.Probe.Spec.sup_toProbe_int`, `Minimalist.Probe.Spec.sup_toProbe_sat`: the join of
  two specifications is a disjunctive probe.
* `Minimalist.Probe.Spec.ofGeometry_toProbe_int_iff`: over a privative geometry, interacting with
  `[INT:f]` is bearing `f`.
* `Minimalist.Probe.Spec.subset_Ici_of_mem_dynamicUpdate`: dynamic interaction narrows the
  interaction condition to the features a dynamic feature dominates.
* `Minimalist.Probe.Spec.foldl_dynamicUpdate`, `Minimalist.Probe.Spec.mem_agree_interacted_iff`:
  the interaction condition a goal meets is the one the last goal before it bearing a dynamic
  feature sets, so the goals Agree flags are fixed by their position in the search.

## Implementation notes

Movement, the M subfeatures of lines 5–6 and 9–10 of (30), is not modelled; `Probe.attract` gives
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
theorem agree_satisfier {q : Probe α} (h : ∀ s, (P s).sat = q.sat) :
    (P.agree copy update s goals).satisfier = q.search goals := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [agree_cons]
    by_cases ha : q.sat a <;> simp [h, ha, ih, search]

end Dynamic

/-- Agree for a fixed probe over an ordered goal sequence, copying from every interacting goal up
to the first satisfier. -/
def agree (p : Probe α) (copy : α → σ → σ) : σ → List α → Result α σ :=
  Dynamic.agree (fun _ ↦ p) copy fun _ s ↦ s

/-- The goals a probe inspects, those before the first satisfying goal together with it. -/
def inspected (p : Probe α) (goals : List α) : List α :=
  goals.takeWhile (¬ p.sat ·) ++ (p.search goals).toList

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
  Dynamic.agree_satisfier (q := p) fun _ ↦ rfl

/-- The goals flagged as interacting are the inspected goals that interact. -/
@[simp] theorem agree_interacted :
    (p.agree copy s goals).interacted = (p.inspected goals).filter (p.int ·) := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [agree_cons]
    by_cases hs : p.sat a <;> by_cases hi : p.int a <;>
      simp [inspected, search, hs, hi, ih]

/-- The state is the fold of `copy` over the goals flagged as interacting. -/
theorem agree_state :
    (p.agree copy s goals).state =
      (p.agree copy s goals).interacted.foldl (fun s a ↦ copy a s) s := by
  induction goals generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [agree_cons]
    by_cases hs : p.sat a <;> by_cases hi : p.int a <;> simp [hs, hi, ih]

/-- Agree only adds to the state when copying does. -/
theorem le_agree_state [Preorder σ] (h : ∀ a s, s ≤ copy a s) :
    s ≤ (p.agree copy s goals).state := by
  rw [agree_state]
  generalize (p.agree copy s goals).interacted = l
  induction l generalizing s with
  | nil => exact le_rfl
  | cons a l ih => exact (h a s).trans ih

theorem mem_of_mem_inspected {a : α} (ha : a ∈ p.inspected goals) : a ∈ goals := by
  rcases List.mem_append.mp ha with h | h
  · exact List.takeWhile_subset _ h
  · cases hs : p.search goals with
    | none => simp [hs] at h
    | some b =>
      simp only [hs, Option.toList_some, List.mem_singleton] at h
      exact h ▸ mem_of_search_eq_some hs

theorem agree_state_eq_of_forall_not_int (h : ∀ a ∈ goals, ¬ p.int a) :
    (p.agree copy s goals).state = s := by
  rw [agree_state, agree_interacted, List.filter_eq_nil_iff.mpr]
  · rfl
  · exact fun a ha hi ↦ h a (mem_of_mem_inspected ha) (of_decide_eq_true hi)

theorem inspected_filter_int_eq_goal (h : ∀ a, p.int a → p.sat a) :
    (p.inspected goals).filter (p.int ·) = (p.goal goals).toList := by
  rw [inspected, List.filter_append, List.filter_eq_nil_iff.mpr, List.nil_append]
  · cases hs : p.search goals with
    | none => simp [goal, hs]
    | some a =>
      by_cases hi : p.int a <;> simp [goal, hs, hi, Option.filter_some]
  · intro a ha hi
    exact absurd (h a (of_decide_eq_true hi)) (by simpa using List.mem_takeWhile_imp ha)

/-- When every interacting goal satisfies the probe, the only goal flagged as interacting is the
goal of the probe. -/
theorem agree_interacted_eq_goal (h : ∀ a, p.int a → p.sat a) :
    (p.agree copy s goals).interacted = (p.goal goals).toList := by
  rw [agree_interacted, inspected_filter_int_eq_goal h]

theorem relativized_agree_interacted (f : α → Prop) [DecidablePred f] :
    ((relativized f).agree copy s goals).interacted = ((relativized f).search goals).toList := by
  rw [agree_interacted_eq_goal (fun _ h ↦ h), relativized_goal]

/-- An insatiable probe flags every interacting goal, Multiple Agree ([hiraiwa-2001]). -/
theorem insatiable_agree_interacted (f : α → Prop) [DecidablePred f] :
    ((insatiable f).agree copy s goals).interacted = goals.filter (f ·) := by
  rw [agree_interacted, inspected, List.takeWhile_eq_self_iff.mpr (by simp),
    search_eq_none_iff.mpr (by simp [insatiable])]
  simp [insatiable]

/-- When copying joins the state with what each goal contributes, Agree joins the initial state
with the contributions of the goals it flags. -/
theorem agree_sup_state [SemilatticeSup σ] [OrderBot σ] [DecidableEq α] (δ : α → σ) :
    (p.agree (fun a s ↦ s ⊔ δ a) s goals).state =
      s ⊔ ((p.inspected goals).filter (p.int ·)).toFinset.sup δ := by
  rw [agree_state, agree_interacted]
  generalize (p.inspected goals).filter (p.int ·) = l
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sup_insert, sup_assoc]

/-! ### Agree over a list of goals -/

/-- Agree when the state is the list of goals itself: each interacting entry is replaced with `f`
of it. -/
def agreeList (p : Probe α) (f : α → α) (l : List α) : List α :=
  ((p.comap Prod.fst).agree (fun e t ↦ t.set e.2 (f e.1)) l l.zipIdx).state

variable {f : α → α}

private theorem agree_set_zipIdx_succ (q : α) (t l : List α) (n : ℕ) :
    ((p.comap Prod.fst).agree (fun e t ↦ t.set e.2 (f e.1)) (q :: t) (l.zipIdx (n + 1))).state =
      q :: ((p.comap Prod.fst).agree (fun e t ↦ t.set e.2 (f e.1)) t (l.zipIdx n)).state := by
  induction l generalizing n t with
  | nil => rfl
  | cons a l ih =>
    rw [List.zipIdx_cons, List.zipIdx_cons, agree_cons, agree_cons]
    by_cases hs : p.sat a <;> by_cases hi : p.int a <;> simp [hs, hi, ih]

@[simp] theorem agreeList_nil : p.agreeList f [] = [] := rfl

theorem agreeList_cons (a : α) (l : List α) :
    p.agreeList f (a :: l) =
      (if p.int a then f a else a) :: if p.sat a then l else p.agreeList f l := by
  rw [agreeList, List.zipIdx_cons, agree_cons]
  by_cases hs : p.sat a <;> by_cases hi : p.int a <;>
    simp [hs, hi, agreeList, agree_set_zipIdx_succ]

/-! ### Feature specifications -/

/-- A probe specification over a feature type, `[INT:int, SAT:sat]` in [deal-2025a]'s notation.
Each condition lists bundles of features, and a goal meets it when it bears every feature of one
of them, so that a condition presents the upper set of the bundles containing one of its own:
`[INT:Ā+D, SAT:D]` is `⟨{{Ā, D}}, {{D}}⟩`, and a condition listing several bundles is a
disjunction. -/
@[ext]
structure Spec (F : Type*) where
  /-- The bundles whose bearers the probe interacts with. -/
  int : Finset (Finset F)
  /-- The bundles whose bearers halt the probe's search. -/
  sat : Finset (Finset F)

namespace Spec

/-- A specification is the pair of its conditions. -/
def equivProd : Spec F ≃ Finset (Finset F) × Finset (Finset F) where
  toFun sp := (sp.int, sp.sat)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Specifications are ordered by inclusion of both conditions' bundles. -/
instance : PartialOrder (Spec F) := equivProd.partialOrder

theorem le_def {sp sp' : Spec F} : sp ≤ sp' ↔ sp.int ⊆ sp'.int ∧ sp.sat ⊆ sp'.sat := Iff.rfl

/-- The specification with no bundles, a head without that probe. -/
instance : OrderBot (Spec F) where
  bot := ⟨∅, ∅⟩
  bot_le _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

@[simp] theorem bot_int : (⊥ : Spec F).int = ∅ := rfl
@[simp] theorem bot_sat : (⊥ : Spec F).sat = ∅ := rfl

/-- The join of two specifications lists the bundles of either, a disjunctive probe. -/
instance [DecidableEq F] : Lattice (Spec F) := equivProd.lattice

@[simp] theorem sup_int [DecidableEq F] (sp sp' : Spec F) : (sp ⊔ sp').int = sp.int ∪ sp'.int :=
  rfl
@[simp] theorem sup_sat [DecidableEq F] (sp sp' : Spec F) : (sp ⊔ sp').sat = sp.sat ∪ sp'.sat :=
  rfl

/-- The specification whose bundles are single features, interacting with a goal that bears a
feature of `int` and satisfied by one that bears a feature of `sat`. -/
def ofFeatures (int sat : Finset F) : Spec F := ⟨int.powersetCard 1, sat.powersetCard 1⟩

/-- The state of Agree for a specification, the features copied so far and the current
interaction condition. -/
structure State (F : Type*) where
  /-- The features copied to the probe so far. -/
  copied : Finset F
  /-- The current interaction condition. -/
  int : Finset (Finset F)

variable [DecidableEq F] (sp : Spec F) (feats : α → Finset F)

/-- The features of the interaction condition a goal bears, which Agree copies from it. -/
def intFeatures (a : α) : Finset F := feats a ∩ sp.int.sup id

/-- The features of the satisfaction condition a goal bears. -/
def satFeatures (a : α) : Finset F := feats a ∩ sp.sat.sup id

/-- The probe a specification denotes over goals exposing feature sets, interacting with a goal
whose features lie in the upper set the interaction condition presents, and satisfied by one
whose features lie in the upper set the satisfaction condition presents. -/
def toProbe : Probe α where
  int a := feats a ∈ upperClosure (sp.int : Set (Finset F))
  sat a := feats a ∈ upperClosure (sp.sat : Set (Finset F))
  decInt a := decidable_of_iff (∃ m ∈ sp.int, m ⊆ feats a) (by simp [mem_upperClosure])
  decSat a := decidable_of_iff (∃ m ∈ sp.sat, m ⊆ feats a) (by simp [mem_upperClosure])

@[simp] theorem toProbe_int (a : α) :
    (sp.toProbe feats).int a ↔ ∃ m ∈ sp.int, m ⊆ feats a := by
  simp [toProbe, mem_upperClosure]

@[simp] theorem toProbe_sat (a : α) :
    (sp.toProbe feats).sat a ↔ ∃ m ∈ sp.sat, m ⊆ feats a := by
  simp [toProbe, mem_upperClosure]

variable {sp feats}

/-- The join interacts with a goal iff either specification does. -/
theorem sup_toProbe_int {sp' : Spec F} {a : α} :
    ((sp ⊔ sp').toProbe feats).int a ↔ (sp.toProbe feats).int a ∨ (sp'.toProbe feats).int a := by
  simp [or_and_right, exists_or]

/-- The join is satisfied by a goal iff either specification is. -/
theorem sup_toProbe_sat {sp' : Spec F} {a : α} :
    ((sp ⊔ sp').toProbe feats).sat a ↔ (sp.toProbe feats).sat a ∨ (sp'.toProbe feats).sat a := by
  simp [or_and_right, exists_or]

variable {int sat : Finset F} {a : α}

@[simp] theorem ofFeatures_toProbe_int :
    ((ofFeatures int sat).toProbe feats).int a ↔ (feats a ∩ int).Nonempty := by
  simp [ofFeatures, Finset.powersetCard_one, Finset.Nonempty, and_comm]

@[simp] theorem ofFeatures_toProbe_sat :
    ((ofFeatures int sat).toProbe feats).sat a ↔ (feats a ∩ sat).Nonempty := by
  simp [ofFeatures, Finset.powersetCard_one, Finset.Nonempty, and_comm]

@[simp] theorem ofFeatures_intFeatures :
    (ofFeatures int sat).intFeatures feats a = feats a ∩ int := by
  simp [intFeatures, ofFeatures, Finset.powersetCard_one, Finset.sup_map]

@[simp] theorem ofFeatures_satFeatures :
    (ofFeatures int sat).satFeatures feats a = feats a ∩ sat := by
  simp [satFeatures, ofFeatures, Finset.powersetCard_one, Finset.sup_map]

section Geometry

variable [Preorder F] [LocallyFiniteOrderTop F]

/-- The specification `[INT:f, SAT:g]` over a feature geometry, in which a feature is below the
features it dominates: interaction with `f` copies `f` and every feature it dominates, (8a) of
[deal-2024], and satisfaction is bearing `g`. -/
def ofGeometry (f g : F) : Spec F := ofFeatures (Finset.Ici f) {g}

/-- The relativized probe `[INT:f, SAT:f]`. -/
abbrev relativized (f : F) : Spec F := ofGeometry f f

variable {f g : F}

@[simp] theorem ofGeometry_intFeatures :
    (ofGeometry f g).intFeatures feats a = feats a ∩ Finset.Ici f :=
  ofFeatures_intFeatures

/-- When a goal bears every feature dominating one it bears, as in a privative geometry, it
interacts with `[INT:f]` exactly when it bears `f`. -/
theorem ofGeometry_toProbe_int_iff (hc : ∀ x ∈ feats a, ∀ y ≤ x, y ∈ feats a) :
    ((ofGeometry f g).toProbe feats).int a ↔ f ∈ feats a := by
  rw [ofGeometry, ofFeatures_toProbe_int]
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun hf ↦ ⟨f, Finset.mem_inter.2 ⟨hf, Finset.mem_Ici.2 le_rfl⟩⟩⟩
  rw [Finset.mem_inter, Finset.mem_Ici] at hx
  exact hc x hx.1 f hx.2

end Geometry

variable (sp feats)

section Dynamic

variable [Preorder F] [LocallyFiniteOrderTop F] (dyn : Finset F)

/-- After a goal, the interaction condition becomes any one of the features dominated by every
feature of the goal marked for dynamic interaction, and stays unchanged if the goal bears none. -/
def dynamicUpdate (a : α) (int : Finset (Finset F)) : Finset (Finset F) :=
  if h : (feats a ∩ dyn).Nonempty then ((feats a ∩ dyn).inf' h Finset.Ici).powersetCard 1 else int

/-- Agree (30) of [deal-2025a] over goals exposing feature sets, `dyn` the features marked for
dynamic interaction. The probe interacts by the current interaction condition, which starts as
`sp.int`. -/
def agree (goals : List α) : Result α (State F) :=
  Dynamic.agree (fun st ↦ ({ sp with int := st.int } : Spec F).toProbe feats)
    (fun a st ↦ ⟨st.copied ∪ (feats a ∩ st.int.sup id), st.int⟩)
    (fun a st ↦ ⟨st.copied, dynamicUpdate feats dyn a st.int⟩) ⟨∅, sp.int⟩ goals

/-- A specification halts on the first goal bearing a satisfaction feature, whatever the dynamic
interaction. -/
theorem agree_satisfier (goals : List α) :
    (sp.agree feats dyn goals).satisfier = (sp.toProbe feats).search goals :=
  Dynamic.agree_satisfier (q := sp.toProbe feats) fun _ ↦ rfl

/-- Dynamic interaction narrows the interaction condition to the features that a dynamic feature
of the goal dominates. -/
theorem subset_Ici_of_mem_dynamicUpdate {a : α} {x : F} (hx : x ∈ feats a ∩ dyn)
    {int : Finset (Finset F)} {m : Finset F} (hm : m ∈ dynamicUpdate feats dyn a int) :
    m ⊆ Finset.Ici x := by
  unfold dynamicUpdate at hm
  split at hm
  · exact (Finset.mem_powersetCard.1 hm).1.trans (Finset.inf'_le _ hx)
  · exact (‹¬ (feats a ∩ dyn).Nonempty› ⟨x, hx⟩).elim

@[simp] theorem dynamicUpdate_empty (a : α) (int : Finset (Finset F)) :
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

/-- Without dynamic interaction, the features a specification copies are those of the interacting
goals it inspects, whatever their order. -/
theorem copied_agree_empty [DecidableEq α] (goals : List α) :
    (sp.agree feats ∅ goals).state.copied =
      (((sp.toProbe feats).inspected goals).filter ((sp.toProbe feats).int ·)).toFinset.sup
        (sp.intFeatures feats) := by
  rw [agree_empty]
  simpa using Probe.agree_sup_state (p := sp.toProbe feats) (s := ∅) (goals := goals)
    (sp.intFeatures feats)

theorem dynamicUpdate_eq_of_nonempty {a : α} (h : (feats a ∩ dyn).Nonempty)
    (int int' : Finset (Finset F)) :
    dynamicUpdate feats dyn a int = dynamicUpdate feats dyn a int' := by
  simp [dynamicUpdate, h]

theorem dynamicUpdate_eq_self {a : α} (h : ¬ (feats a ∩ dyn).Nonempty) (int : Finset (Finset F)) :
    dynamicUpdate feats dyn a int = int := by
  simp [dynamicUpdate, h]

/-- After a sequence of goals the interaction condition is the one the last goal bearing a dynamic
feature sets, and the initial condition if no goal bears one. -/
theorem foldl_dynamicUpdate (int : Finset (Finset F)) (l : List α) :
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
      (fun a st ↦ ⟨st.copied ∪ (feats a ∩ st.int.sup id), st.int⟩)
      (fun a st ↦ ⟨st.copied, dynamicUpdate feats dyn a st.int⟩) st goals).interacted ↔
    ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ (∀ b ∈ l₁, ¬ (sp.toProbe feats).sat b) ∧
      feats a ∈
        upperClosure (↑(l₁.foldl (fun i b ↦ dynamicUpdate feats dyn b i) st.int) : Set _) := by
  induction goals generalizing st with
  | nil => simp
  | cons x xs ih =>
    rw [Dynamic.agree_cons]
    by_cases hs : (sp.toProbe feats).sat x
    · rw [ite_eq_left (show (({ sp with int := st.int } : Spec F).toProbe feats).sat x from hs)]
      dsimp only
      constructor
      · intro ha
        split_ifs at ha with hx
        · obtain rfl := List.mem_singleton.1 ha
          exact ⟨[], xs, rfl, by simp, hx⟩
        · simp at ha
      · rintro ⟨_ | ⟨y, l₁⟩, l₂, he, hl₁, ha⟩
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          rw [ite_eq_left (show (({ sp with int := st.int } : Spec F).toProbe feats).int x from ha)]
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
        · split_ifs at ha with hx
          · obtain rfl := List.mem_singleton.1 ha
            exact ⟨[], xs, rfl, by simp, hx⟩
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
          rw [ite_eq_left (show (({ sp with int := st.int } : Spec F).toProbe feats).int x from ha)]
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
        feats a ∈
          upperClosure (↑(l₁.foldl (fun i b ↦ dynamicUpdate feats dyn b i) sp.int) : Set _) :=
  mem_interacted_iff sp feats dyn ⟨∅, sp.int⟩ goals

end Dynamic

end Spec

end Probe

end Minimalist
