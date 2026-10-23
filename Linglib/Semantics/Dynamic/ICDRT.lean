module

public import Linglib.Semantics.Dynamic.RegisterStructure

/-!
# Intensional CDRT

Muskens's compositional DRT with intensional discourse referents. An individual dref is
an individual concept, a function from worlds to individuals or the universal falsifier ⋆
(type `s(we)`); a propositional dref is a set of worlds (type `s(wt)`) and stores the local
context of some embedded content. This is the flat update of Stone and
Brasoveanu in Hofmann's formulation: a discourse state is a single assignment,
updated relationally, and an individual dref has a referent only at the worlds of its local
context.

A state has two sorts of registers, `IVar` and `PVar`, each with its `RegisterStructure`, so
the variable update `[δ]` is CDRT's `Update.randomAssign` at either sort and a DRS
`[δ | C]` is `Update.box {δ} C`. Over these sit the relative variable update `[φ : υ]`,
after which `υ` has a referent at exactly the `φ`-worlds, predication relative to a local
context, local entailment, and maximization over a propositional dref, CDRT's `Update.maxAt`.

## Main definitions

* `ICDRT.State`: individual concepts for `IVar`s and propositions for `PVar`s.
* `ICDRT.relUpdate`: relative variable update `[φ : υ]`.
* `ICDRT.pred`: predication `R_φ(υ)` relative to a local context.
* `ICDRT.incl`, `ICDRT.eqCompl`: the conditions `φ₁ ⋐ φ₂` and `φ₁ ≡ φ̄₂`.
* `ICDRT.localEntailment`: `υ` has a referent throughout `φ`.

## Main results

* `ICDRT.mem_randomAssign_indiv`, `ICDRT.mem_randomAssign_prop`: a variable update changes one
  register of one sort and nothing else.
* `ICDRT.mem_localEntailment_of_mem_pred`: predication entails local entailment, since ⋆
  satisfies no relation.
* `ICDRT.mem_localEntailment_iff_of_relUpdate`: after `[φ : υ]`, `υ` is entailed in a local
  context exactly when that context lies within `φ`.
* `ICDRT.mem_maxAt_prop`: CDRT's `maxAt` at a propositional dref is maximization `max_φ`.

## Implementation notes

⋆ is `none`. The typed drefs are two register sorts rather than one register carrier, since a
`RegisterStructure` has one value type. The relative variable update is Hofmann's
biconditional form; Stone's has only the implication from `φ`-worlds to referents.

## References

* [muskens-1996]
* [stone-1999]
* [brasoveanu-2006]
* [hofmann-2025]
-/

@[expose] public section

namespace ICDRT

open DynamicSemantics Update SetRel

/-- A propositional variable, the name of a propositional dref. -/
structure PVar where
  idx : ℕ
  deriving DecidableEq, Repr

/-- An individual variable, the name of an individual dref. -/
structure IVar where
  idx : ℕ
  deriving DecidableEq, Repr

/-- A discourse state assigns an individual concept to each individual dref and a proposition to
each propositional dref. An individual dref is `none`, the falsifier ⋆, at the worlds where it
has no referent. -/
@[ext] structure State (W E : Type*) where
  indiv : IVar → W → Option E
  prop : PVar → Set W

variable {W E : Type*}

namespace State

/-- Reassign an individual dref. -/
def updateIndiv (g : State W E) (v : IVar) (e : W → Option E) : State W E :=
  { g with indiv := Function.update g.indiv v e }

/-- Reassign a propositional dref. -/
def updateProp (g : State W E) (p : PVar) (s : Set W) : State W E :=
  { g with prop := Function.update g.prop p s }

@[simp] theorem updateProp_prop_self (g : State W E) (p : PVar) (s : Set W) :
    (g.updateProp p s).prop p = s := by
  simp [updateProp]

@[simp] theorem updateProp_prop_of_ne (g : State W E) {p q : PVar} (h : q ≠ p) (s : Set W) :
    (g.updateProp p s).prop q = g.prop q := by
  simp [updateProp, Function.update_of_ne h]

@[simp] theorem updateProp_indiv (g : State W E) (p : PVar) (s : Set W) :
    (g.updateProp p s).indiv = g.indiv := rfl

@[simp] theorem updateIndiv_prop (g : State W E) (v : IVar) (e : W → Option E) :
    (g.updateIndiv v e).prop = g.prop := rfl

@[simp] theorem updateIndiv_indiv_self (g : State W E) (v : IVar) (e : W → Option E) :
    (g.updateIndiv v e).indiv v = e := by
  simp [updateIndiv]

@[simp] theorem updateIndiv_indiv_of_ne (g : State W E) {v u : IVar} (h : u ≠ v)
    (e : W → Option E) : (g.updateIndiv v e).indiv u = g.indiv u := by
  simp [updateIndiv, Function.update_of_ne h]

end State

/-! ### Registers and variable update -/

/-- Individual drefs are registers holding individual concepts. -/
instance : RegisterStructure IVar (State W E) (W → Option E) where
  val v i := i.indiv v
  extend i v e := i.updateIndiv v e
  val_extend_self _ _ _ := State.updateIndiv_indiv_self ..
  val_extend_of_ne _ _ _ _ h := State.updateIndiv_indiv_of_ne _ h _
  extend_eq_self _ _ := by simp [State.updateIndiv]
  extend_idem _ _ _ _ := by simp [State.updateIndiv]
  extend_comm _ _ _ h _ _ := by simp [State.updateIndiv, Function.update_comm h]

/-- Propositional drefs are registers holding propositions. -/
instance : RegisterStructure PVar (State W E) (Set W) where
  val p i := i.prop p
  extend i p s := i.updateProp p s
  val_extend_self _ _ _ := State.updateProp_prop_self ..
  val_extend_of_ne _ _ _ _ h := State.updateProp_prop_of_ne _ h _
  extend_eq_self _ _ := by simp [State.updateProp]
  extend_idem _ _ _ _ := by simp [State.updateProp]
  extend_comm _ _ _ h _ _ := by simp [State.updateProp, Function.update_comm h]

variable {i j : State W E} {v u : IVar} {φ φ' ψ : PVar}

@[simp] theorem val_ivar (i : State W E) (v : IVar) : RegisterStructure.val v i = i.indiv v := rfl

@[simp] theorem val_pvar (i : State W E) (p : PVar) : RegisterStructure.val p i = i.prop p := rfl

theorem updateIndiv_mem_randomAssign (i : State W E) (v : IVar) (e : W → Option E) :
    i ~[randomAssign v] i.updateIndiv v e :=
  ⟨e, rfl⟩

theorem updateProp_mem_randomAssign (i : State W E) (p : PVar) (s : Set W) :
    i ~[randomAssign p] i.updateProp p s :=
  ⟨s, rfl⟩

/-- The update `[υ]` relates `i` to the states `j` that differ from it at most in the value of
`υ` ([hofmann-2025] App. B (9a)). -/
theorem mem_randomAssign_indiv :
    i ~[randomAssign v] j ↔ (∀ p, j.prop p = i.prop p) ∧ ∀ u, u ≠ v → j.indiv u = i.indiv u := by
  refine ⟨?_, fun ⟨hp, hu⟩ ↦ ⟨j.indiv v, ?_⟩⟩
  · rintro ⟨e, rfl⟩
    exact ⟨fun _ ↦ rfl, fun _ hu ↦ State.updateIndiv_indiv_of_ne _ hu _⟩
  · ext1
    · funext u
      by_cases h : u = v
      · subst h; exact (State.updateIndiv_indiv_self ..).symm
      · exact (hu u h).trans (State.updateIndiv_indiv_of_ne _ h _).symm
    · funext p; exact hp p

/-- The update `[φ]` relates `i` to the states `j` that differ from it at most in the value of
`φ` ([hofmann-2025] App. B (9a)). -/
theorem mem_randomAssign_prop :
    i ~[randomAssign φ] j ↔ (∀ q, q ≠ φ → j.prop q = i.prop q) ∧ ∀ u, j.indiv u = i.indiv u := by
  refine ⟨?_, fun ⟨hq, hu⟩ ↦ ⟨j.prop φ, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact ⟨fun _ hq ↦ State.updateProp_prop_of_ne _ hq _, fun _ ↦ rfl⟩
  · ext1
    · funext u; exact hu u
    · funext q
      by_cases h : q = φ
      · subst h; exact (State.updateProp_prop_self ..).symm
      · exact (hq q h).trans (State.updateProp_prop_of_ne _ h _).symm

theorem _root_.DynamicSemantics.Update.Fixes.prop_eq {D : Update (State W E)} (h : Fixes φ D)
    (hD : i ~[D] j) : j.prop φ = i.prop φ :=
  h i j hD

theorem updateProp_mem_box {C : Condition (State W E)} (p : PVar) (s : Set W)
    (h : i.updateProp p s ∈ C) : i ~[box {p} C] i.updateProp p s :=
  mem_box_singleton.mpr ⟨updateProp_mem_randomAssign i p s, h⟩

theorem fixes_randomAssign_ivar (φ : PVar) (v : IVar) :
    Fixes φ (randomAssign (S := State W E) v) :=
  fun _ _ h ↦ (mem_randomAssign_indiv.mp h).1 φ

/-- Maximization `max_φ(D)` over a propositional dref ([hofmann-2025] (40)) keeps the outputs of `D`
at which no other output gives `φ` a proper superset. -/
theorem mem_maxAt_prop {D : Update (State W E)} :
    i ~[maxAt φ D] j ↔ i ~[D] j ∧ ∀ k, i ~[D] k → ¬j.prop φ ⊂ k.prop φ :=
  Iff.rfl

/-! ### Relative variable update -/

/-- The relative variable update `[φ : υ]` ([hofmann-2025] (25), App. B (9b)) updates `υ` so
that it has a referent at all and only the `φ`-worlds. -/
def relUpdate (φ : PVar) (v : IVar) : Update (State W E) :=
  box {v} {j | ∀ w, w ∈ j.prop φ ↔ j.indiv v w ≠ none}

theorem mem_relUpdate :
    i ~[relUpdate φ v] j ↔ i ~[randomAssign v] j ∧ ∀ w, w ∈ j.prop φ ↔ j.indiv v w ≠ none :=
  mem_box_singleton

theorem updateIndiv_mem_relUpdate (e : W → Option E) (h : ∀ w, w ∈ i.prop φ ↔ e w ≠ none) :
    i ~[relUpdate φ v] i.updateIndiv v e :=
  mem_relUpdate.mpr ⟨updateIndiv_mem_randomAssign i v e, by simpa using h⟩

theorem fixes_relUpdate (ψ φ : PVar) (v : IVar) : Fixes ψ (relUpdate (W := W) (E := E) φ v) := by
  rw [relUpdate, box_singleton]
  exact (fixes_randomAssign_ivar ψ v).comp (fixes_test ψ _)

/-! ### Conditions -/

/-- Predication `R_φ(υ)` ([hofmann-2025] (27), App. B (7a)) holds if `R` holds of `υ`'s
referent at every world of the local context `φ`; ⋆ satisfies no relation. -/
def pred (R : E → W → Prop) (φ : PVar) (v : IVar) : Condition (State W E) :=
  {i | ∀ w ∈ i.prop φ,
    match i.indiv v w with
    | some e => R e w
    | none => False}

/-- Inclusion `φ₁ ⋐ φ₂` (App. B (7c)). -/
def incl (φ₁ φ₂ : PVar) : Condition (State W E) := {i | i.prop φ₁ ⊆ i.prop φ₂}

/-- `φ₁ ≡ φ̄₂` (App. B (7b), (8a)), the condition negation places on its context. -/
def eqCompl (φ₁ φ₂ : PVar) : Condition (State W E) := {i | i.prop φ₁ = (i.prop φ₂)ᶜ}

/-- A dref `υ` is entailed in the local context `φ` ([hofmann-2025] (28)) if it has a referent
at every `φ`-world. -/
def localEntailment (φ : PVar) (v : IVar) : Condition (State W E) :=
  {i | ∀ w ∈ i.prop φ, i.indiv v w ≠ none}

/-- ⋆ falsifies predication ((29a)). -/
theorem not_mem_pred_of_eq_none {R : E → W → Prop} {w : W} (hw : w ∈ i.prop φ)
    (h : i.indiv v w = none) : i ∉ pred R φ v := fun hp ↦ by
  simpa [h] using hp w hw

/-- Predication entails local entailment ((29b)), since a referent satisfying `R` is not ⋆. -/
theorem mem_localEntailment_of_mem_pred {R : E → W → Prop} (h : i ∈ pred R φ v) :
    i ∈ localEntailment φ v := fun _ hw hnone ↦ not_mem_pred_of_eq_none hw hnone h

/-- After `[φ : υ]`, `υ` is entailed in a local context exactly when the context lies within
`φ`, the subset requirement of [hofmann-2025] (39). -/
theorem mem_localEntailment_iff_of_relUpdate (h : i ~[relUpdate φ v] j) :
    j ∈ localEntailment ψ v ↔ j.prop ψ ⊆ j.prop φ :=
  let hj := (mem_relUpdate.mp h).2
  ⟨fun hl _ hw ↦ (hj _).2 (hl _ hw), fun hs _ hw ↦ (hj _).1 (hs hw)⟩

end ICDRT
