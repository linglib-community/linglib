module

public import Linglib.Semantics.Dynamic.RegisterStructure
public import Mathlib.Data.PFun

/-!
# Intensional CDRT

Muskens's compositional DRT with intensional discourse referents. An individual dref is
an individual concept, a partial function from worlds to individuals that is undefined where the
paper's universal falsifier ⋆ would be its value (type `s(we)`); a propositional dref is a set of
worlds (type `s(wt)`) and stores the local context of some embedded content. This is the flat update
of Stone and Brasoveanu in Hofmann's formulation: a discourse state is a single assignment, updated
relationally, and an individual dref has a referent only at the worlds of its local context.

A state has two sorts of registers, `IVar` and `PVar`, each with its `RegisterStructure`, so
the variable update `[δ]` is CDRT's `Update.randomAssign` at either sort and a DRS
`[δ | C]` is `Update.box {δ} C`. Over these sit the relative variable update `[φ : υ]`,
after which `υ` has a referent at exactly the `φ`-worlds, predication relative to a local
context, and local entailment.

## Main definitions

* `ICDRT.State`: individual concepts for `IVar`s and propositions for `PVar`s.
* `ICDRT.sat`: the worlds where the referent of an individual concept satisfies a relation.
* `ICDRT.relUpdate`: relative variable update `[φ : υ]`.
* `ICDRT.predication`: predication `R_φ(υ)` relative to a local context.
* `ICDRT.incl`, `ICDRT.eqCompl`: the conditions `φ₁ ⋐ φ₂` and `φ₁ ≡ φ̄₂`.
* `ICDRT.localEntailment`: `υ` has a referent throughout `φ`.
* `ICDRT.IsWitness`: a possible value of the dref of an indefinite in a local context.

## Main results

* `ICDRT.mem_randomAssign_indiv`, `ICDRT.mem_randomAssign_prop`: a variable update changes one
  register of one sort and nothing else.
* `ICDRT.mem_localEntailment_of_mem_predication`: predication entails local entailment, since ⋆
  satisfies no relation.
* `ICDRT.mem_localEntailment_iff`: where `υ` has a referent at exactly the `φ`-worlds, it is
  entailed in a local context exactly when that context lies within `φ`.
* `ICDRT.exists_isWitness_sat`: a witness can choose an `S` wherever its context has an `R` that is
  one.

## Implementation notes

⋆ is undefinedness of the partial function. The typed drefs are two register sorts rather than one
register carrier, since a `RegisterStructure` has one value type. The relative variable update is
Hofmann's biconditional form; Stone's has only the implication from `φ`-worlds to referents.
Maximization over a propositional dref is `Update.maxInput`, since the dref is introduced outside
the operator (`Studies/Hofmann2025.lean`).

## References

* [muskens-1996]
* [stone-1999]
* [brasoveanu-2007]
* [hofmann-2025]
-/

@[expose] public section

namespace ICDRT

open DynamicSemantics Update SetRel

/-- A propositional variable, the name of a propositional dref. -/
structure PVar where
  /-- The index of the variable. -/
  idx : ℕ
  deriving DecidableEq, Repr

/-- An individual variable, the name of an individual dref. -/
structure IVar where
  /-- The index of the variable. -/
  idx : ℕ
  deriving DecidableEq, Repr

variable {W E : Type*}

/-- The worlds where the referent of an individual concept satisfies `R`. ⋆ satisfies no relation
([hofmann-2025] fn. 9). -/
def sat (R : E → W → Prop) (e : W →. E) : Set W := {w | ∃ a ∈ e w, R a w}

theorem sat_subset_dom (R : E → W → Prop) (e : W →. E) : sat R e ⊆ e.Dom :=
  fun _ ⟨_, ha, _⟩ ↦ Part.dom_iff_mem.2 ⟨_, ha⟩

@[simp] theorem sat_const (R : E → W → Prop) (a : E) :
    sat R (fun _ ↦ Part.some a : W →. E) = {w | R a w} := by
  simp [sat]

/-- A discourse state assigns an individual concept to each individual dref and a proposition to
each propositional dref. -/
@[ext] structure State (W E : Type*) where
  /-- The individual concept of an individual dref. -/
  indiv : IVar → W →. E
  /-- The proposition of a propositional dref. -/
  prop : PVar → Set W

namespace State

/-- Reassign an individual dref. -/
def updateIndiv (g : State W E) (v : IVar) (e : W →. E) : State W E :=
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

@[simp] theorem updateProp_self (g : State W E) (p : PVar) : g.updateProp p (g.prop p) = g := by
  simp [updateProp]

@[simp] theorem updateProp_updateProp_self (g : State W E) (p : PVar) (s t : Set W) :
    (g.updateProp p s).updateProp p t = g.updateProp p t := by
  simp [updateProp]

@[simp] theorem updateIndiv_prop (g : State W E) (v : IVar) (e : W →. E) :
    (g.updateIndiv v e).prop = g.prop := rfl

@[simp] theorem updateIndiv_indiv_self (g : State W E) (v : IVar) (e : W →. E) :
    (g.updateIndiv v e).indiv v = e := by
  simp [updateIndiv]

@[simp] theorem updateIndiv_indiv_of_ne (g : State W E) {v u : IVar} (h : u ≠ v)
    (e : W →. E) : (g.updateIndiv v e).indiv u = g.indiv u := by
  simp [updateIndiv, Function.update_of_ne h]

/-- The null assignment holds no information: no dref has a referent and every proposition is the
trivial one ([hofmann-2025] (32)). -/
def null : State W E := ⟨fun _ _ ↦ Part.none, fun _ ↦ Set.univ⟩

end State

/-! ### Registers and variable update -/

/-- Individual drefs are registers holding individual concepts. -/
instance : RegisterStructure IVar (State W E) (W →. E) where
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

@[simp] theorem extend_ivar (i : State W E) (v : IVar) (e : W →. E) :
    RegisterStructure.extend i v e = i.updateIndiv v e := rfl

@[simp] theorem extend_pvar (i : State W E) (p : PVar) (s : Set W) :
    RegisterStructure.extend i p s = i.updateProp p s := rfl

/-- The update `[υ]` relates `i` to the states `j` that differ from it at most in the value of
`υ` ([hofmann-2025] App. B (9a)). -/
theorem mem_randomAssign_indiv :
    i ~[randomAssign v] j ↔ (∀ p, j.prop p = i.prop p) ∧ ∀ u, u ≠ v → j.indiv u = i.indiv u := by
  refine ⟨?_, fun ⟨hp, hu⟩ ↦ ⟨j.indiv v, ?_⟩⟩
  · rintro ⟨e, rfl⟩
    exact ⟨fun _ ↦ rfl, fun _ hu ↦ State.updateIndiv_indiv_of_ne _ hu _⟩
  · exact State.ext (Function.update_eq_iff.2 ⟨rfl, fun u h ↦ (hu u h).symm⟩).symm (funext hp)

/-- The update `[φ]` relates `i` to the states `j` that differ from it at most in the value of
`φ` ([hofmann-2025] App. B (9a)). -/
theorem mem_randomAssign_prop :
    i ~[randomAssign φ] j ↔ (∀ q, q ≠ φ → j.prop q = i.prop q) ∧ ∀ u, j.indiv u = i.indiv u := by
  refine ⟨?_, fun ⟨hq, hu⟩ ↦ ⟨j.prop φ, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact ⟨fun _ hq ↦ State.updateProp_prop_of_ne _ hq _, fun _ ↦ rfl⟩
  · exact State.ext (funext hu) (Function.update_eq_iff.2 ⟨rfl, fun q h ↦ (hq q h).symm⟩).symm

theorem mem_box_pair_comp {C : Condition (State W E)} {D : Update (State W E)} :
    i ~[box {φ, ψ} C ○ D] j ↔ ∃ s t, (i.updateProp φ s).updateProp ψ t ∈ C ∧
      (i.updateProp φ s).updateProp ψ t ~[D] j := by
  rw [box_insert, comp_assoc, ← dexists, mem_dexists]
  simp only [Update.mem_box_singleton_comp, extend_pvar]

/-! ### Relative variable update -/

/-- The relative variable update `[φ : υ]` ([hofmann-2025] (25), App. B (9b)) updates `υ` so
that it has a referent at all and only the `φ`-worlds. -/
def relUpdate (φ : PVar) (v : IVar) : Update (State W E) :=
  box {v} {j | j.prop φ = (j.indiv v).Dom}

theorem mem_relUpdate :
    i ~[relUpdate φ v] j ↔ i ~[randomAssign v] j ∧ j.prop φ = (j.indiv v).Dom :=
  mem_box_singleton

theorem updateIndiv_mem_relUpdate {e : W →. E} (h : i.prop φ = e.Dom) :
    i ~[relUpdate φ v] i.updateIndiv v e :=
  mem_relUpdate.mpr ⟨⟨e, rfl⟩, by simpa using h⟩

theorem fixes_relUpdate (ψ φ : PVar) (v : IVar) : Fixes ψ (relUpdate (W := W) (E := E) φ v) :=
  fun _ _ h ↦ by
    obtain ⟨⟨e, rfl⟩, -⟩ := mem_relUpdate.mp h
    rfl

/-! ### Conditions -/

/-- Predication `R_φ(υ)` ([hofmann-2025] (27), App. B (7a)) holds if `R` holds of `υ`'s
referent at every world of the local context `φ`; ⋆ satisfies no relation. -/
def predication (R : E → W → Prop) (φ : PVar) (v : IVar) : Condition (State W E) :=
  {i | i.prop φ ⊆ sat R (i.indiv v)}

/-- Inclusion `φ₁ ⋐ φ₂` (App. B (7c)). -/
def incl (φ₁ φ₂ : PVar) : Condition (State W E) := {i | i.prop φ₁ ⊆ i.prop φ₂}

/-- `φ₁ ≡ φ̄₂` (App. B (7b), (8a)), the condition negation places on its context. -/
def eqCompl (φ₁ φ₂ : PVar) : Condition (State W E) := {i | i.prop φ₁ = (i.prop φ₂)ᶜ}

/-- A dref `υ` is entailed in the local context `φ` ([hofmann-2025] (28)) if it has a referent
at every `φ`-world. -/
def localEntailment (φ : PVar) (v : IVar) : Condition (State W E) :=
  {i | i.prop φ ⊆ (i.indiv v).Dom}

@[simp] theorem mem_predication {R : E → W → Prop} :
    i ∈ predication R φ v ↔ i.prop φ ⊆ sat R (i.indiv v) := Iff.rfl

@[simp] theorem mem_incl : i ∈ incl φ φ' ↔ i.prop φ ⊆ i.prop φ' := Iff.rfl

@[simp] theorem mem_eqCompl : i ∈ eqCompl φ φ' ↔ i.prop φ = (i.prop φ')ᶜ := Iff.rfl

@[simp] theorem mem_localEntailment : i ∈ localEntailment φ v ↔ i.prop φ ⊆ (i.indiv v).Dom :=
  Iff.rfl

/-- Predication entails local entailment ((29)), since a referent satisfying `R` is not ⋆. -/
theorem mem_localEntailment_of_mem_predication {R : E → W → Prop}
    (h : i ∈ predication R φ v) :
    i ∈ localEntailment φ v :=
  Set.Subset.trans h (sat_subset_dom R _)

/-- Where `υ` has a referent at exactly the `φ`-worlds, as after `[φ : υ]`, it is entailed in a
local context exactly when the context lies within `φ`, the subset requirement of
[hofmann-2025] (39). -/
theorem mem_localEntailment_iff (h : j.prop φ = (j.indiv v).Dom) :
    j ∈ localEntailment ψ v ↔ j.prop ψ ⊆ j.prop φ := by
  rw [mem_localEntailment, h]

/-! ### Witnesses -/

variable {R S : E → W → Prop}

/-- The worlds where some individual satisfies `R`. -/
def witnessed (R : E → W → Prop) : Set W := {w | ∃ a, R a w}

/-- `e` is a possible value of the dref of an indefinite with restrictor `R` in the local context
`s`: it refers at exactly the `s`-worlds (25), and to an `R` (27). -/
def IsWitness (R : E → W → Prop) (s : Set W) (e : W →. E) : Prop :=
  s = e.Dom ∧ s ⊆ sat R e

theorem witnessed_inf_subset_left : witnessed (R ⊓ S) ⊆ witnessed R :=
  fun _ ⟨a, hR, _⟩ ↦ ⟨a, hR⟩

theorem IsWitness.subset_witnessed {s : Set W} {e : W →. E} (h : IsWitness R s e) :
    s ⊆ witnessed R :=
  fun _ hw ↦ let ⟨a, _, hR⟩ := h.2 hw; ⟨a, hR⟩

theorem IsWitness.sat_subset {s : Set W} {e : W →. E} (h : IsWitness R s e) :
    sat S e ⊆ s ∩ witnessed (R ⊓ S) := by
  rintro w ⟨a, ha, hS⟩
  have hs : w ∈ s := h.1 ▸ sat_subset_dom S e ⟨a, ha, hS⟩
  obtain ⟨b, hb, hR⟩ := h.2 hs
  obtain rfl : a = b := Part.mem_unique ha hb
  exact ⟨hs, a, hR, hS⟩

/-- A witness can choose an `S` wherever the context has an `R` that is one. -/
theorem exists_isWitness_sat {s : Set W} (hs : s ⊆ witnessed R) (S : E → W → Prop) :
    ∃ e, IsWitness R s e ∧ sat S e = s ∩ witnessed (R ⊓ S) := by
  have h (w : W) (hw : w ∈ s) : ∃ a, R a w ∧ (w ∈ witnessed (R ⊓ S) → S a w) := by
    by_cases hc : w ∈ witnessed (R ⊓ S)
    · exact hc.imp fun a ha ↦ ⟨ha.1, fun _ ↦ ha.2⟩
    · exact (hs hw).imp fun a ha ↦ ⟨ha, hc.elim⟩
  choose f hR hS using h
  have hW : IsWitness R s (fun w ↦ ⟨w ∈ s, f w⟩) := ⟨rfl, fun w hw ↦ ⟨_, ⟨hw, rfl⟩, hR w hw⟩⟩
  exact ⟨_, hW, hW.sat_subset.antisymm fun w ⟨hw, hc⟩ ↦ ⟨_, ⟨hw, rfl⟩, hS w hw hc⟩⟩

theorem exists_isWitness_sat_eq (R S : E → W → Prop) :
    ∃ e, IsWitness R (witnessed R) e ∧ sat S e = witnessed (R ⊓ S) := by
  obtain ⟨e, he, hs⟩ := exists_isWitness_sat (subset_refl (witnessed R)) S
  exact ⟨e, he, by rw [hs, Set.inter_eq_right.mpr witnessed_inf_subset_left]⟩

theorem exists_isWitness_subset_sat_iff {s : Set W} :
    (∃ e, IsWitness R (witnessed R) e ∧ s ⊆ sat S e) ↔ s ⊆ witnessed (R ⊓ S) := by
  refine ⟨fun ⟨e, he, hs⟩ ↦ hs.trans (he.sat_subset.trans Set.inter_subset_right), fun hs ↦ ?_⟩
  obtain ⟨e, he, h⟩ := exists_isWitness_sat_eq R S
  exact ⟨e, he, h ▸ hs⟩

end ICDRT
