module

public import Linglib.Semantics.Aspect.SubintervalProperty
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Data.Part

/-!
# Zhao (2025): Cross-Linguistic and Cross-Domain Temporal Expressions

Zhao's dissertation analyzes the Mandarin particles *le*, *méi-yǒu* and *guò*, which occur both with
verbs, locating an event in time, and in comparatives, locating a degree on a scale. Temporal *le*
rejects a stative predicate unless it has a duration argument, degree *le* rejects a comparative
unless it has a measure phrase, and *méi-yǒu* mirrors both. Verbal projections denote quantifiers
over events, an event has a trace on the timeline or on a degree scale, and the licensing condition
is Atomic Distributivity: whenever the quantifier applies to the events with a trace, it applies to
those with any subinterval of it as trace. *Le* is defined only of a quantifier that fails Atomic
Distributivity, so the bare stative and the bare comparative are presupposition failures, which a
duration or a measure phrase repairs.

## Main definitions

* `EvQuant`: a quantifier over events.
* `AtomDist`: Atomic Distributivity.
* `le`: the particle *le*.
* `meiyou`: the particle *méi-yǒu*.

## Implementation notes

Times and degrees are the points of a linear order, traces its closed intervals, and a point is the
interval `NonemptyInterval.pure`; the dissertation also admits non-convex sums of points, which its
analyses do not use. The norm of (4.2.2) is defined only on proper intervals, so a duration argument
is a positive `NonemptyInterval.length`. The particles take the measurement `μ_α(a)` of their
evaluation argument as a point. *Le* is commonly called a perfective marker; the dissertation strips
its temporal content down to precedence, which is the relation `Aspect` assigns to the perfect,
`le_get_iff_perfect`. The first part of the dissertation, the ⌜then⌝-present puzzle, is joint work
with Tsilia, formalized in `Studies/TsiliaZhao2026.lean`.

The library takes states and activities alike to have the subinterval property; here an activity
fails it because of its minimal parts, (5.41), which is what lets *le* attach to activities.

## References

* [zhao-2025]
* [champollion-2015]
* [bennett-partee-1972]
* [tsilia-zhao-2026]
-/

@[expose] public section

namespace Zhao2025

open Event (τ)

open Set

variable {E α : Type*}

/-! ### Atomic Distributivity (chapter 5) -/

/-- A verbal projection denotes a quantifier over events, as in [champollion-2015]. -/
abbrev EvQuant (E : Type*) := (E → Prop) → Prop

/-- `EvQuant.ofPred P` is the existential quantifier over the events of `P`, the shape of (5.37). -/
def EvQuant.ofPred (P : E → Prop) : EvQuant E := fun f ↦ ∃ e, P e ∧ f e

section Preorder

variable [Preorder α] {τ : E → NonemptyInterval α} {P : E → Prop}

/-- Atomic Distributivity along the trace `τ`, (5.83), holds when, whenever the quantifier applies
to the events with trace `i`, it applies to the events with trace `i'` for each
subinterval `i'` of `i`. -/
def AtomDist (τ : E → NonemptyInterval α) (V : EvQuant E) : Prop :=
  ∀ i, V (τ · = i) → ∀ i' ≤ i, V (τ · = i')

theorem atomDist_ofPred_iff : AtomDist τ (.ofPred P) ↔ IsLowerSet (τ '' {e | P e}) :=
  ⟨fun h _ _ hba ⟨e, he, hi⟩ ↦ h _ ⟨e, he, hi⟩ _ hba, fun h _ ⟨e, he, hi⟩ _ hi' ↦
    h hi' ⟨e, he, hi⟩⟩

theorem atomDist_ofPred_mem (hτ : Function.Surjective τ) {S : Set (NonemptyInterval α)}
    (hS : IsLowerSet S) : AtomDist τ (.ofPred (τ · ∈ S)) := by
  rw [atomDist_ofPred_iff, ← preimage, image_preimage_eq S hτ]
  exact hS

-- (5.38)
theorem atomDist_ofPred_le (hτ : Function.Surjective τ) (I : NonemptyInterval α) :
    AtomDist τ (.ofPred (τ · ≤ I)) :=
  atomDist_ofPred_mem hτ (isLowerSet_Iic I)

-- (5.53)
theorem atomDist_ofPred_lt_fst (hτ : Function.Surjective τ) (m : α) :
    AtomDist τ (.ofPred fun e ↦ m < (τ e).fst) :=
  atomDist_ofPred_mem (S := {i | m < i.fst}) hτ fun _ _ hba ha ↦
    ha.trans_le (NonemptyInterval.le_def.1 hba).1

/-- A description with an event, none of whose events has a point trace, is not atomically
distributive, as for the non-stative classes of (5.39)–(5.41). -/
theorem not_atomDist_ofPred (hne : ∃ e, P e) (hP : ∀ e, P e → ¬ (τ e).IsPoint) :
    ¬ AtomDist τ (.ofPred P) := by
  obtain ⟨e, he⟩ := hne
  intro h
  obtain ⟨e', he', hτ⟩ := h _ ⟨e, he, rfl⟩ (.pure (τ e).fst)
    (NonemptyInterval.le_def.2 ⟨le_rfl, (τ e).fst_le_snd⟩)
  exact hP e' he' (hτ ▸ rfl)

/-- An event surpasses when its trace properly contains the measurement of its theme, (6.45). -/
def Surpasses (τ : E → NonemptyInterval α) (θ : E → α) (e : E) : Prop :=
  (τ e).fst < θ e ∧ θ e < (τ e).snd

-- (6.44)
theorem not_atomDist_ofPred_surpasses {θ : E → α} (hne : ∃ e, P e)
    (hP : ∀ e, P e → Surpasses τ θ e) : ¬ AtomDist τ (.ofPred P) :=
  not_atomDist_ofPred hne fun e he h ↦
    lt_irrefl _ (((hP e he).1.trans (hP e he).2).trans_eq h.symm)

end Preorder

/-- A predicate of events in time has the subinterval property exactly when its
existential quantifier is atomically distributive over time at every world. -/
theorem hasSubintervalProperty_iff_forall_atomDist {W T : Type*} [LinearOrder T]
    [Event.TemporalTrace E T] {P : W → E → Prop} :
    Aspect.HasSubintervalProperty P ↔ ∀ w, AtomDist τ (.ofPred (P w)) :=
  forall_congr' fun _ ↦ atomDist_ofPred_iff.symm

-- (5.44), (5.57)
theorem not_atomDist_ofPred_length [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {τ : E → NonemptyInterval α} {P : E → Prop} {d : α} (hd : 0 < d)
    (hne : ∃ e, P e ∧ (τ e).length = d) :
    ¬ AtomDist τ (.ofPred fun e ↦ P e ∧ (τ e).length = d) :=
  not_atomDist_ofPred hne fun _ he h ↦
    hd.ne' (he.2.symm.trans (sub_eq_zero.2 h.symm))

/-! ### *Le* and *méi-yǒu* (chapter 6) -/

section Particles

variable [Preorder α] {τ : E → NonemptyInterval α} {V : EvQuant E} {P : E → Prop} {p : α}

/-- *Le*, (6.3), is defined only of a quantifier that is not atomically distributive, and asserts
that it applies to the events whose trace precedes `p`, the measurement of the evaluation
argument. -/
def le (τ : E → NonemptyInterval α) (V : EvQuant E) (p : α) : Part Prop :=
  ⟨¬ AtomDist τ V, fun _ ↦ V fun e ↦ (τ e).IsBefore (.pure p)⟩

/-- *Méi-yǒu*, (6.18), is the negation of *le*, with the same presupposition. -/
def meiyou (τ : E → NonemptyInterval α) (V : EvQuant E) (p : α) : Part Prop :=
  (le τ V p).map Not

@[simp] theorem le_dom : (le τ V p).Dom ↔ ¬ AtomDist τ V := Iff.rfl

@[simp] theorem meiyou_dom : (meiyou τ V p).Dom ↔ ¬ AtomDist τ V := Iff.rfl

@[simp] theorem le_get (h : (le τ V p).Dom) :
    (le τ V p).get h ↔ V fun e ↦ (τ e).IsBefore (.pure p) := Iff.rfl

@[simp] theorem meiyou_get (h : (meiyou τ V p).Dom) :
    (meiyou τ V p).get h ↔ ¬ (le τ V p).get h := Iff.rfl

/-- The bare stative is a presupposition failure of *le*, (3.40). -/
theorem not_le_dom_of_le (hτ : Function.Surjective τ) (I : NonemptyInterval α) :
    ¬ (le τ (.ofPred (τ · ≤ I)) p).Dom :=
  not_not_intro (atomDist_ofPred_le hτ I)

-- (5.46)
theorem not_le_dom_of_lt_fst (hτ : Function.Surjective τ) (m : α) :
    ¬ (le τ (.ofPred fun e ↦ m < (τ e).fst) p).Dom :=
  not_not_intro (atomDist_ofPred_lt_fst hτ m)

/-- *Guò* licenses *méi-yǒu*, whatever the description of the surpassing events, (6.73), (6.74). -/
theorem meiyou_dom_of_surpasses {θ : E → α} (hne : ∃ e, P e) (hP : ∀ e, P e → Surpasses τ θ e) :
    (meiyou τ (.ofPred P) p).Dom :=
  not_atomDist_ofPred_surpasses hne hP

end Particles

/-- A duration argument or a measure phrase licenses *le*, (6.4), (6.5). -/
theorem le_dom_of_length [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {τ : E → NonemptyInterval α} {P : E → Prop} {d p : α} (hd : 0 < d)
    (hne : ∃ e, P e ∧ (τ e).length = d) :
    (le τ (.ofPred fun e ↦ P e ∧ (τ e).length = d) p).Dom :=
  not_atomDist_ofPred_length hd hne

theorem le_get_iff_perfect {T : Type*} [LinearOrder T] {τ : E → NonemptyInterval T}
    {V : EvQuant E} {p : T} (h : (le τ V p).Dom) :
    (le τ V p).get h ↔
      V fun e ↦ Aspect.ViewpointType.perfect.ttTSitRelation (.pure p) (τ e) :=
  Iff.rfl

end Zhao2025
