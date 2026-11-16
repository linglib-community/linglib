module

public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Quantification.Predicative
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Data.Part

/-!
# Zhao (2025): Cross-Linguistic and Cross-Domain Temporal Expressions

Zhao's dissertation analyzes the Mandarin particles *le*, *méi-yǒu* and *guò*, which locate an
event in time with verbs and a degree on a scale in comparatives. A verbal projection denotes a
quantifier over events, atomically distributive when the traces it applies at form a lower set,
which for an existential quantifier is [the subinterval
property](##Zhao2025.hasSubintervalProperty_iff_forall_atomDist). *Le* is defined only of a
quantifier that is not, so it [rejects a stative](##Zhao2025.not_le_dom_of_hasSubintervalProperty),
and a duration argument or a measure phrase [repairs the failure](##Zhao2025.le_dom_dur_iff)
whatever length it names, a length being measured only off points. *Guò* introduces events whose
trace surpasses their theme; they license *méi-yǒu* and [place the theme strictly
before](##Zhao2025.exists_snd_lt_of_surpasses) the point of evaluation, where [*le*
asserts](##Zhao2025.le_get_some_iff_mem_perfect) weak precedence.

## Implementation notes

Times and degrees are the points of an order, traces its closed intervals, and a point is the
interval `NonemptyInterval.pure`; the dissertation also admits non-convex sums of points, which its
analyses do not use. An event quantifier is a `Quantifier` over events and its traces are those of
its image `Quantifier.map` along the trace function, so Atomic Distributivity is stated of the
predicative content `Quantifier.BE` of that image. The particles take the measurement of their
evaluation argument as an interval, a point for the utterance time or a height and a run time for
a matrix event. *Le* is commonly called a perfective marker; the dissertation strips its temporal
content down to precedence, which is the relation `Aspect` assigns to the perfect. A surpassing
event is one whose trace has the measurement of its theme `NonemptyInterval.During` it.

The presupposition is formalized as printed, so a quantifier that applies at no trace is
atomically distributive and neither particle is defined of it. The library takes states and
activities alike to have the subinterval property; here an activity fails it because of its
minimal parts. The first part of the dissertation, the ⌜then⌝-present puzzle, is joint work with
Tsilia, formalized in `Studies/TsiliaZhao2026.lean`.

## TODO

The dissertation's judgments are not yet rows of `Data/Examples`. The manner head [mn], the head
[exd] for measure phrases with *guò*, and Atomic Distributivity along a spatial axis are not
formalized.

## References

* [zhao-2025]
* [champollion-2015]
* [bennett-partee-1972]
* [tsilia-zhao-2026]
-/

@[expose] public section

namespace Zhao2025

open Quantifier Set

variable {E X α : Type*}

/-! ### Event specifications (chapter 4) -/

/-- `specify C V` adds the specification `C` to the events of the quantifier `V`,
`λf. V (λe. C(e) ∧ f(e))`, the shape shared by the thematic heads of [champollion-2015]. -/
def specify (C : Set E) (V : Quantifier E) : Quantifier E := fun f ↦ V (C ∩ f)

@[simp] theorem specify_apply (C f : Set E) (V : Quantifier E) : specify C V f ↔ V (C ∩ f) := .rfl

@[simp] theorem specify_some (C A : Set E) : specify C (Det.some A) = Det.some (A ∩ C) :=
  funext fun f ↦ congrArg Set.Nonempty (inter_assoc A C f).symm

/-- (6.64): the head [th] gives a quantifier over themes scope over the event quantifier, whose
events it specifies as having that theme. -/
def theme (th : E → X) (Q : Quantifier X) (V : Quantifier E) : Quantifier E :=
  Q.bind fun x ↦ specify {e | th e = x} V

theorem theme_individual (th : E → X) (x : X) (V : Quantifier E) :
    theme th (individual x) V = specify {e | th e = x} V := rfl

theorem theme_some_some (th : E → X) (A : Set X) (S : Set E) :
    theme th (Det.some A) (Det.some S) = Det.some (S ∩ th ⁻¹' A) := by
  funext f
  refine propext ⟨fun ⟨x, hx, e, he, hth, hf⟩ ↦ ⟨e, ⟨he, ?_⟩, hf⟩,
    fun ⟨e, ⟨he, hA⟩, hf⟩ ↦ ⟨th e, hA, e, he, rfl, hf⟩⟩
  rw [mem_preimage, show th e = x from hth]
  exact hx

/-! ### Atomic Distributivity (chapter 5) -/

section Preorder

variable [Preorder α] {τ : E → NonemptyInterval α} {V : Quantifier E} {A : Set E}
  {i : NonemptyInterval α}

/-- (5.83): a quantifier over events is atomically distributive along the trace `τ` when the
traces it applies at form a lower set. -/
def AtomDist (τ : E → NonemptyInterval α) (V : Quantifier E) : Prop :=
  IsLowerSet (BE (V.map τ))

theorem atomDist_iff :
    AtomDist τ V ↔ ∀ i, V {e | τ e = i} → ∀ i' ≤ i, V {e | τ e = i'} :=
  ⟨fun h _ hi _ hle ↦ h hle hi, fun h _ _ hle hi ↦ h _ hi _ hle⟩

theorem atomDist_some_iff : AtomDist τ (Det.some A) ↔ IsLowerSet (τ '' A) := by
  rw [AtomDist, map_some, BE_some]

-- an atomically distributive quantifier that applies at a trace applies at each of its points
theorem AtomDist.pure (h : AtomDist τ V) (hi : V {e | τ e = i}) {x : α} (hx : x ∈ i) :
    V {e | τ e = .pure x} :=
  h (NonemptyInterval.le_def.2 (NonemptyInterval.mem_def.1 hx)) hi

theorem not_atomDist_iff_of_forall_pure (hV : ∀ x, ¬ V {e | τ e = .pure x}) :
    ¬ AtomDist τ V ↔ ∃ i, V {e | τ e = i} :=
  ⟨fun h ↦ by_contra fun hi ↦ h fun i _ _ hi' ↦ absurd ⟨i, hi'⟩ hi,
    fun ⟨i, hi⟩ h ↦ hV i.fst (h.pure hi ⟨le_rfl, i.fst_le_snd⟩)⟩

-- (5.39)–(5.41)
theorem not_atomDist_some (hne : A.Nonempty) (hA : ∀ e ∈ A, ¬ (τ e).IsPoint) :
    ¬ AtomDist τ (Det.some A) :=
  (not_atomDist_iff_of_forall_pure fun _ ⟨e, he, hτ⟩ ↦ hA e he (hτ ▸ rfl)).2
    (let ⟨e, he⟩ := hne; ⟨τ e, e, he, rfl⟩)

theorem atomDist_some_preimage (hτ : IsLowerSet (range τ)) {S : Set (NonemptyInterval α)}
    (hS : IsLowerSet S) : AtomDist τ (Det.some (τ ⁻¹' S)) := by
  rw [atomDist_some_iff, image_preimage_eq_inter_range]
  exact hS.inter hτ

-- (5.53)
theorem atomDist_some_lt_fst (hτ : IsLowerSet (range τ)) (m : α) :
    AtomDist τ (Det.some {e | m < (τ e).fst}) :=
  atomDist_some_preimage (S := {i | m < i.fst}) hτ fun _ _ hba ha ↦
    ha.trans_le (NonemptyInterval.le_def.1 hba).1

end Preorder

/-- A predicate of events in time has the subinterval property exactly when its existential
quantifier is atomically distributive over time at every world. -/
theorem hasSubintervalProperty_iff_forall_atomDist {W T : Type*} [LinearOrder T]
    [TemporalTrace E T] {P : W → E → Prop} :
    Aspect.HasSubintervalProperty P ↔ ∀ w, AtomDist Event.τ (Det.some {e | P w e}) :=
  forall_congr' fun _ ↦ atomDist_some_iff.symm

/-! ### Duration arguments and measure phrases -/

section Norm

variable [AddCommGroup α] [PartialOrder α] {τ : E → NonemptyInterval α}
  {V : Quantifier E} {A : Set E} {P : α → Prop}

/-- The norm of an interval is its length, and is not defined of a point. -/
def norm (i : NonemptyInterval α) : Part α := ⟨¬ i.IsPoint, fun _ ↦ i.length⟩

theorem exists_mem_norm {i : NonemptyInterval α} :
    (∃ ℓ ∈ norm i, P ℓ) ↔ ¬ i.IsPoint ∧ P i.length :=
  ⟨fun ⟨_, ⟨h, rfl⟩, hP⟩ ↦ ⟨h, hP⟩, fun ⟨h, hP⟩ ↦ ⟨_, ⟨h, rfl⟩, hP⟩⟩

/-- (4.10): the head [dur], and its degree counterpart [diff], specify the events as having a
trace whose norm satisfies the measure phrase `P`. -/
def dur (τ : E → NonemptyInterval α) (P : α → Prop) (V : Quantifier E) : Quantifier E :=
  specify {e | ∃ ℓ ∈ norm (τ e), P ℓ} V

theorem dur_some : dur τ P (Det.some A) = Det.some (A ∩ {e | ∃ ℓ ∈ norm (τ e), P ℓ}) :=
  specify_some _ A

theorem dur_pure_iff (x : α) : dur τ P V {e | τ e = .pure x} ↔ V ∅ := by
  have h : {e | ∃ ℓ ∈ norm (τ e), P ℓ} ∩ {e | τ e = .pure x} = ∅ :=
    eq_empty_of_forall_notMem fun e ⟨he, hτ⟩ ↦ (exists_mem_norm.1 he).1 (hτ ▸ rfl)
  rw [dur, specify_apply, h]

-- (5.44), (5.57)
theorem not_atomDist_dur_iff (hV : ¬ V ∅) :
    ¬ AtomDist τ (dur τ P V) ↔ ∃ i, dur τ P V {e | τ e = i} :=
  not_atomDist_iff_of_forall_pure fun x ↦ (dur_pure_iff x).not.2 hV

end Norm

/-! ### *Le* and *méi-yǒu* (chapter 6) -/

section Particles

variable [Preorder α] {τ : E → NonemptyInterval α} {V : Quantifier E} {a : NonemptyInterval α}

/-- (6.3): *le* is defined only of a quantifier that is not atomically distributive, and asserts
that it applies to the events whose trace precedes `a`, the measurement of the evaluation
argument. -/
def le (τ : E → NonemptyInterval α) (V : Quantifier E) (a : NonemptyInterval α) : Part Prop :=
  ⟨¬ AtomDist τ V, fun _ ↦ V {e | (τ e).snd ≤ a.fst}⟩

/-- (6.18): *méi-yǒu* is the negation of *le*, with the same presupposition. -/
def meiyou (τ : E → NonemptyInterval α) (V : Quantifier E) (a : NonemptyInterval α) : Part Prop :=
  (le τ V a).map Not

@[simp] theorem le_dom : (le τ V a).Dom ↔ ¬ AtomDist τ V := .rfl

@[simp] theorem meiyou_dom : (meiyou τ V a).Dom ↔ ¬ AtomDist τ V := .rfl

@[simp] theorem le_get (h : (le τ V a).Dom) :
    (le τ V a).get h ↔ V {e | (τ e).snd ≤ a.fst} := .rfl

@[simp] theorem meiyou_get (h : (meiyou τ V a).Dom) :
    (meiyou τ V a).get h ↔ ¬ (le τ V a).get h := .rfl

-- (5.46)
theorem not_le_dom_some_lt_fst (hτ : IsLowerSet (range τ)) (m : α) :
    ¬ (le τ (Det.some {e | m < (τ e).fst}) a).Dom :=
  not_not_intro (atomDist_some_lt_fst hτ m)

end Particles

section Time

variable {W T : Type*} [LinearOrder T] [TemporalTrace E T] {P : W → E → Prop} {w : W}
  {a : NonemptyInterval T}

/-- (3.40): *le* is not defined of the existential quantifier of a predicate with the subinterval
property, the bare stative. -/
theorem not_le_dom_of_hasSubintervalProperty (hP : Aspect.HasSubintervalProperty P) :
    ¬ (le Event.τ (Det.some {e | P w e}) a).Dom :=
  not_not_intro (hasSubintervalProperty_iff_forall_atomDist.1 hP w)

/-- Of an existential quantifier over events in time, *le* asserts the perfect: the evaluation
time is preceded by an event of the predicate. -/
theorem le_get_some_iff_mem_perfect (h : (le Event.τ (Det.some {e | P w e}) a).Dom) :
    (le Event.τ (Det.some {e | P w e}) a).get h ↔
      a ∈ Aspect.ViewpointType.perfect.denote P w :=
  exists_congr fun _ ↦ and_comm

end Time

section Norm

variable [AddCommGroup α] [PartialOrder α] {τ : E → NonemptyInterval α}
  {V : Quantifier E} {A : Set E} {P : α → Prop} {a : NonemptyInterval α}

/-- (6.4), (6.5): with a duration argument or a measure phrase, whatever length it names, *le* is
defined of a quantifier that does not apply to the empty property exactly when the quantifier
applies at some trace. -/
theorem le_dom_dur_iff (hV : ¬ V ∅) :
    (le τ (dur τ P V) a).Dom ↔ ∃ i, dur τ P V {e | τ e = i} :=
  not_atomDist_dur_iff hV

theorem le_dom_dur_some_iff :
    (le τ (dur τ P (Det.some A)) a).Dom ↔ ∃ e ∈ A, ∃ ℓ ∈ norm (τ e), P ℓ := by
  rw [le_dom_dur_iff fun ⟨_, _, h⟩ ↦ h, dur_some]
  exact ⟨fun ⟨_, e, ⟨he, hP⟩, _⟩ ↦ ⟨e, he, hP⟩, fun ⟨e, he, hP⟩ ↦ ⟨τ e, e, ⟨he, hP⟩, rfl⟩⟩

-- (6.5): the degree use of *le* with a measure phrase yields a comparison by more than `d`
theorem add_lt_of_le_get [IsOrderedAddMonoid α] {m n d : α}
    (h : (le τ (dur τ (· = d) (Det.some {e | m < (τ e).fst})) (.pure n)).Dom)
    (hg : (le τ (dur τ (· = d) (Det.some {e | m < (τ e).fst})) (.pure n)).get h) :
    m + d < n := by
  obtain ⟨e, hm, he, hn⟩ := hg
  obtain ⟨-, rfl⟩ := exists_mem_norm.1 he
  calc m + (τ e).length < (τ e).fst + (τ e).length := by gcongr; exact hm
    _ = (τ e).snd := add_sub_cancel _ _
    _ ≤ n := hn

end Norm

/-! ### *Guò* (chapter 6) -/

section Guo

variable [Preorder α] {τ : E → NonemptyInterval α} {θ : E → NonemptyInterval α} {S : Set E}
  {a : NonemptyInterval α}

theorem not_isPoint_of_during {i j : NonemptyInterval α} (h : j.During i) : ¬ i.IsPoint :=
  fun hp ↦ ((h.1.trans_le j.fst_le_snd).trans h.2).ne hp

-- (6.73), (6.74): *guò* licenses *méi-yǒu*, whatever the description of the surpassing events
theorem meiyou_dom_of_surpasses (hne : S.Nonempty) (hS : ∀ e ∈ S, (θ e).During (τ e)) :
    (meiyou τ (Det.some S) a).Dom :=
  not_atomDist_some hne fun e he ↦ not_isPoint_of_during (hS e he)

/-- (6.68), (6.70): a *guò* sentence quantifies over surpassing events, (6.45), whose trace starts
strictly before the measurement of their theme and ends strictly after it. Specified by [th] for a
theme among `A` and by [eval] as ending at `n`, it places some theme strictly before `n`. -/
theorem exists_snd_lt_of_surpasses {th : E → X} {μ : X → NonemptyInterval α} {A : Set X} {n : α}
    (hS : ∀ e ∈ S, (μ (th e)).During (τ e))
    (h : specify {e | (τ e).snd = n} (theme th (Det.some A) (Det.some S)) univ) :
    ∃ x ∈ A, (μ x).snd < n := by
  rw [theme_some_some, specify_some] at h
  obtain ⟨e, ⟨⟨he, hA⟩, hn⟩, -⟩ := h
  exact ⟨th e, hA, hn ▸ (hS e he).2⟩

end Guo

end Zhao2025
