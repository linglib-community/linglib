module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Quantification.Predicative

/-!
# The subinterval property

This file defines the subinterval property of Bennett and Partee and of Dowty. A predicate of
events has it when [every subinterval](##Aspect.hasSubintervalProperty_iff_witnesses) of the run
time of an event it holds of is the run time of an event it holds of, which is to say that its run
times form a lower set. States and activities have the property: if John slept from one to three,
he slept from one to two. Accomplishments and achievements [lack
it](##Aspect.not_hasSubintervalProperty_snd_eq), since no proper part of the building of a house
is the building of a house.

For a predicate with the property the imperfective [entails the
perfective](##Aspect.HasSubintervalProperty.impf_subset_prfv) at the same reference time, *Mary was
running* entailing *Mary ran*. The entailment [does not
characterize](##Aspect.exists_prfv_of_unbounded_not_hasSubintervalProperty) the property. For an
interval property, a set of intervals at each world, the property is `IsLowerSet`: the [negated
perfective](##Aspect.isLowerSet_compl_prfv) has it, and for a lower set the [durative
claim](##Aspect.durative_eq_of_isLowerSet) and the [perfect](##Aspect.perfect_eq_of_isLowerSet) are
the set itself.

Zhao states the property of a quantifier over events and of a trace on any ordered domain, a
degree scale as well as the timeline: `Aspect.AtomDist`, Atomic Distributivity, holds when the
traces the quantifier applies at form a lower set. Such a quantifier [applies at every
point](##Aspect.AtomDist.pure) of a trace it applies at, and the subinterval property of a
predicate [is the Atomic Distributivity](##Aspect.hasSubintervalProperty_iff_forall_atomDist) of
its existential quantifier along the run time.

## Implementation notes

The property is divisive reference, `Mereology.DIV`, of the predicate's run times, so it is
stated on mathlib's `IsLowerSet`. The viewpoint operators quantify over events of the world of
evaluation, so the entailment is the extensional one. The imperfective paradox proper, on which
*John was building a house* is true though no house is ever built, is the business of the modal
progressive, `Aspect.PROG`. A quantifier that applies at no trace is atomically distributive.

## References

* [bennett-partee-1972]
* [dowty-1979]
* [zhao-2025]
-/

@[expose] public section

namespace Aspect

/-! ### Quantifiers over events -/

section Quantifier

open Quantifier

variable {E α : Type*} [Preorder α] {τ : E → NonemptyInterval α} {V : Quantifier E} {A : Set E}
  {i : NonemptyInterval α}

/-- A quantifier over events is atomically distributive along the trace `τ` when the traces it
applies at form a lower set: whenever it applies to the events with trace `i`, it applies
to the events with trace `i'` for each subinterval `i'` of `i` ([zhao-2025]). -/
def AtomDist (τ : E → NonemptyInterval α) (V : Quantifier E) : Prop :=
  IsLowerSet {i | V {e | τ e = i}}

theorem atomDist_iff :
    AtomDist τ V ↔ ∀ i, V {e | τ e = i} → ∀ i' ≤ i, V {e | τ e = i'} :=
  ⟨fun h _ hi _ hle ↦ h hle hi, fun h _ _ hle hi ↦ h _ hi _ hle⟩

/-- Atomic Distributivity says that the predicative content of the image of the quantifier along
the trace is a lower set. -/
theorem atomDist_iff_isLowerSet_BE : AtomDist τ V ↔ IsLowerSet (BE (V.map τ)) := .rfl

/-- An existential quantifier is atomically distributive when the traces of its restrictor form a
lower set. -/
theorem atomDist_some_iff : AtomDist τ (Det.some A) ↔ IsLowerSet (τ '' A) := by
  rw [atomDist_iff_isLowerSet_BE, map_some, BE_some]

/-- An atomically distributive quantifier that applies at a trace applies at each of its
points. -/
theorem AtomDist.pure (h : AtomDist τ V) (hi : V {e | τ e = i}) {x : α} (hx : x ∈ i) :
    V {e | τ e = .pure x} :=
  h (NonemptyInterval.pure_le_iff.2 hx) hi

/-- A quantifier that applies at no point fails Atomic Distributivity exactly when it applies at
some trace. -/
theorem not_atomDist_iff_of_forall_pure (hV : ∀ x, ¬ V {e | τ e = .pure x}) :
    ¬ AtomDist τ V ↔ ∃ i, V {e | τ e = i} :=
  ⟨fun h ↦ by_contra fun hi ↦ h fun i _ _ hi' ↦ absurd ⟨i, hi'⟩ hi,
    fun ⟨i, hi⟩ h ↦ hV i.fst (h.pure hi ⟨le_rfl, i.fst_le_snd⟩)⟩

/-- A description with an event, none of whose events is at a point, is not atomically
distributive. -/
theorem not_atomDist_some (hne : A.Nonempty) (hA : ∀ e ∈ A, ¬ (τ e).IsPoint) :
    ¬ AtomDist τ (Det.some A) :=
  (not_atomDist_iff_of_forall_pure fun _ ⟨e, he, hτ⟩ ↦ hA e he (hτ ▸ rfl)).2
    (let ⟨e, he⟩ := hne; ⟨τ e, e, he, rfl⟩)

/-- Where the traces of all events form a lower set, a description by a lower set of traces is
atomically distributive. -/
theorem atomDist_some_preimage (hτ : IsLowerSet (Set.range τ)) {S : Set (NonemptyInterval α)}
    (hS : IsLowerSet S) : AtomDist τ (Det.some (τ ⁻¹' S)) := by
  rw [atomDist_some_iff, Set.image_preimage_eq_inter_range]
  exact hS.inter hτ

end Quantifier

open Event (τ)

variable {W T E : Type*} [LinearOrder T] [TemporalTrace E T] {P : W → E → Prop} {w : W}
  {t : NonemptyInterval T}

/-- A predicate of events has the subinterval property when its run times form a lower set at
every world. -/
def HasSubintervalProperty (P : W → E → Prop) : Prop :=
  ∀ w, IsLowerSet (τ '' {e | P w e})

/-- A predicate has the subinterval property exactly when its existential quantifier is
atomically distributive along the run time at every world. -/
theorem hasSubintervalProperty_iff_forall_atomDist :
    HasSubintervalProperty P ↔ ∀ w, AtomDist τ (Quantifier.Det.some {e | P w e}) :=
  forall_congr' fun _ ↦ atomDist_some_iff.symm

/-- A predicate has the subinterval property exactly when every subinterval of the run time of
one of its events is the run time of one of its events. -/
theorem hasSubintervalProperty_iff_witnesses :
    HasSubintervalProperty P ↔
      ∀ (e : E) (w : W), P w e → ∀ t ≤ τ e, ∃ e' : E, τ e' = t ∧ P w e' :=
  ⟨fun h _ w hP _ ht ↦ let ⟨e', hP', hτ⟩ := h w ht (Set.mem_image_of_mem τ hP); ⟨e', hτ, hP'⟩,
    fun h w _ t ht ⟨e, hP, he⟩ ↦ let ⟨e', hτ, hP'⟩ := h e w hP t (he ▸ ht); ⟨e', hP', hτ⟩⟩

namespace HasSubintervalProperty

theorem mem_image_of_unbounded (h : HasSubintervalProperty P) (ht : t ∈ UNBOUNDED P w) :
    t ∈ τ '' {e | P w e} :=
  let ⟨e, hle, hP⟩ := ht; h w hle ⟨e, hP, rfl⟩

theorem unbounded_subset_prfv (h : HasSubintervalProperty P) (w : W) :
    UNBOUNDED P w ⊆ PRFV P w := fun _ ht ↦
  let ⟨e, hP, hτ⟩ := h.mem_image_of_unbounded ht; ⟨e, hτ.le, hP⟩

/-- Under the subinterval property, the imperfective over a modal domain containing the world of
evaluation entails the perfective, Dowty's entailment from *x is V-ing* to *x has V-ed*. -/
theorem impf_subset_prfv (h : HasSubintervalProperty P) {acc : W → NonemptyInterval T → Set W}
    {w : W} (hw : ∀ t, w ∈ acc w t) : IMPF acc P w ⊆ PRFV P w :=
  fun t ht ↦ h.unbounded_subset_prfv w (mem_unbounded_of_mem_impf (hw t) ht)

/-- Under the subinterval property, a predicate in progress throughout a span holds perfectively at
every subinterval of it. -/
theorem unbounded_subset_durative_prfv (h : HasSubintervalProperty P) (w : W) :
    UNBOUNDED P w ⊆ durative (PRFV P) w :=
  fun _ ht _ hj ↦ h.unbounded_subset_prfv w (isLowerSet_unbounded P w hj ht)

end HasSubintervalProperty

/-- The predicate of events that end when a durative event ends lacks the subinterval property,
as the building of a house holds of no proper part that lacks the result. -/
theorem not_hasSubintervalProperty_snd_eq [Nonempty W] {e : E} (he : (τ e).fst < (τ e).snd) :
    ¬ HasSubintervalProperty fun (_ : W) (e' : E) ↦ (τ e').snd = (τ e).snd := fun h ↦ by
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h e (Classical.arbitrary W) rfl
    (.pure (τ e).fst) (NonemptyInterval.le_def.2 ⟨le_rfl, he.le⟩)
  rw [hτ] at hP
  exact he.ne hP

/-- The entailment from the extensional imperfective to the perfective does not characterize the
subinterval property. The predicate of events that are instantaneous or run from `0` to `2`
validates it, every reference time containing an instant, and the interval from `0` to `1` is a
subinterval of one of its run times without being one. -/
theorem exists_prfv_of_unbounded_not_hasSubintervalProperty :
    ∃ P : Unit → NonemptyInterval ℤ → Prop,
      (∀ w, UNBOUNDED P w ⊆ PRFV P w) ∧ ¬ HasSubintervalProperty P := by
  refine ⟨fun _ e ↦ e.IsPoint ∨ e = ⟨⟨0, 2⟩, by decide⟩,
    fun _ t _ ↦ ⟨.pure t.fst, NonemptyInterval.le_def.2 ⟨le_rfl, t.fst_le_snd⟩, .inl rfl⟩,
    fun h ↦ ?_⟩
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h
    ⟨⟨0, 2⟩, by decide⟩ () (.inr rfl) ⟨⟨0, 1⟩, by decide⟩
    (NonemptyInterval.le_def.2 ⟨le_rfl, by decide⟩)
  rw [Event.τ_nonemptyInterval] at hτ
  subst hτ
  rcases hP with hP | hP
  · exact absurd hP (by decide)
  · exact absurd (congrArg (·.snd) hP) (by decide)

/-! ### Interval properties -/

variable (P w) in
/-- Negation yields the subinterval property, since an interval containing no event of the
predicate has no subinterval containing one. -/
theorem isLowerSet_compl_prfv : IsLowerSet (PRFV P w)ᶜ :=
  (isUpperSet_prfv P w).compl

variable {p : W → Set (NonemptyInterval T)}

variable (p w) in
theorem isLowerSet_durative : IsLowerSet (durative p w) :=
  fun _ _ hle h ↦ (Set.Iic_subset_Iic.2 hle).trans h

/-- For an interval property with the subinterval property, the durative claim is the property
itself. -/
theorem durative_eq_of_isLowerSet (hp : IsLowerSet (p w)) : durative p w = p w :=
  Set.ext fun _ ↦ ⟨fun h ↦ h (Set.mem_Iic.2 le_rfl), fun h ↦ hp.Iic_subset h⟩

/-- For an interval property with the subinterval property, the perfect is the property
itself. -/
theorem perfect_eq_of_isLowerSet (hp : IsLowerSet (p w)) : perfect p w = p w :=
  Set.ext fun i ↦ ⟨fun ⟨_, hp', hf⟩ ↦ hp hf.le hp',
    fun h ↦ ⟨i, h, NonemptyInterval.finalSubinterval_refl i⟩⟩

end Aspect
