module

public import Linglib.Semantics.Aspect.Viewpoint

/-!
# The subinterval property

This file defines the subinterval property of Bennett and Partee and of Dowty. A predicate of
events has it when every subinterval of the run time of an event it holds of is the run time of
an event it holds of, which is to say that its run times form a lower set. States and activities
have the property: if John slept from one to three, he slept from one to two. Accomplishments and
achievements lack it, since no proper part of the building of a house is the building of a house.
The property draws only this line, and does not separate states from activities or
accomplishments from achievements.

For a predicate with the property the imperfective entails the perfective at the same reference
time, *Mary was running* entailing *Mary ran*: the reference time lies inside the run time of a
running, so it is itself the run time of a running. The entailment does not characterize the
property, since a predicate may validate it without being closed under subintervals.

Dowty states the property of sentences true at intervals. For an interval property, a set of
intervals at each world, it says that the set is a lower set, mathlib's `IsLowerSet`, so it needs
no name of its own. The non-strict and the strict imperfective have it whatever the predicate,
and so does the negated perfective, the complement of an upper set: an interval containing no
event of the predicate has no subinterval containing one. A durative claim, the predicate at
every subinterval of a span, has it too, and for a lower set the durative claim and the perfect
are the set itself.

## Main definitions

* `Aspect.HasSubintervalProperty`: the run times of the predicate form a lower set at every
  world.

## Main results

* `Aspect.hasSubintervalProperty_iff_witnesses`: every subinterval of the run time of an event of
  the predicate is the run time of an event of the predicate.
* `Aspect.HasSubintervalProperty.impf_subset_prfv`: the imperfective entails the perfective.
* `Aspect.not_hasSubintervalProperty_snd_eq`: the predicate of events that end when a durative
  event ends lacks the property.
* `Aspect.exists_prfv_of_impf_not_hasSubintervalProperty`: a predicate may validate the
  entailment and lack the property.
* `Aspect.isLowerSet_impf`, `Aspect.isLowerSet_compl_prfv`: the imperfective and the negated
  perfective have the property as interval properties, as the non-strict imperfective does
  (`Aspect.isLowerSet_unbounded`).
* `Aspect.durative_eq_of_isLowerSet`, `Aspect.perfect_eq_of_isLowerSet`: for an interval property
  with the property, the durative claim and the perfect are the property itself.

## Implementation notes

The property is divisive reference, `Mereology.DIV`, of the predicate's run times, so it is
stated on mathlib's `IsLowerSet`. The viewpoint operators quantify over events of the world of
evaluation, so the entailment is the extensional one. The imperfective paradox proper, on which
*John was building a house* is true though no house is ever built, is the business of the modal
progressive, `Aspect.PROG`.

## References

* [bennett-partee-1972]
* [dowty-1979]
-/

@[expose] public section

namespace Aspect

open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {P : W → E → Prop} {w : W}
  {t : NonemptyInterval T}

/-- A predicate of events has the subinterval property when its run times form a lower set at
every world. -/
def HasSubintervalProperty (P : W → E → Prop) : Prop :=
  ∀ w, IsLowerSet (τ '' {e | P w e})

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

/-- Under the subinterval property the imperfective entails the perfective. -/
theorem impf_subset_prfv (h : HasSubintervalProperty P) (w : W) : IMPF P w ⊆ PRFV P w :=
  (impf_subset_unbounded P w).trans (h.unbounded_subset_prfv w)

end HasSubintervalProperty

/-- The predicate of events that end when a durative event ends lacks the subinterval property,
as the building of a house holds of no proper part that lacks the result. -/
theorem not_hasSubintervalProperty_snd_eq [Nonempty W] {e : E} (he : (τ e).fst < (τ e).snd) :
    ¬ HasSubintervalProperty fun (_ : W) (e' : E) ↦ (τ e').snd = (τ e).snd := fun h ↦ by
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h e (Classical.arbitrary W) rfl
    (.pure (τ e).fst) (NonemptyInterval.le_def.2 ⟨le_rfl, he.le⟩)
  rw [hτ] at hP
  exact he.ne hP

/-- The entailment from the imperfective to the perfective does not characterize the subinterval
property. The predicate of events that are instantaneous or run from `0` to `2` validates it,
every reference time containing an instant, and the interval from `0` to `1` is a subinterval
of one of its run times without being one. -/
theorem exists_prfv_of_impf_not_hasSubintervalProperty :
    ∃ P : Unit → NonemptyInterval ℤ → Prop,
      (∀ w, IMPF P w ⊆ PRFV P w) ∧ ¬ HasSubintervalProperty P := by
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
/-- The imperfective has the subinterval property whatever the predicate. -/
theorem isLowerSet_impf : IsLowerSet (IMPF P w) :=
  fun _ _ hle ⟨e, he, hP⟩ ↦ ⟨e, hle.trans_lt he, hP⟩

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
  Set.ext fun i ↦ ⟨fun ⟨_, hp', hf⟩ ↦ hp hf.1 hp',
    fun h ↦ ⟨i, h, NonemptyInterval.finalSubinterval_refl i⟩⟩

end Aspect
