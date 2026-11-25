module

public import Linglib.Semantics.Aspect.Viewpoint.Basic
public import Linglib.Semantics.Quantifier.Predicative

/-!
# The subinterval property

A predicate of events has the subinterval property of Bennett and Partee and of Dowty when every
subinterval of the run time of one of its events is the run time of one of its events: its run
times `runTimes P` are closed under subintervals, `Antitone (runTimes P)`. States and activities
have the property: if John slept from one to three, he slept from one to two. A predicate of
events that all end when a given durative event ends lacks it,
`not_hasSubintervalProperty_snd_eq`, as no proper part of the building of a house is the building
of a house.

A predicate has the property exactly when its non-strict imperfective holds only at its run times,
`hasSubintervalProperty_iff_unbounded_le`. The imperfective then entails the perfective at the same
reference time, `HasSubintervalProperty.imperfective_le_perfective`, *Mary was running* entailing
*Mary ran*;
the entailment does not characterize the property,
`exists_unbounded_le_perfective_not_hasSubintervalProperty`.

Zhao states the property of a quantifier over events and of a trace on any ordered domain, a
degree scale as well as the timeline: `AtomDist τ V`, Atomic Distributivity, holds when the
traces the quantifier applies at form a lower set. Such a quantifier applies at every point of a
trace it applies at, `AtomDist.pure`, and the subinterval property of a predicate is the Atomic
Distributivity of its existential quantifier along the run time,
`hasSubintervalProperty_iff_atomDist`.

## Implementation notes

The viewpoint operators quantify over events of one world, so the entailment is the extensional
one. The imperfective paradox proper, on which *John was building a house* is true though no
house is ever built, is the business of the modal progressive, `Aspect.progressive`. A quantifier
that applies at no trace is atomically distributive.

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

open Event (τ runTimes runTimes_τ)
open scoped SetRel

variable {W T E : Type*} [LinearOrder T] [TemporalTrace E T] {P : E → Prop}
  {t : NonemptyInterval T}

/-- A predicate of events has the subinterval property when its run times are closed under
subintervals. -/
def HasSubintervalProperty (P : E → Prop) : Prop := Antitone (runTimes P)

/-- A predicate has the subinterval property exactly when every subinterval of the run time of
one of its events is the run time of one of its events. -/
theorem hasSubintervalProperty_iff_witnesses :
    HasSubintervalProperty P ↔ ∀ e, P e → ∀ t ≤ τ e, ∃ e', τ e' = t ∧ P e' :=
  ⟨fun h _ hP _ ht ↦ h ht (runTimes_τ hP), fun h _ _ hle ⟨e, he, hP⟩ ↦ h e hP _ (he ▸ hle)⟩

/-- A predicate has the subinterval property exactly when its existential quantifier is
atomically distributive along the run time. -/
theorem hasSubintervalProperty_iff_atomDist :
    HasSubintervalProperty P ↔ AtomDist τ (Quantifier.Det.some {e | P e}) := by
  rw [atomDist_some_iff, hasSubintervalProperty_iff_witnesses]
  exact ⟨fun h _ _ hle ⟨e, hP, he⟩ ↦ let ⟨e', he', hP'⟩ := h e hP _ (he ▸ hle); ⟨e', hP', he'⟩,
    fun h e hP _ ht ↦ let ⟨e', hP', he'⟩ := h ht ⟨e, hP, rfl⟩; ⟨e', he', hP'⟩⟩

/-- A predicate has the subinterval property exactly when its non-strict imperfective holds only
at its run times. -/
theorem hasSubintervalProperty_iff_unbounded_le :
    HasSubintervalProperty P ↔ unbounded P ≤ runTimes P := by
  rw [unbounded_le_iff]
  exact ⟨fun h _ ht ↦ durative_iff.2 fun _ hs ↦ h hs ht,
    fun h _ _ hle ht ↦ durative_iff.1 (h _ ht) _ hle⟩

namespace HasSubintervalProperty

theorem unbounded_le_runTimes (h : HasSubintervalProperty P) : unbounded P ≤ runTimes P :=
  hasSubintervalProperty_iff_unbounded_le.1 h

theorem unbounded_le_perfective (h : HasSubintervalProperty P) : unbounded P ≤ perfective P :=
  h.unbounded_le_runTimes.trans (le_inclusive _)

/-- Under the subinterval property, the imperfective over a modal domain containing the world of
evaluation entails the perfective, Dowty's entailment from *x is V-ing* to *x has V-ed*. -/
theorem imperfective_le_perfective {P : W → E → Prop} {w : W} (h : HasSubintervalProperty (P w))
    {acc : NonemptyInterval T → SetRel W W} (hw : ∀ t, w ~[acc t] w) :
    imperfective acc P w ≤ perfective (P w) :=
  fun t ht ↦ h.unbounded_le_perfective t (unbounded_of_imperfective (hw t) ht)

/-- Under the subinterval property, a predicate in progress throughout a span holds perfectively at
every subinterval of it. -/
theorem unbounded_le_durative_perfective (h : HasSubintervalProperty P) :
    unbounded P ≤ durative (perfective P) :=
  fun _ ht ↦ durative_iff.2 fun _ hs ↦ h.unbounded_le_perfective _ (antitone_unbounded P hs ht)

end HasSubintervalProperty

/-- The predicate of events that end when a durative event ends lacks the subinterval property,
as the building of a house holds of no proper part that lacks the result. -/
theorem not_hasSubintervalProperty_snd_eq {e : E} (he : (τ e).fst < (τ e).snd) :
    ¬ HasSubintervalProperty fun e' : E ↦ (τ e').snd = (τ e).snd := fun h ↦ by
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h e rfl
    (.pure (τ e).fst) (NonemptyInterval.le_def.2 ⟨le_rfl, he.le⟩)
  rw [hτ] at hP
  exact he.ne hP

/-- The entailment from the non-strict imperfective to the perfective does not characterize the
subinterval property. The predicate of events that are instantaneous or run from `0` to `2`
validates it, every reference time containing an instant, and the interval from `0` to `1` is a
subinterval of one of its run times without being one. -/
theorem exists_unbounded_le_perfective_not_hasSubintervalProperty :
    ∃ P : NonemptyInterval ℤ → Prop, unbounded P ≤ perfective P ∧ ¬ HasSubintervalProperty P := by
  refine ⟨fun e ↦ e.IsPoint ∨ e = ⟨⟨0, 2⟩, by decide⟩,
    fun t _ ↦ perfective_iff.2
      ⟨.pure t.fst, NonemptyInterval.le_def.2 ⟨le_rfl, t.fst_le_snd⟩, .inl rfl⟩,
    fun h ↦ ?_⟩
  obtain ⟨e', hτ, hP⟩ := hasSubintervalProperty_iff_witnesses.1 h
    ⟨⟨0, 2⟩, by decide⟩ (.inr rfl) ⟨⟨0, 1⟩, by decide⟩
    (NonemptyInterval.le_def.2 ⟨le_rfl, by decide⟩)
  rw [Event.τ_nonemptyInterval] at hτ
  subst hτ
  rcases hP with hP | hP
  · exact absurd hP (by decide)
  · exact absurd (congrArg (·.snd) hP) (by decide)

/-- An interval containing no event of the predicate has no subinterval containing one. -/
theorem antitone_not_perfective (P : E → Prop) : Antitone fun t ↦ ¬ perfective P t :=
  fun _ _ hle h hp ↦ h (monotone_perfective P hle hp)

end Aspect
