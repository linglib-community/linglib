module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Temporal.IntervalAlgebra

/-!
# Interval properties

An interval property is a predicate of intervals of time, `NonemptyInterval T → Prop`, ordered
pointwise. This file defines operators on interval properties as possibility and necessity,
`◇[R]` and `□[R]`, along relations between intervals: `◇[R] p` holds at an interval `t` when `p`
holds at some interval that `t` is `R`-related to, and `□[R] p` when `p` holds at all of them.

Along inclusion, `inclusive p` holds at `t` when `p` holds at some subinterval of `t`, and
`durative p` when `p` holds at every subinterval of `t`. The perfect `perfect p` holds at `t`
when `t` is a final subinterval of some interval of `p`, the perfect time span, and at a
point `a` when `a` is the right boundary of one. The prospective `prospective p` holds at `t`
when `t` precedes some interval of `p`.

A monotone interval property is one closed under superintervals, and an antitone one is closed
under subintervals. The property `inclusive p` is monotone and equals `p` when `p` is monotone;
`durative p` is antitone and equals `p` when `p` is antitone. The perfect of an antitone property
is the property itself, and the perfect of a monotone property holds where some interval of the
property is over by the end of the reference interval.

## Implementation notes

* An interval property is a predicate, as the propositions of `Logic/Modal` are, so that `◇[R]`
  and `□[R]` apply to it and entailment is `≤`.
* A perfect-level adverbial is an interval property that the perfect intersects with its
  argument, `perfect (adv ⊓ p)`: *since t₀* holds of the spans starting at `t₀`, and the covert
  adverbial of an unmodified perfect of every span.

## References

* [iatridou-anagnostopoulou-izvorski-2001]
* [dowty-1979]
* [mittwoch-1988]
* [vlach-1993]
-/

@[expose] public section

namespace Aspect

open ModalLogic IntervalAlgebra Allen
open scoped SetRel

variable {T : Type*} [LinearOrder T] {p q : NonemptyInterval T → Prop} {s t : NonemptyInterval T}

/-! ### Composition -/

/-- Possibility along one cell after another entails possibility along their product. -/
theorem _root_.IntervalAlgebra.diamond_toSetRel_diamond_le (C D : IntervalAlgebra)
    (p : NonemptyInterval T → Prop) :
    ◇[toSetRel C] (◇[toSetRel D] p) ≤ ◇[toSetRel (C * D)] p := by
  rw [← diamond_comp]
  exact diamond_le_diamond_iff.2 (toSetRel_comp_subset C D) p

/-- On dense time without endpoints, possibility along a product of cells is possibility along
one after the other. -/
theorem _root_.IntervalAlgebra.diamond_toSetRel_mul [DenselyOrdered T] [NoMinOrder T]
    [NoMaxOrder T] (C D : IntervalAlgebra) (p : NonemptyInterval T → Prop) :
    ◇[toSetRel (C * D)] p = ◇[toSetRel C] (◇[toSetRel D] p) := by
  rw [toSetRel_mul, diamond_comp]

/-! ### Subintervals and superintervals -/

/-- `inclusive p` holds at an interval when `p` holds at some subinterval of it, the inclusive
reading of an interval adverbial, *in*. -/
def inclusive (p : NonemptyInterval T → Prop) : NonemptyInterval T → Prop := ◇[toSetRel .le] p

/-- `durative p` holds at an interval when `p` holds at every subinterval of it, the durative
reading of an interval adverbial, *throughout*. -/
def durative (p : NonemptyInterval T → Prop) : NonemptyInterval T → Prop := □[toSetRel .le] p

theorem inclusive_iff : inclusive p t ↔ ∃ s ≤ t, p s := by
  simp [inclusive, diamond_iff]

theorem durative_iff : durative p t ↔ ∀ s ≤ t, p s := by
  simp [durative, box_iff]

theorem inclusive_mono : Monotone (inclusive : (NonemptyInterval T → Prop) → _) := diamond_mono _

theorem durative_mono : Monotone (durative : (NonemptyInterval T → Prop) → _) := box_mono _

theorem le_inclusive (p : NonemptyInterval T → Prop) : p ≤ inclusive p :=
  fun t h ↦ inclusive_iff.2 ⟨t, le_rfl, h⟩

theorem durative_le (p : NonemptyInterval T → Prop) : durative p ≤ p :=
  fun t h ↦ durative_iff.1 h t le_rfl

theorem durative_le_inclusive (p : NonemptyInterval T → Prop) : durative p ≤ inclusive p :=
  (durative_le p).trans (le_inclusive p)

/-- An inclusive property is closed under superintervals. -/
theorem monotone_inclusive (p : NonemptyInterval T → Prop) : Monotone (inclusive p) :=
  fun _ _ hle h ↦ let ⟨s, hs, hp⟩ := inclusive_iff.1 h; inclusive_iff.2 ⟨s, hs.trans hle, hp⟩

/-- A durative property is closed under subintervals. -/
theorem antitone_durative (p : NonemptyInterval T → Prop) : Antitone (durative p) :=
  fun _ _ hle h ↦ durative_iff.2 fun s hs ↦ durative_iff.1 h s (hs.trans hle)

/-- A property closed under superintervals is its own inclusive reading. -/
theorem inclusive_eq_of_monotone (hp : Monotone p) : inclusive p = p :=
  le_antisymm (fun _ h ↦ let ⟨_, hs, hps⟩ := inclusive_iff.1 h; hp hs hps) (le_inclusive p)

/-- A property closed under subintervals is its own durative reading. -/
theorem durative_eq_of_antitone (hp : Antitone p) : durative p = p :=
  le_antisymm (durative_le p) fun _ h ↦ durative_iff.2 fun _ hs ↦ hp hs h

@[simp] theorem inclusive_inclusive (p : NonemptyInterval T → Prop) :
    inclusive (inclusive p) = inclusive p :=
  inclusive_eq_of_monotone (monotone_inclusive p)

@[simp] theorem durative_durative (p : NonemptyInterval T → Prop) :
    durative (durative p) = durative p :=
  durative_eq_of_antitone (antitone_durative p)

/-- A property closed under superintervals holds throughout an interval exactly when it holds at
every moment of the interval. -/
theorem durative_iff_of_monotone (hp : Monotone p) : durative p t ↔ ∀ a ∈ t, p (.pure a) := by
  rw [durative_iff]
  refine ⟨fun h a ha ↦ h _ (NonemptyInterval.pure_le_iff.2 ha), fun h s hs ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hs
  exact hp (NonemptyInterval.pure_le_iff.2 ⟨le_rfl, s.fst_le_snd⟩)
    (h s.fst ⟨h₁, s.fst_le_snd.trans h₂⟩)

/-! ### The perfect and the prospective -/

/-- `perfect p` holds at a reference interval that is a final subinterval of some interval of
`p`, the perfect time span. -/
def perfect (p : NonemptyInterval T → Prop) : NonemptyInterval T → Prop :=
  ◇[toSetRel IntervalAlgebra.finalSubinterval⁻¹] p

/-- `prospective p` holds at a reference interval that precedes some interval of `p`. -/
def prospective (p : NonemptyInterval T → Prop) : NonemptyInterval T → Prop :=
  ◇[toSetRel IntervalAlgebra.precedes⁻¹] p

theorem perfect_iff : perfect p t ↔ ∃ pts, t.FinalSubinterval pts ∧ p pts := by
  simp [perfect, diamond_iff]

theorem prospective_iff : prospective p t ↔ ∃ s, t.Precedes s ∧ p s := by
  simp [prospective, diamond_iff]

/-- The perfect holds at a point that is the right boundary of some perfect time span. -/
theorem perfect_pure_iff {a : T} : perfect p (.pure a) ↔ ∃ pts, pts.snd = a ∧ p pts := by
  rw [perfect_iff]
  refine exists_congr fun pts ↦ and_congr_left fun _ ↦ ?_
  change pts.fst ≤ a ∧ a = pts.snd ↔ pts.snd = a
  exact ⟨fun h ↦ h.2.symm, fun h ↦ ⟨h ▸ pts.fst_le_snd, h.symm⟩⟩

theorem perfect_mono : Monotone (perfect : (NonemptyInterval T → Prop) → _) := diamond_mono _

theorem prospective_mono : Monotone (prospective : (NonemptyInterval T → Prop) → _) :=
  diamond_mono _

/-- Under an adverbial fixing the left boundary in `D`, the perfect holds at `a` where the span
from a time of `D` to `a` belongs to the interval property. -/
theorem perfect_pure_inf_fst_iff {D : T → Prop} {a : T} :
    perfect ((fun pts ↦ D pts.fst) ⊓ p) (.pure a) ↔ ∃ x, D x ∧ ∃ h : x ≤ a, p ⟨(x, a), h⟩ := by
  rw [perfect_pure_iff]
  constructor
  · rintro ⟨⟨⟨x, s⟩, h⟩, rfl, hx, hp⟩
    exact ⟨x, hx, h, hp⟩
  · rintro ⟨x, hx, h, hp⟩
    exact ⟨⟨(x, a), h⟩, rfl, hx, hp⟩

/-- For an interval property closed under superintervals, the perfect holds where some interval
of the property is over by the end of the reference interval: the span need not end with the
reference interval, since it extends to one that does. -/
theorem perfect_iff_of_monotone (hp : Monotone p) :
    perfect p t ↔ ∃ pts, pts.snd ≤ t.snd ∧ p pts := by
  rw [perfect_iff]
  constructor
  · rintro ⟨pts, ⟨-, hsnd⟩, hpts⟩
    exact ⟨pts, hsnd.ge, hpts⟩
  · rintro ⟨pts, hle, hpts⟩
    exact ⟨⟨(pts.fst ⊓ t.fst, t.snd), inf_le_right.trans t.fst_le_snd⟩, ⟨inf_le_right, rfl⟩,
      hp (NonemptyInterval.le_def.2 ⟨inf_le_left, hle⟩) hpts⟩

/-- For an interval property closed under superintervals, the perfect is possibility along
ending no later: a perfect time span ends no later than the reference time. -/
theorem perfect_eq_of_monotone (hp : Monotone p) :
    perfect p = ◇[toSetRel IntervalAlgebra.endsNoLater] p := by
  ext t
  simp [perfect_iff_of_monotone hp, diamond_iff]

/-- For an interval property closed under subintervals, the perfect is the property itself. -/
theorem perfect_eq_of_antitone (hp : Antitone p) : perfect p = p := by
  ext t
  exact ⟨fun h ↦ let ⟨_, hf, hpts⟩ := perfect_iff.1 h; hp hf.le hpts,
    fun h ↦ perfect_iff.2 ⟨t, NonemptyInterval.finalSubinterval_refl t, h⟩⟩

/-- A reference interval within one that precedes an interval precedes it too. -/
theorem antitone_prospective (p : NonemptyInterval T → Prop) : Antitone (prospective p) :=
  fun _ _ hle h ↦ let ⟨j, hj, hp⟩ := prospective_iff.1 h
    prospective_iff.2 ⟨j, (NonemptyInterval.le_def.1 hle).2.trans_lt hj, hp⟩

end Aspect
