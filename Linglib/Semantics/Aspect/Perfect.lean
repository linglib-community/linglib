module

public import Linglib.Logic.Temporal.IntervalAlgebra
public import Linglib.Logic.Temporal.IntervalProperty

/-!
# The perfect and the prospective

The perfect and the prospective are operators on interval properties, possibility along a
relation between the reference interval and an interval of the property. The perfect `perfect p`
holds at `t` when `t` is a final subinterval of some interval of `p`, the perfect time span, and
at a point `a` when `a` is the right boundary of one. The prospective `prospective p` holds at
`t` when `t` precedes some interval of `p`.

The perfect of a property closed under subintervals is the property itself, and the perfect of a
property closed under superintervals holds where some interval of the property is over by the end
of the reference interval.

## Implementation notes

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

open ModalLogic IntervalAlgebra Allen Temporal
open scoped SetRel

variable {T : Type*} [LinearOrder T] {p q : NonemptyInterval T → Prop} {s t : NonemptyInterval T}

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
