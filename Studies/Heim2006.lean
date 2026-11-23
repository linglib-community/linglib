module

public import Linglib.Data.Examples.Heim2006
public import Linglib.Semantics.Degree.Little
public import Mathlib.Algebra.Order.Group.Defs

/-!
# Heim 2006: *little*

The degree word *little* is a negation of degree properties, and a gradable predicate holds of
the degrees its argument reaches, so *we grow `d` little* holds of the degrees above our growth.
Under a modal the negation takes scope below it or above it. With `A` the accessible worlds and
`μ` the measure in each, the degrees of *can … little* are
`scopeDegrees (Det.some A) (fun v ↦ (Iic (μ v))ᶜ)`, those above the least measure
(`scopeDegrees_some_compl_of_isLeast`), and the degrees of *little can …* are
`(scopeDegrees (Det.some A) (Iic ∘ μ))ᶜ`, those above the greatest
(`compl_scopeDegrees_some_of_isGreatest`).

*very* says that a delineation interval `L` is included in the degree property. Over *little* over
*can* that is a necessity, `L ⊆ (Iic (μ v))ᶜ` at every accessible world
(`subset_compl_scopeDegrees_some_iff`), and under *can* a possibility.

The comparative is proper inclusion of the than-clause degrees in the matrix degrees, and *less*
is the comparative of *little*. With the negation of the than-clause below a possibility modal the
subject measures less than the least accessible measure, `Quantifier.LittleBelow`, and with the
negation above it less than the greatest, `Quantifier.LittleAbove`
(`lessThanMinimum_iff`, `lessThanMaximum_iff`). A necessity modal gives the same two readings
with the scopes exchanged (`littleAbove_every_iff_littleBelow_some`), and a comparative without
*little* has one reading (`more_some_iff`). An antonym formed by reversing the scale commutes
with every quantifier, so its scope makes no difference (`scopeDegrees_neg`).

## Implementation notes

The paper's diagram has six worlds with the measure `10 n` at the `n`th and the second to the
fourth accessible; `measure` and `acc` are that model, with the worlds numbered from zero.

## TODO

* The embedding constructions of *how little* and *so little*, the matrix modals of section 5 and
  the two instances of *little* in a comparative with a modal in each clause.
* The monotonicity of the comparative and the licensing of negative polarity items in section 6.
* Section 7: a lexical antonym such as *slow* carries a degree negation that does not move, on
  which the scenario of (46) turns.

## References

* [heim-2006]
* [rullmann-1995]
* [heim-2001]
-/

@[expose] public section

namespace Heim2006

open Set Quantifier Quantifier.Det

section General

variable {W D : Type*} [LinearOrder D] {A : Set W} {μ : W → D} {L : Set D} {a c m : D}

-- (11): the measure lies below the delineation interval.
theorem subset_compl_Iic_iff : L ⊆ (Iic a)ᶜ ↔ ∀ l ∈ L, a < l :=
  forall₂_congr fun _ _ ↦ not_le

/-- (13c): *very* over *little* over a possibility modal is a necessity, the delineation interval
lying above the measure at every accessible world. -/
theorem subset_compl_scopeDegrees_some_iff :
    L ⊆ (scopeDegrees (Det.some A) (Iic ∘ μ))ᶜ ↔ ∀ v ∈ A, L ⊆ (Iic (μ v))ᶜ :=
  ⟨fun h v hv _ hl hle ↦ h hl ⟨v, hv, hle⟩, fun h _ hl ⟨v, hv, hle⟩ ↦ h v hv hl hle⟩

-- (17b)
theorem scopeDegrees_some_compl_of_isLeast (h : IsLeast (μ '' A) m) :
    scopeDegrees (Det.some A) (fun v ↦ (Iic (μ v))ᶜ) = Ioi m := by
  obtain ⟨⟨u, hu, rfl⟩, hm⟩ := h
  ext e
  exact ⟨fun ⟨v, hv, he⟩ ↦ (hm ⟨v, hv, rfl⟩).trans_lt (not_le.mp he),
    fun he ↦ ⟨u, hu, not_le.mpr he⟩⟩

-- (17c)
theorem compl_scopeDegrees_some_of_isGreatest (h : IsGreatest (μ '' A) m) :
    (scopeDegrees (Det.some A) (Iic ∘ μ))ᶜ = Ioi m := by
  obtain ⟨⟨u, hu, rfl⟩, hm⟩ := h
  ext e
  exact ⟨fun he ↦ lt_of_not_ge fun hle ↦ he ⟨u, hu, hle⟩,
    fun he ⟨v, hv, hle⟩ ↦ (hle.trans (hm ⟨v, hv, rfl⟩)).not_gt he⟩

/-- With *little*, a necessity modal and a possibility modal give the same two readings: the
negation above one is the negation below the other. -/
theorem littleAbove_every_iff_littleBelow_some :
    (LittleAbove (every A) μ c ↔ LittleBelow (Det.some A) μ c) ∧
      (LittleBelow (every A) μ c ↔ LittleAbove (Det.some A) μ c) :=
  ⟨by rw [littleBelow_iff_littleAbove_dual, dual_some],
    by rw [littleBelow_iff_littleAbove_dual, dual_every]⟩

/-- (32): a comparative without *little* under a possibility modal has the subject above every
accessible measure. -/
theorem more_some_iff :
    scopeDegrees (Det.some A) (Iic ∘ μ) ⊂ Iic c ↔ ∀ v ∈ A, μ v < c :=
  ⟨fun h v hv ↦ lt_of_not_ge fun hc ↦ h.2 fun _ he ↦ ⟨v, hv, le_trans he hc⟩,
    fun h ↦ ⟨fun _ ⟨v, hv, he⟩ ↦ le_trans he (h v hv).le,
      fun hsub ↦ let ⟨v, hv, hc⟩ := hsub (le_refl c); (h v hv).not_ge hc⟩⟩

-- (29): an antonym that reverses the scale commutes with any quantifier.
theorem scopeDegrees_neg {G : Type*} [Neg G] (Q : Quantifier W) (P : W → Set G) :
    scopeDegrees Q (fun v ↦ Neg.neg ⁻¹' P v) = Neg.neg ⁻¹' scopeDegrees Q P :=
  scopeDegrees_preimage _ Q P

end General

/-! ### The model of (14) -/

/-- (14): the measure at each of six worlds, `10 n` at the `n`th. -/
def measure (v : Fin 6) : ℕ := 10 * (v + 1)

/-- (14): the accessible worlds, the second to the fourth. -/
def acc : Set (Fin 6) := {1, 2, 3}

theorem isLeast_measure : IsLeast (measure '' acc) 20 :=
  ⟨⟨1, .inl rfl, rfl⟩, by rintro _ ⟨v, rfl | rfl | rfl, rfl⟩ <;> decide⟩

theorem isGreatest_measure : IsGreatest (measure '' acc) 40 :=
  ⟨⟨3, .inr (.inr rfl), rfl⟩, by rintro _ ⟨v, rfl | rfl | rfl, rfl⟩ <;> decide⟩

/-- (22a): with *little* below *allowed*, Lucinda drives below the minimum speed, 20. -/
theorem lessThanMinimum_iff {c : ℕ} : LittleBelow (Det.some acc) measure c ↔ c < 20 :=
  littleBelow_some_iff_of_isGLB isLeast_measure.isGLB

/-- (22b): with *little* above *allowed*, Lucinda drives below the maximum speed, 40. -/
theorem lessThanMaximum_iff {c : ℕ} : LittleAbove (Det.some acc) measure c ↔ c < 40 :=
  littleAbove_some_iff_of_isLUB isGreatest_measure.isLUB

-- (13b), (13c): *very little* under *can* asks the interval to lie above 20, over it above 40.
theorem veryLittle_iff {L : Set ℕ} :
    (Det.some acc {v | L ⊆ (Iic (measure v))ᶜ} → ∀ l ∈ L, 20 < l) ∧
      (L ⊆ (scopeDegrees (Det.some acc) (Iic ∘ measure))ᶜ ↔ ∀ l ∈ L, 40 < l) := by
  refine ⟨fun ⟨v, hv, h⟩ l hl ↦ ?_, ?_⟩
  · exact (isLeast_measure.2 ⟨v, hv, rfl⟩).trans_lt (subset_compl_Iic_iff.mp h l hl)
  · rw [compl_scopeDegrees_some_of_isGreatest isGreatest_measure]
    rfl

end Heim2006
