module

public import Linglib.Data.Examples.FoxHackl2006
public import Mathlib.Order.Interval.Set.Monotone
public import Linglib.Semantics.Questions.HamblinSet
public import Linglib.Semantics.Exhaustification.Pointwise
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Logic.Modal.Defs

/-!
# Fox and Hackl (2006): The Universal Density of Measurement

This file formalizes Fox and Hackl's Universal Density of Measurement, the claim that the
measurement scales of natural language semantics are dense, and the single mechanism it drives
through scalar implicatures, *only*, degree questions and definite descriptions. Each maximizes
a property of degrees with MAXinf, the most informative true degree, which is Dayal's strongest
true answer of the degree property (`Question.IsStrongestTrueAnswer`), and the Constraint on
Interval Maximization, `not_isExhaustivelyResolvable_of_isNecessarilyOpen`, says this fails on a
property that necessarily describes an open interval. *More than d* and *not … d* are such
properties, so they carry no implicature, reject *only*, and make negative islands; a universal
modal closes the interval (`isExhaustivelyResolvable_box`) and an existential modal does not
(`not_isGreatest_diamond`); at cardinality granularity *more than n* exhaustifies to
*exactly n + 1* (`moreThan_exact_nat`).

## Implementation notes

On a strictly antitone family the most informative degree is the greatest true one
(`Question.isExhaustivelyResolvable_range_iff_isGreatest`), so density removes it exactly when
the true set is open at its informative end; the downward-monotone cases are the order duals.
The paper's example sentences are the rows of `Examples.all`.

## References

* [fox-hackl-2006]
* [rullmann-1995]
* [beck-rullmann-1999]
* [dayal-1996]
* [hackl-2000]
-/

@[expose] public section

namespace FoxHackl2006

open Question ModalLogic OrderDual Set
open SetRel
open Degree

variable {D W : Type*} [LinearOrder D]

/-! ### Necessarily open properties -/

/-- A property of degrees necessarily describes an open interval when at every world some degree
fails it and every smaller degree satisfies it. -/
def IsNecessarilyOpen (φ : D → Set W) : Prop :=
  ∀ w, ∃ d, w ∉ φ d ∧ ∀ d' < d, w ∈ φ d'

/-- A property is necessarily open from below when at every world some degree fails it and every
larger degree satisfies it. -/
abbrev IsNecessarilyOpenBelow (φ : D → Set W) : Prop :=
  IsNecessarilyOpen fun d : Dᵒᵈ => φ (ofDual d)

/-- By the Constraint on Interval Maximization (42), on a dense scale a necessarily open
upward-monotone property has no most informative degree. -/
theorem not_isExhaustivelyResolvable_of_isNecessarilyOpen [DenselyOrdered D] {φ : D → Set W}
    (hφ : StrictAnti φ) (hopen : IsNecessarilyOpen φ) (w : W) :
    ¬ IsExhaustivelyResolvable (range φ) w :=
  (isExhaustivelyResolvable_range_iff_isGreatest hφ).not.2 fun ⟨_, hm⟩ =>
    let ⟨_, hd, hlt⟩ := hopen w
    let ⟨y, hmy, hyd⟩ := exists_between (lt_of_not_ge fun h => hd (hφ.antitone h hm.1))
    not_le.2 hmy (hm.2 (hlt y hyd))

-- (42)
theorem not_isExhaustivelyResolvable_of_isNecessarilyOpenBelow [DenselyOrdered D] {φ : D → Set W}
    (hφ : StrictMono φ) (hopen : IsNecessarilyOpenBelow φ) (w : W) :
    ¬ IsExhaustivelyResolvable (range φ) w :=
  not_isExhaustivelyResolvable_of_isNecessarilyOpen (φ := fun d : Dᵒᵈ => φ (ofDual d))
    (fun _ _ h => hφ h) hopen w

/-! ### Implicatures and *only* -/

theorem isNecessarilyOpen_gt_over (μ : W → D) : IsNecessarilyOpen (μ ⁻¹' Set.Ioi ·) :=
  fun w => ⟨μ w, lt_irrefl _, fun _ h => h⟩

-- (2), (5), (7b–c)
theorem moreThan_not_isExhaustivelyResolvable [DenselyOrdered D] (μ : W → D)
    (hμ : Function.Surjective μ) (w : W) : ¬ IsExhaustivelyResolvable (range (μ ⁻¹' Set.Ioi ·)) w :=
  not_isExhaustivelyResolvable_of_isNecessarilyOpen
    ((Set.monotone_preimage.comp_antitone antitone_Ioi).strictAnti_of_injective
      ((Set.preimage_injective.2 hμ).comp Set.Ioi_injective))
    (isNecessarilyOpen_gt_over μ) w

theorem exhAgainst_lt_iff_isStrongestTrueAnswer {φ : D → Set W} (hφ : StrictAnti φ) {i : D}
    {w : W} :
    Exhaustification.exhAgainst (· < ·) (w ∈ φ ·) i ↔ IsStrongestTrueAnswer (range φ) w (φ i) :=
  (Exhaustification.mem_exh_range_iff_exhAgainst_lt hφ i w).symm.trans
    (mem_exh_iff_isStrongestTrueAnswer (mem_range_self i))

/-! ### Modal operators -/

/-- The deontic modal base whose only requirement is `φ a` is the set of worlds where `φ` holds
of some degree above `a`. -/
abbrev requirementBase (φ : D → Set W) (a : D) : SetRel W W :=
  {p | ∃ d, a < d ∧ p.2 ∈ φ d}

-- (46)
theorem box_eq_Iic [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ) (a : D) (w : W) :
    {d | w ∈ (requirementBase φ a).core (φ d)} = Iic a := by
  ext d'
  constructor
  · intro h
    by_contra hd'
    obtain ⟨m, ham, hmd'⟩ := exists_between (not_le.1 hd')
    obtain ⟨u, hu, hu'⟩ := Set.exists_of_ssubset (hφ hmd')
    exact hu' (h ⟨m, ham, hu⟩)
  · intro hd' u hu
    obtain ⟨d, had, hu⟩ := hu
    exact hφ.antitone ((hd' : d' ≤ a).trans had.le) hu

/-- A universal modal closes the interval, so *required to φ more than d* has a most informative
degree, `a` itself ((13), (46)). -/
theorem isExhaustivelyResolvable_box [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ)
    (a : D) (w : W) :
    IsExhaustivelyResolvable (range fun d => (requirementBase φ a).core (φ d)) w := by
  have hanti : Antitone fun d => (requirementBase φ a).core (φ d) :=
    fun _ _ h _ hv _ hu => hφ.antitone h (hv hu)
  refine isExhaustivelyResolvable_range_iff_exists.2 ⟨a, ?_⟩
  rw [IsStrongestTrueAnswer, trueAnswers_range]
  exact hanti.map_isGreatest (box_eq_Iic hφ a w ▸ isGreatest_Iic)

/-- Under an existential modal, the true degrees of *allowed to φ d* have no greatest element ((14),
(47)). -/
theorem not_isGreatest_diamond [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ)
    (hopen : IsNecessarilyOpen φ) (R : SetRel W W) (w : W) :
    ¬ ∃ m, IsGreatest {d | w ∈ R.preimage (φ d)} m := by
  rintro ⟨m, ⟨v, hvm, hv⟩, hub⟩
  obtain ⟨d, hd, hlt⟩ := hopen v
  have hmd : m < d := lt_of_not_ge fun h => hd (hφ.antitone h hvm)
  obtain ⟨y, hmy, hyd⟩ := exists_between hmd
  exact not_le.2 hmy (hub ⟨v, hlt y hyd, hv⟩)

/-! ### Negative islands -/

theorem isNecessarilyOpenBelow_lt_over (μ : W → D) :
    IsNecessarilyOpenBelow (μ ⁻¹' Set.Iio ·) :=
  isNecessarilyOpen_gt_over (toDual ∘ μ)

-- (16), (19a), (25)
theorem negation_not_isExhaustivelyResolvable [DenselyOrdered D] (μ : W → D)
    (hμ : Function.Surjective μ) (w : W) : ¬ IsExhaustivelyResolvable (range (μ ⁻¹' Set.Iio ·)) w :=
  not_isExhaustivelyResolvable_of_isNecessarilyOpenBelow
    ((Set.monotone_preimage.comp monotone_Iio).strictMono_of_injective
      ((Set.preimage_injective.2 hμ).comp Set.Iio_injective))
    (isNecessarilyOpenBelow_lt_over μ) w

-- (27b), (28a), (29a)
theorem isExhaustivelyResolvable_box_below [DenselyOrdered D] {φ : D → Set W} (hφ : StrictMono φ)
    (a : D) (w : W) :
    IsExhaustivelyResolvable (range fun d => SetRel.core {p | ∃ d, d < a ∧ p.2 ∈ φ d} (φ d)) w :=
  isExhaustivelyResolvable_box (φ := fun d : Dᵒᵈ => φ (ofDual d)) (fun _ _ h => hφ h) (toDual a) w

-- (28b), (29b), (47)
theorem not_isLeast_diamond [DenselyOrdered D] {φ : D → Set W} (hφ : StrictMono φ)
    (hopen : IsNecessarilyOpenBelow φ) (R : SetRel W W) (w : W) :
    ¬ ∃ m, IsLeast {d | w ∈ R.preimage (φ d)} m :=
  not_isGreatest_diamond (φ := fun d : Dᵒᵈ => φ (ofDual d)) (fun _ _ h => hφ h) hopen R w

/-! ### Cardinality as a level of granularity -/

/-- At cardinality granularity, *more than m* is strongest true iff the count is `m + 1`, so *only
more than 15F* means *exactly 16* ((73)–(75)). -/
theorem moreThan_exact_nat (μ : W → ℕ) (hμ : Function.Surjective μ) (m : ℕ) (w : W) :
    IsStrongestTrueAnswer (range (μ ⁻¹' Set.Ioi ·)) w (μ ⁻¹' Set.Ioi m) ↔ μ w = m + 1 := by
  refine isStrongestTrueAnswer_range_iff.trans ⟨fun ⟨h1, h2⟩ => ?_, fun h => ⟨?_, fun y hy => ?_⟩⟩
  · obtain ⟨v, hv⟩ := hμ (m + 1)
    by_contra hne
    have h1 : m < μ w := h1
    have h3 : m + 1 < μ v :=
      h2 (m + 1) (by change m + 1 < μ w; omega) (by change m < μ v; omega)
    omega
  · change m < μ w; omega
  · exact Set.preimage_mono (Set.Ioi_subset_Ioi (by change y < μ w at hy; omega))

end FoxHackl2006
