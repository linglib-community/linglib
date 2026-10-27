module

public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Pragmatics.RSA.QUD
public import Linglib.Data.Examples.Warstadt2022

/-!
# Warstadt (2022): Presupposition Triggering Reflects Pragmatic Reasoning About Utterance Utility

Warstadt derives soft presupposition triggers from a listener's inference about the common ground
the speaker assumed. The model is Qing, Goodman and Lassiter's. Within a context set the literal
listener conditions the prior on the utterance and answers the question under discussion (`L0`),
the speaker is informative about the answer at her world and says nothing false there
(`speaker`), and the pragmatic listener inverts the speaker jointly over worlds and context sets
(`listener`).

## Main results

* `needVisa_nonUS_lt`: asked whether Tom needs a visa, a listener who hears *Tom doesn't have a
  green card* favours the world where Tom is a non-US citizen over the one where he is a US
  citizen, at every rationality.
* `freeDrink_exhaustive`, `freeDrink_nonUS_lt`: asked whether Tom gets a free drink, the
  utterance settles the question in every context set, and the listener still favours the non-US
  world.
* `notSprinter_exhaustive_iff`: *not an Olympic sprinter* settles which kind of athlete Tom is,
  at the world where he is another runner, exactly within context sets that exclude the athlete
  and the non-athlete worlds.
* `other_share_lt`: at the non-athlete world *not an Olympic sprinter* is produced more often than
  silence and less often than *not a runner*.

## Implementation notes

* Utterances carry no cost.
* The paper gives a false utterance a utility of minus infinity. Here the speaker who addresses
  the question is conditioned on the utterances true at her world, which is the same distribution
  wherever some true utterance has positive weight.
* Shares are evaluated cell by cell from tables of natural-number weights (`weight`), certified by
  `decide`, and the listener comparisons are prior-weighted sums over the eight context sets.

## TODO

* The paper reports the free-drink posteriors of its second figure as nearly equal. Under the
  model as written the non-US world is favoured under both questions.
* The family-genus-species listener of the paper's third figure is not formalized.

## References

* [warstadt-2022]
* [qing-goodman-lassiter-2016]
* [abusch-2002]
* [frank-goodman-2012]
* [stalnaker-1978]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace Warstadt2022

private theorem toReal_frac_rpow (n m : ℕ) (α : ℝ) :
    (((n : ℝ≥0∞) / m) ^ α).toReal = ((n : ℝ) / m) ^ α := by
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-! ### The model (3) -/

section Model

variable {W U Q : Type} [DecidableEq W]

/-- The speaker's weight on an utterance at a world before the rationality exponent (3c), as a
numerator and a denominator. Where the utterance is true it is the literal listener's probability
of the world's answer, the prior weight of the context-set worlds that make the utterance true
and share the answer over that of those that make it true. Where it is false it is `0` over
`1`. -/
def weight (P : W → ℕ) (cell : Q → W → Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (C : Finset W) (q : Q) (u : U) (w : W) : ℕ × ℕ :=
  if w ∈ sem u then
    (∑ v ∈ (C.filter (· ∈ sem u)).filter (fun v ↦ cell q v = cell q w), P v,
      ∑ v ∈ C.filter (· ∈ sem u), P v)
  else (0, 1)

variable [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

/-- In the prior over pairs of a world and a context set (3d), a world's weight within a
context set is its prior share of the set, and context sets are equally likely. -/
noncomputable def pairPrior (P : W → ℕ) : Measure (W × Finset W) :=
  Measure.count.withDensity fun p ↦
    if p.1 ∈ p.2 then (P p.1 : ℝ≥0∞) / ∑ v ∈ p.2, (P v : ℝ≥0∞) else 0

theorem pairPrior_singleton (P : W → ℕ) (w : W) (C : Finset W) :
    pairPrior P {(w, C)}
      = if w ∈ C then (P w : ℝ≥0∞) / ∑ v ∈ C, (P v : ℝ≥0∞) else 0 := by
  rw [pairPrior, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    Measure.count_singleton, mul_one]

theorem pairPrior_singleton_le_one (P : W → ℕ) (w : W) (C : Finset W) :
    pairPrior P {(w, C)} ≤ 1 := by
  rw [pairPrior_singleton]
  split_ifs with h
  · exact ENNReal.div_le_of_le_mul (by
      rw [one_mul]
      exact Finset.single_le_sum (f := fun v ↦ (P v : ℝ≥0∞)) (fun _ _ ↦ zero_le) h)
  · exact zero_le_one

theorem pairPrior_real (P : W → ℕ) (w : W) (C : Finset W) :
    (pairPrior P).real {(w, C)}
      = if w ∈ C then (P w : ℝ) / ∑ v ∈ C, (P v : ℝ) else 0 := by
  rw [measureReal_def, pairPrior_singleton]
  split_ifs
  · rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun _ _ ↦ ENNReal.natCast_ne_top _]
    simp only [ENNReal.toReal_natCast]
  · exact ENNReal.toReal_zero

instance (P : W → ℕ) : IsFiniteMeasure (pairPrior P) :=
  ⟨by
    rw [pairPrior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
      tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun p _ ↦
      lt_of_le_of_lt (by rw [← pairPrior_singleton]; exact pairPrior_singleton_le_one P p.1 p.2)
        ENNReal.one_lt_top⟩

variable [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] (P : W → ℕ)
  (cell : Q → W → Finset W) (sem : U → Set W) (C : Finset W) (q : Q)

/-- The literal listener within a context set (3a) conditions the prior on the context set and
on the utterance, and answers the question. -/
noncomputable def L0 : Kernel U (Finset W) :=
  (RSA.listener ((Measure.ofWeights (P ·)).restrict ↑C) (truthful sem)).map (cell q)

instance : IsFiniteKernel (L0 P cell sem C q) := inferInstanceAs (IsFiniteKernel (Kernel.map _ _))

/-- The speaker within a context set (3b) is informative about the answer at her world, with no
cost, and says nothing false there (3c). -/
noncomputable def speaker (α : ℝ) (w : W) : Measure U :=
  (RSA.speaker α 0 (L0 P cell sem C q) Measure.dirac (cell q w))[|{u | w ∈ sem u}]

instance (α : ℝ) (w : W) : IsFiniteMeasure (speaker P cell sem C q α w) :=
  inferInstanceAs (IsFiniteMeasure (cond _ _))

/-- The share of an utterance at a world within a context set, on reals. -/
noncomputable def share (u : U) (w : W) (α : ℝ) : ℝ := (speaker P cell sem C q α w).real {u}

/-- The pragmatic listener (3d) inverts the speaker jointly over worlds and context sets, given
the question. -/
noncomputable def listener (α : ℝ) : Kernel U (W × Finset W) :=
  RSA.listener (pairPrior P) fun p ↦ speaker P cell sem p.2 q α p.1

/-- The pairs whose world is `w`. -/
def worldEvent (w : W) : Finset (W × Finset W) := Finset.univ.image fun C ↦ (w, C)

theorem listener_worldEvent_lt_iff {α : ℝ} {u : U} (w₁ w₂ : W) :
    (listener P cell sem q α u).real ↑(worldEvent w₁)
        < (listener P cell sem q α u).real ↑(worldEvent w₂)
      ↔ (∑ C, (pairPrior P).real {(w₁, C)} * share P cell sem C q u w₁ α)
        < ∑ C, (pairPrior P).real {(w₂, C)} * share P cell sem C q u w₂ α := by
  unfold listener worldEvent
  rw [RSA.listener_real_finset_lt_iff,
    Finset.sum_image fun _ _ _ _ h ↦ (Prod.mk.inj h).2,
    Finset.sum_image fun _ _ _ _ h ↦ (Prod.mk.inj h).2]
  rfl

variable {P cell sem C q} [∀ u, DecidablePred (· ∈ sem u)] [DiscreteMeasurableSpace W] {u : U}
  {w : W}

theorem L0_apply (h : w ∈ sem u) :
    L0 P cell sem C q u {cell q w}
      = ((weight P cell sem C q u w).1 : ℝ≥0∞) / (weight P cell sem C q u w).2 := by
  have e1 : sem u ∩ ↑C = ↑(C.filter (· ∈ sem u)) := by ext; simp [and_comm]
  have e2 : sem u ∩ cell q ⁻¹' {cell q w} ∩ ↑C
      = ↑((C.filter (· ∈ sem u)).filter fun v ↦ cell q v = cell q w) := by
    ext; simp; tauto
  rw [L0, listener_truthful_map_apply_singleton, Measure.restrict_apply .of_discrete,
    Measure.restrict_apply .of_discrete, e1, e2, Measure.ofWeights_apply_finset,
    Measure.ofWeights_apply_finset]
  simp only [weight, ite_eq_left h, Nat.cast_sum]

theorem L0_apply_eq_one_iff (h : w ∈ sem u) (hC : w ∈ C) (hP : P w ≠ 0) :
    L0 P cell sem C q u {cell q w} = 1
      ↔ (weight P cell sem C q u w).1 = (weight P cell sem C q u w).2 := by
  have h2 : (weight P cell sem C q u w).2 ≠ 0 := by
    simp only [weight, ite_eq_left h]
    exact Finset.sum_eq_zero_iff.not.mpr fun hz ↦ hP (hz w (Finset.mem_filter.mpr ⟨hC, h⟩))
  rw [L0_apply h, ENNReal.div_eq_one_iff (Nat.cast_ne_zero.mpr h2) (ENNReal.natCast_ne_top _),
    Nat.cast_inj]

theorem share_eq {α : ℝ} (hα : 0 < α) :
    share P cell sem C q u w α
      = (((weight P cell sem C q u w).1 : ℝ) / (weight P cell sem C q u w).2) ^ α
        / ∑ u', (((weight P cell sem C q u' w).1 : ℝ) / (weight P cell sem C q u' w).2) ^ α := by
  have hw (u' : U) : (((weight P cell sem C q u' w).1 : ℝ) / (weight P cell sem C q u' w).2) ^ α
      = if w ∈ sem u' then (L0 P cell sem C q u' {cell q w} ^ α).toReal else 0 := by
    split_ifs with h
    · rw [L0_apply h, toReal_frac_rpow]
    · simp [weight, ite_eq_right h, Real.zero_rpow hα.ne']
  have hT : {u' | w ∈ sem u'} = ↑(Finset.univ.filter fun u' ↦ w ∈ sem u') := by ext; simp
  have hnum (μ : Measure U) :
      μ.real ({u' | w ∈ sem u'} ∩ {u}) = if w ∈ sem u then μ.real {u} else 0 := by
    split_ifs with h
    · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr (by exact h))]
    · rw [Set.inter_singleton_eq_empty.mpr (by exact h), measureReal_empty]
  simp only [hw]
  rw [share, speaker, cond_real_apply _ (Set.toFinite _).measurableSet, hnum, hT,
    ← sum_measureReal_singleton,
    ← Finset.sum_filter]
  split_ifs with h
  · simp only [speaker_dirac_zero_real_singleton hα.le, ← Finset.sum_div]
    rcases eq_or_ne (∑ u', (L0 P cell sem C q u' {cell q w} ^ α).toReal) 0 with hZ | hZ
    · rw [(Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg).mp hZ u
        (Finset.mem_univ u), zero_div, zero_div, zero_div]
    · rw [div_div_div_cancel_right₀ hZ]
  · rw [zero_div, zero_div]

end Model

/-! ### The green card scenario (Table 1) -/

/-- Tom is a US citizen, a green card holder, or a non-US citizen without a green card. -/
inductive World
  | usCitizen | gcHolder | nonUS
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩
instance : MeasurableSingletonClass World := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Silence, *US citizen*, *not US citizen*, *green card*, *not green card*. -/
inductive Utterance
  | silence | us | notUS | gc | notGC
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩
instance : MeasurableSingletonClass Utterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The truth conditions follow Table 1, and a negation is the complement. -/
def Utterance.sem : Utterance → Set World
  | .silence => Set.univ
  | .us => {w | w = .usCitizen}
  | .notUS => {w | w ≠ .usCitizen}
  | .gc => {w | w = .gcHolder}
  | .notGC => {w | w ≠ .gcHolder}

instance : ∀ u : Utterance, DecidablePred (· ∈ u.sem)
  | .silence, _ => inferInstanceAs (Decidable True)
  | .us, w => inferInstanceAs (Decidable (w = _))
  | .notUS, w => inferInstanceAs (Decidable (w ≠ _))
  | .gc, w => inferInstanceAs (Decidable (w = _))
  | .notGC, w => inferInstanceAs (Decidable (w ≠ _))

/-- Does Tom need a visa? Can Tom get a free drink? -/
inductive QUD
  | needVisa | freeDrink
  deriving DecidableEq, Repr

/-- The answer of a world to a question. -/
def QUD.answer : QUD → World → Bool
  | .needVisa, w => decide (w = .nonUS)
  | .freeDrink, w => decide (w = .gcHolder)

/-- The cell of a world holds the worlds with the same answer. -/
def QUD.cell (q : QUD) (w : World) : Finset World := Finset.univ.filter (q.answer · = q.answer w)

/-- The context sets containing the non-US world, and those containing the US-citizen world. -/
def nonUSSets : List (Finset World) :=
  [{.nonUS}, {.usCitizen, .nonUS}, {.gcHolder, .nonUS}, {.usCitizen, .gcHolder, .nonUS}]

def usSets : List (Finset World) :=
  [{.usCitizen}, {.usCitizen, .gcHolder}, {.usCitizen, .nonUS}, {.usCitizen, .gcHolder, .nonUS}]

/-- The uniform world prior. -/
def uniform : World → ℕ := fun _ ↦ 1

/-- *Not green card* settles the free-drink question in every context set, since at a world
where it is true the literal listener is certain of the answer. -/
theorem freeDrink_exhaustive {C : Finset World} {w : World} (hC : w ∈ C)
    (h : w ∈ Utterance.notGC.sem) :
    L0 uniform QUD.cell Utterance.sem C .freeDrink .notGC {QUD.cell .freeDrink w} = 1 :=
  (L0_apply_eq_one_iff h hC one_ne_zero).mpr (by revert C w; decide)

theorem needVisa_not_exhaustive :
    L0 uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .needVisa .notGC
        {QUD.cell .needVisa .usCitizen} = 1 / 2 ∧
      L0 uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} .needVisa .notGC
        {QUD.cell .needVisa .nonUS} = 1 := by
  rw [L0_apply (by decide), L0_apply (by decide),
    show weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .needVisa .notGC
      .usCitizen = (1, 2) by decide,
    show weight uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} .needVisa .notGC .nonUS
      = (1, 1) by decide]
  norm_num

/-! #### Shares -/

private theorem sum_utterance {M : Type*} [AddCommMonoid M] (f : Utterance → M) :
    ∑ u, f u = f .silence + f .us + f .notUS + f .gc + f .notGC := by
  rw [show (Finset.univ : Finset Utterance) = {.silence, .us, .notUS, .gc, .notGC} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]

private theorem share_expand (C : Finset World) (q : QUD) (w : World) {α : ℝ} (hα : 0 < α)
    (tbl : Utterance → ℕ × ℕ)
    (htbl : ∀ u, weight uniform QUD.cell Utterance.sem C q u w = tbl u) :
    share uniform QUD.cell Utterance.sem C q .notGC w α =
      (((tbl .notGC).1 : ℝ) / (tbl .notGC).2) ^ α /
        (((tbl .silence).1 / (tbl .silence).2) ^ α + ((tbl .us).1 / (tbl .us).2) ^ α
          + ((tbl .notUS).1 / (tbl .notUS).2) ^ α + ((tbl .gc).1 / (tbl .gc).2) ^ α
          + ((tbl .notGC).1 / (tbl .notGC).2) ^ α) := by
  rw [share_eq hα, sum_utterance]
  simp only [htbl]

section Tables

/-- Weights at the non-US world within its singleton context set, both questions. -/
private def tblN1 : Utterance → ℕ × ℕ
  | .silence => (1, 1) | .us => (0, 1) | .notUS => (1, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem weight_N1 (q : QUD) : ∀ u,
    weight uniform QUD.cell Utterance.sem {.nonUS} q u .nonUS = tblN1 u := by
  cases q <;> decide

/-- Weights at the non-US world within `{usCitizen, nonUS}`, visa question. -/
private def tblN2 : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (0, 1) | .notUS => (1, 1) | .gc => (0, 1) | .notGC => (1, 2)

private theorem weight_N2 : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa u .nonUS = tblN2 u := by
  decide

/-- Weights at the non-US world within `{gcHolder, nonUS}`, both questions. -/
private def tblN3 : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (0, 1) | .notUS => (1, 2) | .gc => (0, 1) | .notGC => (1, 1)

private theorem weight_N3 (q : QUD) : ∀ u,
    weight uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} q u .nonUS = tblN3 u := by
  cases q <;> decide

/-- Weights at the non-US world in the universe, visa question. -/
private def tblN4 : Utterance → ℕ × ℕ
  | .silence => (1, 3) | .us => (0, 1) | .notUS => (1, 2) | .gc => (0, 1) | .notGC => (1, 2)

private theorem weight_N4 : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .needVisa u .nonUS
      = tblN4 u := by
  decide

/-- Weights at the US-citizen world within its singleton context set, both questions. -/
private def tblU1 : Utterance → ℕ × ℕ
  | .silence => (1, 1) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem weight_U1 (q : QUD) : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen} q u .usCitizen = tblU1 u := by
  cases q <;> decide

/-- Weights at the US-citizen world within `{usCitizen, gcHolder}`, visa question. -/
private def tblU2 : Utterance → ℕ × ℕ
  | .silence => (2, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem weight_U2 : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder} .needVisa u .usCitizen
      = tblU2 u := by
  decide

/-- Weights at the US-citizen world within `{usCitizen, nonUS}`, visa question. -/
private def tblU3 : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 2)

private theorem weight_U3 : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa u .usCitizen
      = tblU3 u := by
  decide

/-- Weights at the US-citizen world in the universe, visa question. -/
private def tblU4 : Utterance → ℕ × ℕ
  | .silence => (2, 3) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 2)

private theorem weight_U4 : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .needVisa u .usCitizen
      = tblU4 u := by
  decide

/-- Weights at the non-US world within `{usCitizen, nonUS}`, free-drink question. -/
private def tblN2' : Utterance → ℕ × ℕ
  | .silence => (2, 2) | .us => (0, 1) | .notUS => (1, 1) | .gc => (0, 1) | .notGC => (2, 2)

private theorem weight_N2' : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink u .nonUS = tblN2' u := by
  decide

/-- Weights at the non-US world in the universe, free-drink question. -/
private def tblN4' : Utterance → ℕ × ℕ
  | .silence => (2, 3) | .us => (0, 1) | .notUS => (1, 2) | .gc => (0, 1) | .notGC => (2, 2)

private theorem weight_N4' : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .freeDrink u .nonUS
      = tblN4' u := by
  decide

/-- Weights at the US-citizen world within `{usCitizen, gcHolder}`, free-drink question. -/
private def tblU2' : Utterance → ℕ × ℕ
  | .silence => (1, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (1, 1)

private theorem weight_U2' : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder} .freeDrink u .usCitizen
      = tblU2' u := by
  decide

/-- Weights at the US-citizen world within `{usCitizen, nonUS}`, free-drink question. -/
private def tblU3' : Utterance → ℕ × ℕ
  | .silence => (2, 2) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (2, 2)

private theorem weight_U3' : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink u .usCitizen
      = tblU3' u := by
  decide

/-- Weights at the US-citizen world in the universe, free-drink question. -/
private def tblU4' : Utterance → ℕ × ℕ
  | .silence => (2, 3) | .us => (1, 1) | .notUS => (0, 1) | .gc => (0, 1) | .notGC => (2, 2)

private theorem weight_U4' : ∀ u,
    weight uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS} .freeDrink u .usCitizen
      = tblU4' u := by
  decide

end Tables

section Cells

variable {α : ℝ} (hα : 0 < α)
include hα

private theorem share_N1 (q : QUD) : share uniform QUD.cell Utterance.sem {.nonUS} q .notGC
    .nonUS α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblN1 (weight_N1 q)]
  dsimp only [tblN1]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_N2 : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa
    .notGC .nonUS α = (1 / 2 : ℝ) ^ α / (1 + 2 * (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN2 weight_N2]
  dsimp only [tblN2]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_N3 (q : QUD) : share uniform QUD.cell Utterance.sem {.gcHolder, .nonUS} q
    .notGC .nonUS α = 1 / (1 + 2 * (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN3 (weight_N3 q)]
  dsimp only [tblN3]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_N4 : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .needVisa .notGC .nonUS α
      = (1 / 2 : ℝ) ^ α / (2 * (1 / 2 : ℝ) ^ α + (1 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN4 weight_N4]
  dsimp only [tblN4]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U1 (q : QUD) : share uniform QUD.cell Utterance.sem {.usCitizen} q .notGC
    .usCitizen α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblU1 (weight_U1 q)]
  dsimp only [tblU1]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_U2 : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder} .needVisa
    .notGC .usCitizen α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblU2 weight_U2]
  dsimp only [tblU2]
  norm_num [Real.zero_rpow hα.ne']

private theorem share_U3 : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .needVisa
    .notGC .usCitizen α = (1 / 2 : ℝ) ^ α / (1 + 2 * (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU3 weight_U3]
  dsimp only [tblU3]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U4 : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .needVisa .notGC .usCitizen α
      = (1 / 2 : ℝ) ^ α / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU4 weight_U4]
  dsimp only [tblU4]
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_N2' : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink
    .notGC .nonUS α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblN2' weight_N2']
  dsimp only [tblN2']
  norm_num [Real.zero_rpow hα.ne']

private theorem share_N4' : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .freeDrink .notGC .nonUS α = 1 / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblN4' weight_N4']
  dsimp only [tblN4']
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U2' : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder}
    .freeDrink .notGC .usCitizen α = 1 / (2 + (1 / 2 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU2' weight_U2']
  dsimp only [tblU2']
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

private theorem share_U3' : share uniform QUD.cell Utterance.sem {.usCitizen, .nonUS} .freeDrink
    .notGC .usCitizen α = 1 / 3 := by
  rw [share_expand _ _ _ hα tblU3' weight_U3']
  dsimp only [tblU3']
  norm_num [Real.zero_rpow hα.ne']

private theorem share_U4' : share uniform QUD.cell Utterance.sem {.usCitizen, .gcHolder, .nonUS}
    .freeDrink .notGC .usCitizen α = 1 / (2 + (2 / 3 : ℝ) ^ α) := by
  rw [share_expand _ _ _ hα tblU4' weight_U4']
  dsimp only [tblU4']
  norm_num [Real.zero_rpow hα.ne']
  first | done | ring

end Cells

/-! #### The listener over worlds -/

/-- The joint listener of the green card scenario. -/
noncomputable def gcListener (q : QUD) (α : ℝ) : Kernel Utterance (World × Finset World) :=
  listener uniform QUD.cell Utterance.sem q α

private theorem sum_ctx {M : Type*} [AddCommMonoid M] (f : Finset World → M) :
    ∑ C, f C = f ∅ + f {.usCitizen} + f {.gcHolder} + f {.nonUS} + f {.usCitizen, .gcHolder}
      + f {.usCitizen, .nonUS} + f {.gcHolder, .nonUS} + f {.usCitizen, .gcHolder, .nonUS} := by
  rw [show (Finset.univ : Finset (Finset World)) = {∅, {.usCitizen}, {.gcHolder}, {.nonUS},
      {.usCitizen, .gcHolder}, {.usCitizen, .nonUS}, {.gcHolder, .nonUS},
      {.usCitizen, .gcHolder, .nonUS}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]

private theorem pairPrior_uniform_real (w : World) (C : Finset World) :
    (pairPrior uniform).real {(w, C)} = if w ∈ C then 1 / (C.card : ℝ) else 0 := by
  rw [pairPrior_real]
  simp [uniform]

private theorem card_two {a b : World} (h : a ≠ b) : ({a, b} : Finset World).card = 2 := by
  rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr h), Finset.card_singleton]

private theorem card_three : ({.usCitizen, .gcHolder, .nonUS} : Finset World).card = 3 := by
  decide

private theorem half_rpow_lt_one {α : ℝ} (hα : 0 < α) : (1 / 2 : ℝ) ^ α < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hα

/-- With the question whether Tom needs a visa, *not green card* makes the listener favour the
non-US world over the US-citizen world (Figure 1). -/
theorem needVisa_nonUS_lt {α : ℝ} (hα : 0 < α) :
    (gcListener .needVisa α .notGC).real ↑(worldEvent World.usCitizen)
      < (gcListener .needVisa α .notGC).real ↑(worldEvent World.nonUS) := by
  rw [gcListener, listener_worldEvent_lt_iff, sum_ctx, sum_ctx]
  simp (config := { decide := true }) only [pairPrior_uniform_real, ite_true, ite_false]
  rw [card_two (by decide), card_two (by decide), card_two (by decide), card_three]
  norm_num
  rw [share_N1 hα, share_N2 hα, share_N3 hα, share_N4 hα, share_U1 hα, share_U2 hα,
    share_U3 hα, share_U4 hα]
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hy0 : (0 : ℝ) < (1 / 3 : ℝ) ^ α := by positivity
  have hyz : (1 / 3 : ℝ) ^ α < (2 / 3 : ℝ) ^ α :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hα
  have h1 : (1 : ℝ) / 3 < 1 / (1 + 2 * (1 / 2 : ℝ) ^ α) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h2 : (1 / 2 : ℝ) ^ α / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α)
      < (1 / 2 : ℝ) ^ α / (2 * (1 / 2 : ℝ) ^ α + (1 / 3 : ℝ) ^ α) :=
    div_lt_div_of_pos_left hx0 (by positivity) (by linarith)
  linarith

/-- With the question whether Tom gets a free drink, *not green card* still makes the listener
favour the non-US world (Figure 2). -/
theorem freeDrink_nonUS_lt {α : ℝ} (hα : 0 < α) :
    (gcListener .freeDrink α .notGC).real ↑(worldEvent World.usCitizen)
      < (gcListener .freeDrink α .notGC).real ↑(worldEvent World.nonUS) := by
  rw [gcListener, listener_worldEvent_lt_iff, sum_ctx, sum_ctx]
  simp (config := { decide := true }) only [pairPrior_uniform_real, ite_true, ite_false]
  rw [card_two (by decide), card_two (by decide), card_two (by decide), card_three]
  norm_num
  rw [share_N1 hα, share_N2' hα, share_N3 hα, share_N4' hα, share_U1 hα, share_U2' hα,
    share_U3' hα, share_U4' hα]
  have hx := half_rpow_lt_one hα
  have hx0 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := by positivity
  have hz0 : (0 : ℝ) < (2 / 3 : ℝ) ^ α := by positivity
  have h1 : (1 : ℝ) / (2 + (1 / 2 : ℝ) ^ α) < 1 / (1 + 2 * (1 / 2 : ℝ) ^ α) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h2 : (1 : ℝ) / (2 + (2 / 3 : ℝ) ^ α)
      < 1 / (1 + (1 / 2 : ℝ) ^ α + (2 / 3 : ℝ) ^ α) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-! ### The family-genus-species scenario (Table 2) -/

/-- Tom is an Olympic sprinter, another runner, another athlete, or none of these. -/
inductive Hobby
  | sprinter | runner | athlete | other
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace Hobby := ⊤
instance : DiscreteMeasurableSpace Hobby := ⟨fun _ ↦ trivial⟩
instance : MeasurableSingletonClass Hobby := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The three predicates, affirmed or negated, and silence. -/
inductive HobbyUtterance
  | silence | sprinter | notSprinter | runner | notRunner | athlete | notAthlete
  deriving DecidableEq, Fintype, Repr, Inhabited

instance : MeasurableSpace HobbyUtterance := ⊤
instance : DiscreteMeasurableSpace HobbyUtterance := ⟨fun _ ↦ trivial⟩
instance : MeasurableSingletonClass HobbyUtterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The truth conditions of Table 2, respecting the hierarchy of the predicates. -/
def HobbyUtterance.sem : HobbyUtterance → Set Hobby
  | .silence => Set.univ
  | .sprinter => {w | w = .sprinter}
  | .notSprinter => {w | w ≠ .sprinter}
  | .runner => {w | w = .sprinter ∨ w = .runner}
  | .notRunner => {w | ¬ (w = .sprinter ∨ w = .runner)}
  | .athlete => {w | w ≠ .other}
  | .notAthlete => {w | w = .other}

instance : ∀ u : HobbyUtterance, DecidablePred (· ∈ u.sem)
  | .silence, _ => inferInstanceAs (Decidable True)
  | .sprinter, w => inferInstanceAs (Decidable (w = _))
  | .notSprinter, w => inferInstanceAs (Decidable (w ≠ _))
  | .runner, w => inferInstanceAs (Decidable (w = _ ∨ w = _))
  | .notRunner, w => inferInstanceAs (Decidable (¬ (w = _ ∨ w = _)))
  | .athlete, w => inferInstanceAs (Decidable (w ≠ _))
  | .notAthlete, w => inferInstanceAs (Decidable (w = _))

/-- The prior of Table 2, in percent. -/
def hobbyWeight : Hobby → ℕ
  | .sprinter => 1
  | .runner => 5
  | .athlete => 10
  | .other => 84

/-- Under the question which world it is, every cell is a singleton. -/
def which (_ : Unit) (w : Hobby) : Finset Hobby := {w}

/-- The universe of hobbies. -/
def hobbies : Finset Hobby := {.sprinter, .runner, .athlete, .other}

/-- *Not an Olympic sprinter* settles the question at the runner world exactly within context
sets that exclude the athlete and the non-athlete world, so the accommodation the paper
describes is of a common ground in which Tom is a runner or a sprinter. -/
theorem notSprinter_exhaustive_iff {C : Finset Hobby} (hC : .runner ∈ C) :
    L0 hobbyWeight which HobbyUtterance.sem C () .notSprinter {which () .runner} = 1
      ↔ .athlete ∉ C ∧ .other ∉ C := by
  rw [L0_apply_eq_one_iff (by decide) hC (by decide)]
  revert C
  decide

theorem notRunner_exhaustive_iff {C : Finset Hobby} (hC : .athlete ∈ C) :
    L0 hobbyWeight which HobbyUtterance.sem C () .notRunner {which () .athlete} = 1
      ↔ .other ∉ C := by
  rw [L0_apply_eq_one_iff (by decide) hC (by decide)]
  revert C
  decide

private theorem sum_hobbyUtterance {M : Type*} [AddCommMonoid M] (f : HobbyUtterance → M) :
    ∑ u, f u = f .silence + f .sprinter + f .notSprinter + f .runner + f .notRunner + f .athlete
      + f .notAthlete := by
  rw [show (Finset.univ : Finset HobbyUtterance) = {.silence, .sprinter, .notSprinter, .runner,
      .notRunner, .athlete, .notAthlete} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

/-- Weights at the non-athlete world in the universe. -/
private def tblO : HobbyUtterance → ℕ × ℕ
  | .silence => (84, 100) | .sprinter => (0, 1) | .notSprinter => (84, 99) | .runner => (0, 1)
  | .notRunner => (84, 94) | .athlete => (0, 1) | .notAthlete => (84, 84)

private theorem weight_O : ∀ u,
    weight hobbyWeight which HobbyUtterance.sem hobbies () u .other = tblO u := by
  decide

private theorem share_other {α : ℝ} (hα : 0 < α) (u : HobbyUtterance) :
    share hobbyWeight which HobbyUtterance.sem hobbies () u .other α =
      (((tblO u).1 : ℝ) / (tblO u).2) ^ α /
        (((tblO .silence).1 / (tblO .silence).2) ^ α
          + ((tblO .sprinter).1 / (tblO .sprinter).2) ^ α
          + ((tblO .notSprinter).1 / (tblO .notSprinter).2) ^ α
          + ((tblO .runner).1 / (tblO .runner).2) ^ α
          + ((tblO .notRunner).1 / (tblO .notRunner).2) ^ α
          + ((tblO .athlete).1 / (tblO .athlete).2) ^ α
          + ((tblO .notAthlete).1 / (tblO .notAthlete).2) ^ α) := by
  rw [share_eq hα, sum_hobbyUtterance]
  simp only [weight_O]

/-- At the non-athlete world, *not an Olympic sprinter* is produced more often than silence but less
often than *not a runner* (4). -/
theorem other_share_lt {α : ℝ} (hα : 0 < α) :
    share hobbyWeight which HobbyUtterance.sem hobbies () .silence .other α
        < share hobbyWeight which HobbyUtterance.sem hobbies () .notSprinter .other α ∧
      share hobbyWeight which HobbyUtterance.sem hobbies () .notSprinter .other α
        < share hobbyWeight which HobbyUtterance.sem hobbies () .notRunner .other α ∧
      share hobbyWeight which HobbyUtterance.sem hobbies () .notRunner .other α
        < share hobbyWeight which HobbyUtterance.sem hobbies () .notAthlete .other α := by
  simp only [share_other hα]
  dsimp only [tblO]
  refine ⟨?_, ?_, ?_⟩ <;>
    exact div_lt_div_of_pos_right (Real.rpow_lt_rpow (by norm_num) (by norm_num) hα)
      (by positivity)

end Warstadt2022
