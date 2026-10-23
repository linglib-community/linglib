module

public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Fragments.English.Adjectives

/-!
# Nouwen (2024): The Semantics and Probabilistic Pragmatics of Deadjectival Intensifiers

This file formalizes Nouwen's probabilistic account of deadjectival intensifiers such as
*horribly warm* and *pleasantly warm*. The adverb contributes a second positive form: its
adjectival base measures the proposition that the subject has the degree it actually has, so
over the cells of the question under discussion raised by the adjective both the adjective
and the adverb are measure functions on the same states. Each positive form is interpreted as
in Lassiter and Goodman's threshold model, with a costly positive form competing against a
free silent message, and the listener's posterior over states is the state marginal of the
joint posterior over states and thresholds (`update`).

Because a speaker sees a state only through the thresholds the state meets, the posterior is
the prior reweighted by a quantity that grows with the set of thresholds met
(`update_mul_le_mul`, strictly in `update_mul_lt_mul`). For a single positive form this is the
upward shift along the measure function (`positiveForm_mul_le_mul`). The conjunctive model
resolves the two thresholds in tandem (`simultaneous`) and is ordered only by the two measures
jointly; Nouwen's final proposal backgrounds the adverb, updating first with the adverb's
positive form and then interpreting the adjective against that posterior (`sequential`), so
that the last update is ordered by the adjective's measure alone. The Goldilocks effect of
evaluation, negative evaluation growing and positive evaluation shrinking with excess, fixes
the direction of the shift (`sequential_mul_le_mul_of_negative`,
`sequential_mul_le_mul_of_positive`), with the valence read off the English fragment
(`horribly_mul_le_mul`, `pleasantly_mul_le_mul`). A measure function that does not distinguish
the states leaves the prior unchanged (`update_eq_self`). This is the intuition Nouwen offers
for the generalisation he credits to Zwicky, that positive modal adjectives such as *usual* do
not form intensifiers: if *usual* conveyed the prior, the intensified adjective would be
indistinguishable from the bare one (`sequential_eq_positiveForm`). Nouwen notes that the
intuition faces complications.

## Implementation notes

States are an arbitrary finite type standing for the cells of the question under discussion,
and a measure function is any map from states to a linear order, so the adverb's measure of
the proposition a cell expresses is a function on states like the adjective's. The three
models are instances of one update over a family of extensions indexed by a latent parameter:
a threshold, or a pair of thresholds for the conjunctive model. The threshold prior is a
parameter; the paper sums over thresholds unweighted.

## TODO

The simulations behind the paper's figures are not stated. In particular the residual mass
that the conjunctive model leaves on the cold extreme for *horribly warm*, the reason the
paper rejects it, is a quantitative fact about a discretized normal prior and a quadratic
measure, and so is the comparison between the intensified and the bare posterior. The
paper's discussion of why a predicative *normal* is informative while the adverb is not
is not formalized.

## References

* [R. Nouwen, *The Semantics and Probabilistic Pragmatics of Deadjectival Intensifiers*
  (2024)][nouwen-2024]
* [D. Lassiter and N. D. Goodman, *Adjectival Vagueness in a Bayesian Model of Interpretation*
  (2017)][lassiter-goodman-2017]
* [A. M. Zwicky, *Usually and Unusually* (1970)][zwicky-1970]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace Nouwen2024

/-- The messages of the threshold model are the positive form and saying nothing. -/
inductive Message
  | positive | silent
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Message := ⊤
instance : DiscreteMeasurableSpace Message := ⟨fun _ ↦ trivial⟩
instance : Nonempty Message := ⟨.silent⟩

/-- The positive form costs `c` and silence costs nothing. -/
def cost (c : ℝ) : Message → ℝ
  | .positive => c
  | .silent => 0

variable {S Λ : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-! ### The update with a positive form -/

/-- The meaning of a message under a latent parameter is the parameter's extension for the
positive form and every state for silence. -/
def sem (E : Λ → Set S) (l : Λ) : Message → Set S
  | .positive => E l
  | .silent => Set.univ

/-- The literal listener at a latent parameter conditions the prior on the truth of the
message. -/
noncomputable def L0 (P : Measure S) (E : Λ → Set S) (l : Λ) : Kernel Message S :=
  listener P (truthful fun u ↦ sem E l u)

instance (P : Measure S) (E : Λ → Set S) (l : Λ) : IsFiniteKernel (L0 P E l) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

/-- The speaker at a state and a latent parameter soft-maximizes the literal listener's log
probability of the state minus the cost of the message. -/
noncomputable def S1 (P : Measure S) (E : Λ → Set S) (α c : ℝ) (p : S × Λ) : Measure Message :=
  speaker α (cost c) (L0 P E p.2) Measure.dirac p.1

instance (P : Measure S) (E : Λ → Set S) (α c : ℝ) (p : S × Λ) :
    IsFiniteMeasure (S1 P E α c p) :=
  inferInstanceAs (IsFiniteMeasure (speaker _ _ _ _ _))

section Speaker

variable (P : Measure S) [IsFiniteMeasure P] (E : Λ → Set S) (α c : ℝ)

theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) (s : S) (l : Λ) (u : Message) :
    S1 P E α c (s, l) {u} ≠ 0 ↔ s ∈ sem E l u ∧ P {s} ≠ 0 :=
  speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff hα (cost c) P (sem E l) u s

variable {P E α}

theorem S1_congr (hα : 0 < α) {s t : S} {l : Λ} (hs : P {s} ≠ 0) (ht : P {t} ≠ 0)
    (hsl : s ∈ E l) (htl : t ∈ E l) : S1 P E α c (t, l) = S1 P E α c (s, l) :=
  speaker_listener_truthful_dirac_congr hα _ P (sem E l) hs ht fun u ↦ by
    cases u <;> simp [sem, hsl, htl]

theorem S1_real_positive_le (hα : 0 < α) {s t : S} (hs : P {s} ≠ 0) (ht : P {t} ≠ 0) {l : Λ}
    (h : s ∈ E l → t ∈ E l) :
    (S1 P E α c (s, l)).real {.positive} ≤ (S1 P E α c (t, l)).real {.positive} := by
  by_cases hl : s ∈ E l
  · rw [S1_congr c hα hs ht hl (h hl)]
  · rw [measureReal_def, not_not.mp (mt (S1_apply_singleton_ne_zero_iff P E α c hα s l
      .positive).mp fun h' ↦ hl h'.1), ENNReal.toReal_zero]
    exact measureReal_nonneg

end Speaker

variable [MeasurableSpace Λ] (P : Measure S) [IsFiniteMeasure P] (ν : Measure Λ) (E : Λ → Set S)
  (α c : ℝ)

/-- The positive form is assertable when some state of positive prior lies in the extension of
some latent parameter of positive prior. -/
def Assertable : Prop := ∃ s l, P {s} ≠ 0 ∧ ν {l} ≠ 0 ∧ s ∈ E l

/-- The pragmatic listener inverts the speaker against the product of the state prior and the
prior over latent parameters. -/
noncomputable def L1 : Kernel Message (S × Λ) :=
  listener (P.prod ν) (S1 P E α c)

/-- The update of a prior with the positive form is the state marginal of the pragmatic
listener's posterior. -/
noncomputable def update : Measure S := (L1 P ν E α c .positive).fst

instance : IsFiniteMeasure (update P ν E α c) := by
  unfold update L1; infer_instance

variable {P ν E α}

private theorem update_congr {Q : Measure S} [IsFiniteMeasure Q] (h : Q = P) :
    update Q ν E α c = update P ν E α c := by
  subst h; rfl

variable [Fintype Λ] (P ν E α)

/-- The production weight of a state is the prior-averaged probability that the speaker
produces the positive form there. -/
noncomputable def production (s : S) : ℝ :=
  ∑ l, ν.real {l} * (S1 P E α c (s, l)).real {.positive}

variable {P ν E α}

theorem production_le_production (hα : 0 < α) {s t : S} (hs : P {s} ≠ 0) (ht : P {t} ≠ 0)
    (h : ∀ l, s ∈ E l → t ∈ E l) : production P ν E α c s ≤ production P ν E α c t :=
  Finset.sum_le_sum fun l _ ↦
    mul_le_mul_of_nonneg_left (S1_real_positive_le c hα hs ht (h l)) measureReal_nonneg

theorem production_lt_production [IsFiniteMeasure ν] (hα : 0 < α) {s t : S} (hs : P {s} ≠ 0)
    (ht : P {t} ≠ 0) (h : ∀ l, s ∈ E l → t ∈ E l) {l₀ : Λ} (hl₀ : ν {l₀} ≠ 0) (hs₀ : s ∉ E l₀)
    (ht₀ : t ∈ E l₀) : production P ν E α c s < production P ν E α c t := by
  refine Finset.sum_lt_sum (fun l _ ↦ mul_le_mul_of_nonneg_left
    (S1_real_positive_le c hα hs ht (h l)) measureReal_nonneg) ⟨l₀, Finset.mem_univ _, ?_⟩
  rw [measureReal_def (μ := S1 P E α c (s, l₀)), not_not.mp (mt
    (S1_apply_singleton_ne_zero_iff P E α c hα s l₀ .positive).mp fun h' ↦ hs₀ h'.1),
    ENNReal.toReal_zero, mul_zero]
  exact mul_pos (ENNReal.toReal_pos hl₀ (measure_ne_top _ _))
    (ENNReal.toReal_pos ((S1_apply_singleton_ne_zero_iff P E α c hα t l₀ .positive).mpr ⟨ht₀, ht⟩)
      (measure_ne_top _ _))

variable [IsFiniteMeasure ν]

theorem Assertable.sum_pos (h : Assertable P ν E) (hα : 0 < α) :
    0 < ∑ p, (P.prod ν).real {p} * (S1 P E α c p).real {.positive} := by
  obtain ⟨s, l, hs, hl, hsl⟩ := h
  refine Finset.sum_pos' (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg)
    ⟨(s, l), Finset.mem_univ _, mul_pos ?_ ?_⟩
  · rw [Measure.prod_real_singleton]
    exact mul_pos (ENNReal.toReal_pos hs (measure_ne_top _ _))
      (ENNReal.toReal_pos hl (measure_ne_top _ _))
  · exact ENNReal.toReal_pos
      ((S1_apply_singleton_ne_zero_iff P E α c hα s l .positive).mpr ⟨hsl, hs⟩)
      (measure_ne_top _ _)

variable [DiscreteMeasurableSpace Λ]

theorem Assertable.isProbabilityMeasure_update (h : Assertable P ν E) (hα : 0 < α) :
    IsProbabilityMeasure (update P ν E α c) := by
  obtain ⟨s, l, hs, hl, hsl⟩ := h
  have : IsProbabilityMeasure (L1 P ν E α c .positive) :=
    isProbabilityMeasure_listener_of_ne_zero _ _
      (by rw [← Set.singleton_prod_singleton, Measure.prod_prod]; exact mul_ne_zero hs hl)
      ((S1_apply_singleton_ne_zero_iff P E α c hα s l .positive).mpr ⟨hsl, hs⟩)
  unfold update
  infer_instance

theorem update_real_singleton (s : S) :
    (update P ν E α c).real {s} = P.real {s} * production P ν E α c s /
      ∑ p, (P.prod ν).real {p} * (S1 P E α c p).real {.positive} :=
  listener_prod_fst_real_singleton P ν _ _ s

theorem update_apply_singleton_ne_zero_iff (hα : 0 < α) (s : S) :
    update P ν E α c {s} ≠ 0 ↔ P {s} ≠ 0 ∧ ∃ l, ν {l} ≠ 0 ∧ s ∈ E l := by
  rw [update, L1, listener_fst_apply_singleton_ne_zero_iff]
  have hs := S1_apply_singleton_ne_zero_iff P E α c hα s
  simp_rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_ne_zero_iff, hs, sem]
  exact ⟨fun ⟨l, ⟨h, hl⟩, hsl, _⟩ ↦ ⟨h, l, hl, hsl⟩, fun ⟨h, l, hl, hsl⟩ ↦ ⟨l, ⟨h, hl⟩, hsl, h⟩⟩

theorem assertable_update {Λ' : Type*} [MeasurableSpace Λ'] {ν' : Measure Λ'}
    {E' : Λ' → Set S} (hα : 0 < α) {s : S} {l : Λ} {l' : Λ'} (hs : P {s} ≠ 0) (hl : ν {l} ≠ 0)
    (hsl : s ∈ E l) (hl' : ν' {l'} ≠ 0) (hsl' : s ∈ E' l') :
    Assertable (update P ν E α c) ν' E' :=
  ⟨s, l', (update_apply_singleton_ne_zero_iff c hα s).mpr ⟨hs, l, hl, hsl⟩,
    hl', hsl'⟩

theorem update_mul_le_mul (hα : 0 < α) {s t : S} (h : ∀ l, s ∈ E l → t ∈ E l) :
    (update P ν E α c).real {s} * P.real {t} ≤ (update P ν E α c).real {t} * P.real {s} := by
  rw [update_real_singleton, update_real_singleton]
  rcases eq_or_ne (P {s}) 0 with hs | hs
  · simp [measureReal_def, hs]
  rcases eq_or_ne (P {t}) 0 with ht | ht
  · simp [measureReal_def, ht]
  set Z := ∑ p, (P.prod ν).real {p} * (S1 P E α c p).real {Message.positive}
  calc P.real {s} * production P ν E α c s / Z * P.real {t}
      = P.real {s} * P.real {t} / Z * production P ν E α c s := by ring
    _ ≤ P.real {s} * P.real {t} / Z * production P ν E α c t :=
        mul_le_mul_of_nonneg_left (production_le_production c hα hs ht h)
          (div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
            (Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))
    _ = P.real {t} * production P ν E α c t / Z * P.real {s} := by ring

theorem update_mul_lt_mul (hα : 0 < α) {s t : S} (hs : P {s} ≠ 0) (ht : P {t} ≠ 0)
    (h : ∀ l, s ∈ E l → t ∈ E l) {l₀ : Λ} (hl₀ : ν {l₀} ≠ 0) (hs₀ : s ∉ E l₀) (ht₀ : t ∈ E l₀) :
    (update P ν E α c).real {s} * P.real {t} < (update P ν E α c).real {t} * P.real {s} := by
  have hE : Assertable P ν E := ⟨t, l₀, ht, hl₀, ht₀⟩
  rw [update_real_singleton, update_real_singleton]
  set Z := ∑ p, (P.prod ν).real {p} * (S1 P E α c p).real {Message.positive}
  have hpos : 0 < P.real {s} * P.real {t} / Z :=
    div_pos (mul_pos (ENNReal.toReal_pos hs (measure_ne_top _ _))
        (ENNReal.toReal_pos ht (measure_ne_top _ _)))
      (hE.sum_pos c hα)
  calc P.real {s} * production P ν E α c s / Z * P.real {t}
      = P.real {s} * P.real {t} / Z * production P ν E α c s := by ring
    _ < P.real {s} * P.real {t} / Z * production P ν E α c t :=
        mul_lt_mul_of_pos_left (production_lt_production c hα hs ht h hl₀ hs₀ ht₀) hpos
    _ = P.real {t} * production P ν E α c t / Z * P.real {s} := by ring

theorem update_eq_self [IsProbabilityMeasure P] (hα : 0 < α) (hE : Assertable P ν E)
    (h : ∀ l s t, s ∈ E l → t ∈ E l) : update P ν E α c = P := by
  have := hE.isProbabilityMeasure_update c hα
  refine Measure.ext_of_singleton fun s ↦ ?_
  have key : ∀ t, (update P ν E α c).real {s} * P.real {t}
      = (update P ν E α c).real {t} * P.real {s} := fun t ↦
    le_antisymm (update_mul_le_mul c hα fun l ↦ h l s t)
      (update_mul_le_mul c hα fun l ↦ h l t s)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun t _ ↦ key t
  rw [← Finset.mul_sum, ← Finset.sum_mul, sum_measureReal_singleton_eq_one,
    sum_measureReal_singleton_eq_one, mul_one, one_mul] at hsum
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hsum

/-! ### Positive forms of measure functions -/

section Models

variable {D D' X : Type*} [LinearOrder D] [Fintype D] [MeasurableSpace D]
  [DiscreteMeasurableSpace D] [LinearOrder D'] [Fintype D'] [MeasurableSpace D']
  [DiscreteMeasurableSpace D'] [Preorder X]

/-- The extension of a positive form at a threshold holds the states whose measure meets the
threshold. -/
def atLeast (m : S → D) (θ : D) : Set S := {s | θ ≤ m s}

/-- The interpretation of a bare positive form updates the prior with the extensions of the
adjective's measure function. -/
noncomputable abbrev positiveForm (P : Measure S) [IsFiniteMeasure P] (νA : Measure D)
    [IsFiniteMeasure νA] (mA : S → D) (α c : ℝ) : Measure S :=
  update P νA (atLeast mA) α c

/-- The conjunctive model of an intensified adjective resolves the thresholds of the adjective
and the adverb in tandem, as one update over pairs of thresholds. -/
noncomputable abbrev simultaneous (P : Measure S) [IsFiniteMeasure P] (νA : Measure D)
    [IsFiniteMeasure νA] (νD : Measure D') [IsFiniteMeasure νD] (mA : S → D) (mD : S → D')
    (α c : ℝ) : Measure S :=
  update P (νA.prod νD) (fun θ ↦ atLeast mA θ.1 ∩ atLeast mD θ.2) α c

/-- The backgrounded model of an intensified adjective first updates the prior with the
adverb's positive form at cost `c'` and then interprets the adjective's positive form
against that posterior. -/
noncomputable abbrev sequential (P : Measure S) [IsFiniteMeasure P] (νA : Measure D)
    [IsFiniteMeasure νA] (νD : Measure D') [IsFiniteMeasure νD] (mA : S → D) (mD : S → D')
    (α c c' : ℝ) : Measure S :=
  positiveForm (positiveForm P νD mD α c') νA mA α c

variable {νA : Measure D} [IsFiniteMeasure νA] {νD : Measure D'} [IsFiniteMeasure νD]
  {mA : S → D} {mD : S → D'} (c' : ℝ)

theorem positiveForm_mul_le_mul (hα : 0 < α) {s t : S} (h : mA s ≤ mA t) :
    (positiveForm P νA mA α c).real {s} * P.real {t}
      ≤ (positiveForm P νA mA α c).real {t} * P.real {s} :=
  update_mul_le_mul c hα fun _ hθ ↦ le_trans hθ h

theorem positiveForm_mul_lt_mul (hα : 0 < α) {s t : S} (hs : P {s} ≠ 0) (ht : P {t} ≠ 0)
    (h : mA s < mA t) (hν : νA {mA t} ≠ 0) :
    (positiveForm P νA mA α c).real {s} * P.real {t}
      < (positiveForm P νA mA α c).real {t} * P.real {s} :=
  update_mul_lt_mul c hα hs ht (fun _ hθ ↦ le_trans hθ h.le) hν (not_le.mpr h) le_rfl

theorem simultaneous_mul_le_mul (hα : 0 < α) {s t : S} (hA : mA s ≤ mA t) (hD : mD s ≤ mD t) :
    (simultaneous P νA νD mA mD α c).real {s} * P.real {t}
      ≤ (simultaneous P νA νD mA mD α c).real {t} * P.real {s} :=
  update_mul_le_mul c hα fun _ hθ ↦ ⟨le_trans hθ.1 hA, le_trans hθ.2 hD⟩

theorem sequential_mul_le_mul (hα : 0 < α) {s t : S} (hmA : mA s ≤ mA t) (hmD : mD s ≤ mD t) :
    (sequential P νA νD mA mD α c c').real {s} * P.real {t}
      ≤ (sequential P νA νD mA mD α c c').real {t} * P.real {s} := by
  have h₁ := positiveForm_mul_le_mul (P := positiveForm P νD mD α c') (νA := νA) c hα hmA
  have h₂ := positiveForm_mul_le_mul (P := P) (νA := νD) c' hα hmD
  set Q := positiveForm P νD mD α c'
  set ρ := sequential P νA νD mA mD α c c'
  rcases (measureReal_nonneg (μ := Q) (s := {t})).eq_or_lt with hQt | hQt
  · rw [← hQt, zero_mul] at h₂
    rcases mul_eq_zero.mp (le_antisymm h₂ (mul_nonneg measureReal_nonneg measureReal_nonneg))
      with hQs | hPt
    · rw [show ρ.real {s} = 0 by rw [update_real_singleton, hQs, zero_mul, zero_div],
        zero_mul]
      exact mul_nonneg measureReal_nonneg measureReal_nonneg
    · rw [hPt, mul_zero]
      exact mul_nonneg measureReal_nonneg measureReal_nonneg
  · refine le_of_mul_le_mul_right ?_ hQt
    calc ρ.real {s} * P.real {t} * Q.real {t}
        = ρ.real {s} * Q.real {t} * P.real {t} := by ring
      _ ≤ ρ.real {t} * Q.real {s} * P.real {t} :=
          mul_le_mul_of_nonneg_right h₁ measureReal_nonneg
      _ = ρ.real {t} * (Q.real {s} * P.real {t}) := by ring
      _ ≤ ρ.real {t} * (Q.real {t} * P.real {s}) :=
          mul_le_mul_of_nonneg_left h₂ measureReal_nonneg
      _ = ρ.real {t} * P.real {s} * Q.real {t} := by ring

/-! ### The Goldilocks effect and vacuous intensifiers -/

/-- The Goldilocks effect of evaluation constrains the measure function of an evaluative base
over a scale of excess, so that a negative evaluation grows with excess and a positive
evaluation shrinks with it. -/
def Goldilocks (a : Degree.GradableAdjective) (excess : S → X) (m : S → D') : Prop :=
  match a.evaluativeValence with
  | some .negative => ∀ s t, excess s ≤ excess t → m s ≤ m t
  | some .positive => ∀ s t, excess s ≤ excess t → m t ≤ m s
  | _ => True

variable {a : Degree.GradableAdjective} {excess : S → X}

theorem sequential_mul_le_mul_of_negative (ha : a.evaluativeValence = some .negative)
    (hm : Goldilocks a excess mD) (hα : 0 < α) {s t : S} (hmA : mA s ≤ mA t)
    (hx : excess s ≤ excess t) :
    (sequential P νA νD mA mD α c c').real {s} * P.real {t}
      ≤ (sequential P νA νD mA mD α c c').real {t} * P.real {s} := by
  rw [Goldilocks, ha] at hm
  exact sequential_mul_le_mul c c' hα hmA (hm s t hx)

theorem sequential_mul_le_mul_of_positive (ha : a.evaluativeValence = some .positive)
    (hm : Goldilocks a excess mD) (hα : 0 < α) {s t : S} (hmA : mA s ≤ mA t)
    (hx : excess t ≤ excess s) :
    (sequential P νA νD mA mD α c c').real {s} * P.real {t}
      ≤ (sequential P νA νD mA mD α c c').real {t} * P.real {s} := by
  rw [Goldilocks, ha] at hm
  exact sequential_mul_le_mul c c' hα hmA (hm t s hx)

theorem horribly_mul_le_mul (hm : Goldilocks English.Adjectives.horrible excess mD)
    (hα : 0 < α) {s t : S} (hmA : mA s ≤ mA t) (hx : excess s ≤ excess t) :
    (sequential P νA νD mA mD α c c').real {s} * P.real {t}
      ≤ (sequential P νA νD mA mD α c c').real {t} * P.real {s} :=
  sequential_mul_le_mul_of_negative c c' rfl hm hα hmA hx

theorem pleasantly_mul_le_mul (hm : Goldilocks English.Adjectives.pleasant excess mD)
    (hα : 0 < α) {s t : S} (hmA : mA s ≤ mA t) (hx : excess t ≤ excess s) :
    (sequential P νA νD mA mD α c c').real {s} * P.real {t}
      ≤ (sequential P νA νD mA mD α c c').real {t} * P.real {s} :=
  sequential_mul_le_mul_of_positive c c' rfl hm hα hmA hx

end Models

section Vacuous

variable {D D' : Type*} [LinearOrder D] [MeasurableSpace D] [LinearOrder D'] [Fintype D']
  [MeasurableSpace D'] [DiscreteMeasurableSpace D'] {νA : Measure D} [IsFiniteMeasure νA]
  {νD : Measure D'} [IsFiniteMeasure νD] {mA : S → D} {mD : S → D'} (c' : ℝ)

theorem sequential_eq_positiveForm [IsProbabilityMeasure P] (hα : 0 < α)
    (hD : Assertable P νD (atLeast mD)) (h : ∀ s t, mD s = mD t) :
    sequential P νA νD mA mD α c c' = positiveForm P νA mA α c :=
  update_congr c (update_eq_self c' hα hD fun θ s t (hs : θ ≤ mD s) ↦ (h s t ▸ hs : θ ≤ mD t))

end Vacuous

end Nouwen2024
