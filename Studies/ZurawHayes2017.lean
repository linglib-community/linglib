module

public import Linglib.Phonology.HarmonicGrammar.IntersectingFamilies
public import Linglib.Phonology.HarmonicGrammar.Noise
public import Studies.Zuraw2010

/-!
# Zuraw and Hayes (2017): Intersecting Constraint Families

Tagalog nasal substitution is conditioned by consonant-sensitive markedness constraints and by
one Uniformity constraint per prefix, so every square of two prefixes and two stems is
independent (`independent`): the effects of prefixes and stems are [across the board in
MaxEnt](##ZurawHayes2017.maxEnt_acrossTheBoard), those of prefixes [in Noisy Harmonic
Grammar](##ZurawHayes2017.weightNoise_acrossTheBoard). With a lone constraint opposing two
synergistic families, the difference a stronger constraint makes [grows in stochastic OT as the
other weakens](##ZurawHayes2017.antitone_raceRate_sub), the opposing rate [vanishing as the
first strengthens](##ZurawHayes2017.tendsto_raceRate_atTop), and is [neither antitone nor
monotone under the MaxEnt rate](##ZurawHayes2017.not_antitone_not_monotone_sigmoid_sub).

## Implementation notes

* The inputs are the thirty-six crossings of the six prefix constructions of Figure 3 with the
  six stem-initial consonants of `Studies/Zuraw2010`; its /t/ stands for the paper's t/s class.
* The constraints are those of Table 1, in its order, the consonant-sensitive ones pulled back
  from `Studies/Zuraw2010` along the projection of a candidate onto its stem and decision.
* Magri's theorem is proved for noise of any law, stochastic OT's Gaussian noise among them: the
  opposing candidate's rate integrates, against the law of its constraint, the product of the
  other two constraints' distribution functions (`choiceProb_pi_eq_lintegral`), and that product
  has increasing differences in the two ranking values.
* The paper's fitted weights and ranking values, their log likelihoods, the empirical rates, the
  French and Hungarian data, and the partial-ordering model are not represented.

## References

* [zuraw-hayes-2017]
* [zuraw-2010]
* [pater-1999]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace ZurawHayes2017

open Real OptimalityTheory HarmonicGrammar ProbabilityTheory Finset
open scoped NNReal
open Zuraw2010 (StemC SubSt NSCand)

/-! ### Inputs and candidates -/

/-- The six most type-frequent prefix constructions of Figure 3, in the order of Table 1. -/
inductive Prefix
  /-- *maŋ-* OTHER, nonadversative verbs. -/
  | mangOther
  /-- *paŋ-* RED-, mainly gerunds. -/
  | pangRed
  /-- *maŋ-* ADV, adversative verbs. -/
  | mangAdv
  /-- *maŋ-* RED-, professional or habitual nouns. -/
  | mangRed
  /-- *paŋ-* NOUN, various nominalizations. -/
  | pangNoun
  /-- *paŋ-* RES, reservational adjectives. -/
  | pangRes
  deriving DecidableEq, Repr, Fintype

/-- A candidate is a prefix construction and a stem-initial consonant, with or without
substitution. -/
abbrev Candidate := (Prefix × StemC) × SubSt

/-- The projection of a candidate onto the stem and decision of a `Zuraw2010` candidate. -/
def project (c : Candidate) : NSCand := (c.1.2, c.2)

/-- The square crossing the prefixes `p` and `p'` (rows) with the stems `c` and `c'` (columns). -/
def square (p p' : Prefix) (c c' : StemC) : Square (Prefix × StemC) :=
  ⟨(p, c), (p, c'), (p', c), (p', c')⟩

/-! ### The constraints -/

/-- `NasSub` (3) assigns one violation to a nasal followed by an obstruent across a morpheme
boundary. -/
def nasSub : Constraint Candidate := Zuraw2010.nasSub.comap project

/-- *NC̥ (4) assigns one violation to a nasal followed by a voiceless obstruent. -/
def starNC : Constraint Candidate := Zuraw2010.starNC.comap project

/-- *[root m/n/ŋ (6a) forbids a root to begin with a nasal. -/
def starRootNasal : Constraint Candidate := Zuraw2010.starInitAll.comap project

/-- *[root n/ŋ (6b) forbids a root to begin with a coronal or velar nasal. -/
def starRootCorVel : Constraint Candidate := Zuraw2010.starInitCorVel.comap project

/-- *[root ŋ (6c) forbids a root to begin with a velar nasal. -/
def starRootVelar : Constraint Candidate := Zuraw2010.starInitVelar.comap project

/-- The Uniformity constraint of (5) indexed to prefix construction `q`, which forbids a segment
of the prefix and a distinct input segment to correspond to one output segment. -/
def unif (q : Prefix) : Constraint Candidate :=
  Constraint.binary fun c ↦ c.1.1 = q ∧ c.2 = .yes

/-- The eleven constraints, in the order of Table 1. -/
def constraints : ConstraintSet Candidate (Fin 11) :=
  ![nasSub, starNC, starRootNasal, starRootCorVel, starRootVelar, unif .mangOther, unif .pangRed,
    unif .mangAdv, unif .mangRed, unif .pangNoun, unif .pangRes]

attribute [local simp] constraints nasSub starNC starRootNasal starRootCorVel starRootVelar unif
  Zuraw2010.nasSub Zuraw2010.starNC Zuraw2010.starInitAll Zuraw2010.starInitCorVel
  Zuraw2010.starInitVelar project

theorem independent (p p' : Prefix) (c c' : StemC) :
    (square p p' c c').Independent constraints .yes .no := by
  intro k
  fin_cases k <;> first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

theorem sum_unif_eq_starRootNasal (c : Candidate) : ∑ q, unif q c = starRootNasal c := by
  revert c
  decide +kernel

/-! ### Across-the-board effects -/

/-- The effect of the rows of a square is across the board (§2.3) when it has the same direction
in both columns, so that the lines of Figure 4 do not cross. -/
def AcrossTheBoard {X : Type*} (sq : Square X) (r : X → ℝ) : Prop :=
  0 ≤ (r sq.tl - r sq.bl) * (r sq.tr - r sq.br)

theorem acrossTheBoard_of_interaction_eq_zero {X S : Type*} {sq : Square X} {d : X → ℝ}
    {s : X → S} {F : S → ℝ → ℝ} (hF : ∀ x, Monotone (F (s x))) (hd : sq.interaction d = 0)
    (hs : sq.InsensitiveToRow s) : AcrossTheBoard sq fun x ↦ F (s x) (d x) := by
  rw [Square.interaction_eq_zero_iff'] at hd
  rw [AcrossTheBoard, ← hs.1, ← hs.2]
  rcases le_total (d sq.tl) (d sq.bl) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hF _ h)) (sub_nonpos.2 (hF _ (by linarith)))
  · exact mul_nonneg (sub_nonneg.2 (hF _ h)) (sub_nonneg.2 (hF _ (by linarith)))

/-! ### Maximum entropy -/

instance : MeasurableSpace SubSt := ⊤
instance : MeasurableSingletonClass SubSt := ⟨fun _ ↦ trivial⟩

/-- The MaxEnt probability of substitution for an input. -/
noncomputable def maxEntSubst (w : Fin 11 → ℝ) (x : Prefix × StemC) : ℝ :=
  (maxEnt (constraints.comap (x, ·)).violations w).real {.yes}

-- (13)
theorem maxEntSubst_eq (w : Fin 11 → ℝ) (x : Prefix × StemC) :
    maxEntSubst w x =
      sigmoid (harmonyScore constraints w (x, .yes) - harmonyScore constraints w (x, .no)) :=
  maxEnt_real_singleton_of_pair _ _ (a := SubSt.yes) (b := .no) (by decide) (by decide)

theorem maxEnt_interaction_logOdds_eq_zero (w : Fin 11 → ℝ) (p p' : Prefix) (c c' : StemC) :
    (square p p' c c').interaction (fun x ↦
      log ((maxEnt (constraints.comap (x, ·)).violations w).real {.yes} /
        (maxEnt (constraints.comap (x, ·)).violations w).real {.no})) = 0 :=
  (independent p p' c c').interaction_logOdds_maxEnt w

theorem harmony_b_sub_harmony_k (w : Fin 11 → ℝ) (p : Prefix) :
    harmonyScore constraints w ((p, .b), .yes) - harmonyScore constraints w ((p, .b), .no) -
      (harmonyScore constraints w ((p, .k), .yes) - harmonyScore constraints w ((p, .k), .no)) =
    w 3 + w 4 - w 1 := by
  cases p <;> simp [harmonyScore_eq_neg_sum, Fin.sum_univ_succ] <;> ring

/-- In MaxEnt the effects of the prefixes and of the stems are across the board on every square,
for every weighting (§2.3). -/
theorem maxEnt_acrossTheBoard (w : Fin 11 → ℝ) (p p' : Prefix) (c c' : StemC) :
    AcrossTheBoard (square p p' c c') (maxEntSubst w) ∧
      AcrossTheBoard (square p p' c c').transpose (maxEntSubst w) := by
  have hd := (independent p p' c c').interaction_harmonyScore_sub w
  rw [funext (maxEntSubst_eq w)]
  exact ⟨acrossTheBoard_of_interaction_eq_zero (s := fun _ ↦ ()) (F := fun _ ↦ sigmoid)
      (fun _ ↦ sigmoid_strictMono.monotone) hd ⟨rfl, rfl⟩,
    acrossTheBoard_of_interaction_eq_zero (s := fun _ ↦ ()) (F := fun _ ↦ sigmoid)
      (fun _ ↦ sigmoid_strictMono.monotone) (by rwa [Square.interaction_transpose]) ⟨rfl, rfl⟩⟩

/-! ### Noisy Harmonic Grammar -/

/-- The NHG probability of substitution for an input under noise of variance `v` on the
weights. -/
noncomputable def weightNoiseSubst (w : Fin 11 → ℝ) (v : ℝ≥0) (x : Prefix × StemC) : ℝ :=
  (weightNoiseChoiceProb (constraints.comap (x, ·)) w v .yes).toReal

/-- The number of constraints that distinguish substitution from its absence, each counted with
its squared violation difference. -/
private def diffSq (x : Prefix × StemC) : ℤ :=
  ∑ i, ((constraints i (x, .yes) : ℤ) - constraints i (x, .no)) ^ 2

private theorem dotProduct_violationDiff_self_eq_diffSq (x : Prefix × StemC) :
    (constraints.violationDiff (x, .yes) (x, .no) ⬝ᵥ
      constraints.violationDiff (x, .yes) (x, .no) : ℝ) = diffSq x := by
  simp [dotProduct, ConstraintSet.violationDiff, diffSq, sq]

private theorem diffSq_eq (q : Prefix) (c : StemC) : diffSq (q, c) = diffSq (.mangOther, c) := by
  revert q c
  decide +kernel

private theorem diffSq_pos (x : Prefix × StemC) : 0 < diffSq x := by
  revert x
  decide +kernel

-- (15)
theorem dotProduct_violationDiff_self_p (q : Prefix) :
    (constraints.violationDiff ((q, .p), .yes) ((q, .p), .no) ⬝ᵥ
      constraints.violationDiff ((q, .p), .yes) ((q, .p), .no) : ℝ) = 4 := by
  rw [dotProduct_violationDiff_self_eq_diffSq]
  exact_mod_cast (show diffSq (q, .p) = 4 by cases q <;> decide +kernel)

private theorem weightNoiseSubst_eq (w : Fin 11 → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : Prefix × StemC) :
    weightNoiseSubst w v x =
      normalCDF ((harmonyScore constraints w (x, .yes) - harmonyScore constraints w (x, .no)) /
        √(v * diffSq (.mangOther, x.2))) := by
  have hd : (constraints.violationDiff (x, .yes) (x, .no) : Fin 11 → ℝ) ≠ 0 := fun h ↦ by
    have := dotProduct_violationDiff_self_eq_diffSq x
    rw [h, zero_dotProduct] at this
    exact (diffSq_pos x).ne' (by exact_mod_cast this.symm)
  rw [weightNoiseSubst, weightNoiseChoiceProb_of_forall_ne_eq (constraints.comap (x, ·)) w v hv
      (fun y hy ↦ by cases y <;> simp_all) (by decide) hd,
    ENNReal.toReal_ofReal (normalCDF_pos _).le, ← diffSq_eq x.1,
    ← dotProduct_violationDiff_self_eq_diffSq x]
  rfl

/-- In Noisy Harmonic Grammar the effects of the prefixes are across the board on every square,
for every weighting and noise: the noise on a comparison depends on the stem alone. -/
theorem weightNoise_acrossTheBoard (w : Fin 11 → ℝ) {v : ℝ≥0} (hv : v ≠ 0) (p p' : Prefix)
    (c c' : StemC) :
    AcrossTheBoard (square p p' c c') (weightNoiseSubst w v) := by
  rw [funext (weightNoiseSubst_eq w hv)]
  refine acrossTheBoard_of_interaction_eq_zero (F := fun s Δ ↦ normalCDF (Δ / s))
    (fun x ↦ (normalCDF_strictMono.comp (strictMono_id.div_const ?_)).monotone)
    ((independent p p' c c').interaction_harmonyScore_sub w) ⟨rfl, rfl⟩
  have : (0 : ℝ) < diffSq (.mangOther, x.2) := by exact_mod_cast diffSq_pos _
  have : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  positivity

/-! ### Stochastic OT with synergistic families (§3.8) -/

section StochasticOT

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable (η : Measure ℝ)

/-- In stochastic OT every ranking value is perturbed by independent noise of law `η`, and an
evaluation is decided by the highest-ranked constraint that distinguishes the candidates. When a
lone opposing constraint, with ranking value `n`, faces two synergistic families, each applying
through one constraint, with ranking values `a` and `u`, the candidate it favors wins exactly
when it outruns the other two (§3.8). `raceRate η n a u` is the rate of that candidate. -/
noncomputable def raceRate (n a u : ℝ) : ℝ≥0∞ :=
  choiceProb (Measure.pi ![η.map (n + ·), η.map (a + ·), η.map (u + ·)]) 0

private theorem map_add_Iio (r x : ℝ) : η.map (r + ·) (Iio x) = η (Iio (x - r)) := by
  rw [Measure.map_apply (measurable_const_add r) measurableSet_Iio, preimage_const_add_Iio]

private theorem measurable_Iio_sub (r : ℝ) : Measurable fun x ↦ η (Iio (x - r)) :=
  Monotone.measurable fun _ _ h ↦ measure_mono (Iio_subset_Iio (by linarith))

private theorem measurable_race (a u : ℝ) :
    Measurable fun x ↦ η (Iio (x - a)) * η (Iio (x - u)) :=
  (measurable_Iio_sub η a).mul (measurable_Iio_sub η u)

variable [IsProbabilityMeasure η]

theorem raceRate_eq (n a u : ℝ) :
    raceRate η n a u = ∫⁻ x, η (Iio (x - a)) * η (Iio (x - u)) ∂η.map (n + ·) := by
  have : ∀ j, SigmaFinite (![η.map (n + ·), η.map (a + ·), η.map (u + ·)] j) := fun j ↦ by
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
      infer_instance
  rw [raceRate, choiceProb_pi_eq_lintegral, show univ.erase (0 : Fin 3) = {1, 2} by decide]
  simp [map_add_Iio]

theorem raceRate_le_one (n a u : ℝ) : raceRate η n a u ≤ 1 := by
  rw [raceRate_eq]
  calc _ ≤ ∫⁻ _, 1 ∂η.map (n + ·) := lintegral_mono fun _ ↦ mul_le_one' prob_le_one prob_le_one
    _ = 1 := by simp [Measure.map_apply (measurable_const_add n) .univ]

-- §3.8
theorem raceRate_add_le {n a a' u u' : ℝ} (ha : a' ≤ a) (hu : u ≤ u') :
    raceRate η n a u + raceRate η n a' u' ≤ raceRate η n a' u + raceRate η n a u' := by
  simp only [raceRate_eq]
  rw [← lintegral_add_left (measurable_race η a u), ← lintegral_add_left (measurable_race η a' u)]
  refine lintegral_mono fun x ↦ ?_
  obtain ⟨p, hp⟩ := exists_add_of_le (measure_mono (μ := η) (Iio_subset_Iio (sub_le_sub_left ha x)))
  obtain ⟨q, hq⟩ := exists_add_of_le (measure_mono (μ := η) (Iio_subset_Iio (sub_le_sub_left hu x)))
  rw [hp, hq]
  set A := η (Set.Iio (x - a))
  set B := η (Set.Iio (x - u'))
  calc A * (B + q) + (A + p) * B = A * B + p * B + (A * B + A * q) := by ring
    _ ≤ A * B + p * B + (A * B + A * q) + p * q := le_self_add
    _ = (A + p) * (B + q) + A * B := by ring

/-- The difference a stronger constraint of one family makes grows monotonically as the constraint
of the other family weakens (§3.8, Figure 20). -/
theorem antitone_raceRate_sub (n : ℝ) {u u' : ℝ} (hu : u ≤ u') :
    Antitone fun a ↦ (raceRate η n a u).toReal - (raceRate η n a u').toReal := by
  intro a' a ha
  have h := raceRate_add_le η (n := n) ha hu
  have fin (a u : ℝ) : raceRate η n a u ≠ ∞ :=
    ((raceRate_le_one η n a u).trans_lt ENNReal.one_lt_top).ne
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩)
    (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩), ENNReal.toReal_add (fin _ _) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _)] at h
  simp only
  linarith

/-- As a constraint of one family strengthens, the opposing candidate's rate vanishes whatever
the other: the rates converge (§3.8). -/
theorem tendsto_raceRate_atTop (n u : ℝ) :
    Tendsto (fun a ↦ raceRate η n a u) atTop (𝓝 0) := by
  have hlim (x : ℝ) : Tendsto (fun a ↦ η (Iio (x - a))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_cdf_atBot η).comp
      (tendsto_atBot_add_const_left atTop x tendsto_neg_atTop_atBot))
    rw [ENNReal.ofReal_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
      fun a ↦ (measure_mono Set.Iio_subset_Iic_self).trans_eq
        (by rw [Function.comp_apply, ← sub_eq_add_neg, ofReal_cdf])
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := η.map (n + ·)) (l := atTop)
    (F := fun a x ↦ η (Iio (x - a)) * η (Iio (x - u))) (f := fun _ ↦ 0) (fun _ ↦ 1)
    (.of_forall (measurable_race η · u))
    (.of_forall fun _ ↦ .of_forall fun _ ↦ mul_le_one' prob_le_one prob_le_one)
    (by rw [lintegral_one]; exact measure_ne_top _ _)
    (.of_forall fun x ↦ by
      simpa using ENNReal.Tendsto.mul_const (hlim x) (.inr (measure_ne_top η _)))
  simpa [raceRate_eq] using key

/-- With the two-candidate MaxEnt rate `sigmoid (n - a - u)` (13), the difference a stronger
constraint makes is neither antitone nor monotone in the other. -/
theorem not_antitone_not_monotone_sigmoid_sub (n : ℝ) {u u' : ℝ} (hu : u < u') :
    ¬ Antitone (fun a ↦ sigmoid (n - a - u) - sigmoid (n - a - u')) ∧
      ¬ Monotone (fun a ↦ sigmoid (n - a - u) - sigmoid (n - a - u')) := by
  set D := fun a ↦ sigmoid (n - a - u) - sigmoid (n - a - u')
  have hpos : 0 < D 0 := sub_pos.2 (sigmoid_strictMono (by linarith))
  have hbot : Tendsto D atBot (𝓝 0) := by
    have h (v : ℝ) : Tendsto (fun a ↦ sigmoid (n - a - v)) atBot (𝓝 1) :=
      tendsto_sigmoid_atTop.comp (tendsto_atTop_add_const_right _ _
        (tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop))
    simpa using (h u).sub (h u')
  have htop : Tendsto D atTop (𝓝 0) := by
    have h (v : ℝ) : Tendsto (fun a ↦ sigmoid (n - a - v)) atTop (𝓝 0) :=
      tendsto_sigmoid_atBot.comp (tendsto_atBot_add_const_right _ _
        (tendsto_atBot_add_const_left _ _ tendsto_neg_atTop_atBot))
    simpa using (h u).sub (h u')
  refine ⟨fun hD ↦ ?_, fun hD ↦ ?_⟩
  · exact hpos.not_ge (ge_of_tendsto hbot (eventually_le_atBot 0 |>.mono fun a ha ↦ hD ha))
  · exact hpos.not_ge (ge_of_tendsto htop (eventually_ge_atTop 0 |>.mono fun a ha ↦ hD ha))

end StochasticOT

/-! ### The decision-tree model -/

theorem decision_tree_monotonic_diff (g₁ g₂ h₁ h₂ : ℚ) (hg : g₁ < g₂) (hh : h₁ < h₂) :
    g₁ * h₂ - g₁ * h₁ < g₂ * h₂ - g₂ * h₁ := by
  have key : g₁ * (h₂ - h₁) < g₂ * (h₂ - h₁) := mul_lt_mul_of_pos_right hg (by linarith)
  linarith [mul_sub g₁ h₂ h₁, mul_sub g₂ h₂ h₁]

theorem decision_tree_diff_proportional (g₁ g₂ h₁ h₂ : ℚ) :
    (g₂ * h₂ - g₂ * h₁) * g₁ = (g₁ * h₂ - g₁ * h₁) * g₂ := by
  ring

end ZurawHayes2017
