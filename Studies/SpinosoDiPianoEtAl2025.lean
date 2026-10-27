module

public import Studies.KaoGoodman2015
public import Studies.KaoWuEtAl2014

/-!
# Spinoso-Di Piano, Austin, Piantanida and Cheung (2025): (RSA)²: A Rhetorical-Strategy-Aware Rational Speech Act Framework for Figurative Language Understanding

The framework replaces the Boolean meaning of the literal listener by a rhetorical function, one
graded meaning per rhetorical strategy such as literalness, irony or hyperbole. A strategy-indexed
literal listener, speaker and pragmatic listener run the standard pipeline (`L0`, `S1`, `L1`),
and the listener averages the strategies under a strategy posterior given the utterance
(`listener`).

## Main results

* `L1_indicator_apply_singleton_of_notMem`, `listener_apply_singleton_ne_zero_iff`: standard RSA
  gives no mass to a meaning outside the literal extension of the utterance, while the listener
  gives a meaning of positive prior mass exactly when some strategy of positive posterior weight
  admits it at the utterance.
* `L0_rhetoricalOfQUD`, `kaoGoodman2015_S1`, `kaoWuEtAl2014_S1`: every literal listener of
  question-under-discussion RSA is the literal listener of a rhetorical function, at a prior that
  is positive everywhere, and the speakers of Kao and Goodman's irony model and of Kao and
  colleagues' hyperbole model are the framework's speakers at that function.
* `exists_L0_ne_qudListener`: over two or more meanings some literal listener of the framework is
  no literal listener of question-under-discussion RSA.
* `literal_reading_iff`: in the running example, *the weather is amazing* keeps its
  literal reading exactly when the strategy posterior gives the literal strategy weight.

## Implementation notes

* The context of the paper's conditional probabilities indexes the prior, the utterance prior,
  the rhetorical functions and the strategy posterior. Every statement holds at a fixed context,
  so the context is not represented.
* Rhetorical functions take values in `ℝ≥0∞` where the paper has the unit interval. The bound is
  a normalization (`exists_le_one_and_L0_eq`), and the two lemmas about question-under-discussion
  RSA are stated with it.
* The speaker pays a cost where the paper weighs utterances by a prior; `S1_eq_ofWeights_prior`
  gives the cost of a prior.
* The paper's first definition states the literal listener of question-under-discussion RSA as a
  distribution over meanings (`qudListener`). Kao and colleagues state it as a distribution over
  answers, the pushforward of the literal listener along the question. The two give a meaning's
  cell proportional mass. The constant depends on the utterance in general, and not when the
  cells of the question have one size, as those of a coordinate projection do
  (`speaker_qudListener_dirac`).

## TODO

* The price experiment's rhetorical function, set by hand to one where the strategy fits the
  utterance to the price and to a thousandth elsewhere, the network-fitted function of the
  weather experiment, the comparison with affect-aware RSA on both, and the language-model
  listeners of the fifth section are not formalized.

## References

* [spinoso-di-piano-etal-2025]
* [kao-goodman-2015]
* [kao-etal-2014-hyperbole]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace SpinosoDiPianoEtAl2025

variable {M U R : Type*} [MeasurableSpace M] [MeasurableSpace U]

/-! ### The framework -/

section Framework

variable [Fintype M] [Fintype U] [DiscreteMeasurableSpace U]

/-- The strategy-indexed literal listener (eq. 4) reweights the prior by the rhetorical
function of the strategy. -/
noncomputable def L0 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (r : R) : Kernel U M :=
  Kernel.ofDensity μ (f r)

instance (μ : Measure M) (f : R → U → M → ℝ≥0∞) (r : R) : IsFiniteKernel (L0 μ f r) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

theorem exists_le_one_and_L0_eq (μ : Measure M) {f : R → U → M → ℝ≥0∞}
    (hf : ∀ r u m, f r u m ≠ ∞) :
    ∃ f' : R → U → M → ℝ≥0∞, (∀ r u m, f' r u m ≤ 1) ∧ L0 μ f' = L0 μ f :=
  ⟨fun r u m ↦ f r u m / ⨆ m', f r u m',
    fun r u m ↦ ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_iSup (f r u) m),
    funext fun r ↦ Kernel.ofDensity_div_iSup μ (f r) fun u ↦ iSup_ne_top (hf r u)⟩

variable [DiscreteMeasurableSpace M]

/-- The strategy-indexed speaker (eq. 5) is the best response to the strategy's literal
listener, less the utterance cost. -/
noncomputable def S1 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ) (r : R) :
    Kernel M U :=
  speaker α κ (L0 μ f r) Measure.dirac

instance (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ) (r : R) :
    IsFiniteKernel (S1 μ f α κ r) :=
  inferInstanceAs (IsFiniteKernel (speaker α κ (L0 μ f r) Measure.dirac))

/-- The strategy-indexed pragmatic listener (eq. 6). -/
noncomputable def L1 (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ) (r : R) :
    Kernel U M :=
  RSA.listener μ (S1 μ f α κ r)

/-- The pragmatic listener (eq. 7) averages the strategy-indexed listeners under the strategy
posterior given the utterance. -/
noncomputable def listener [MeasurableSpace R] (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ)
    (κ : U → ℝ) (ρ : Kernel U R) : Kernel U M :=
  Kernel.ofFunOfCountable fun u ↦ (ρ u).bind fun r ↦ L1 μ f α κ r u

variable (μ : Measure M) (f : R → U → M → ℝ≥0∞) (α : ℝ) (κ : U → ℝ)

theorem S1_eq_ofWeights_prior (hα : α ≠ 0) {π : U → ℝ≥0∞} (hπ0 : ∀ u, π u ≠ 0)
    (hπ : ∀ u, π u ≠ ∞) (r : R) :
    S1 μ f α (fun u ↦ -Real.log (π u).toReal / α) r =
      Kernel.ofWeights fun m u ↦ L0 μ f r u {m} ^ α * π u := by
  rw [S1, speaker_dirac_eq_ofWeights]
  congr 1
  funext m u
  rw [mul_div_cancel₀ _ hα, neg_neg, Real.exp_log (ENNReal.toReal_pos (hπ0 u) (hπ u)),
    ENNReal.ofReal_toReal (hπ u)]

theorem L1_indicator (sem : U → Set M) {r : R} (hr : f r = fun u ↦ (sem u).indicator 1) :
    L1 μ f α κ r =
      RSA.listener μ (speaker α κ (RSA.listener μ (truthful sem)) Measure.dirac) := by
  rw [L1, S1, L0, hr, listener_truthful_eq_ofDensity]

/-- Under a Boolean rhetorical function, standard RSA gives no listener mass to meanings outside the
utterance's extension (Appendix A.2). -/
theorem L1_indicator_apply_singleton_of_notMem (hα : 0 < α) (sem : U → Set M) {r : R}
    (hr : f r = fun u ↦ (sem u).indicator 1) {u : U} {m : M} (hm : m ∉ sem u) :
    L1 μ f α κ r u {m} = 0 := by
  rw [L1_indicator μ f α κ sem hr]
  exact listener_speaker_listener_truthful_apply_singleton_of_notMem hα κ μ sem hm

theorem listener_apply_singleton [Fintype R] [MeasurableSpace R] [DiscreteMeasurableSpace R]
    (ρ : Kernel U R) (u : U) (m : M) :
    listener μ f α κ ρ u {m} = ∑ r, L1 μ f α κ r u {m} * ρ u {r} := by
  rw [listener, Kernel.ofFunOfCountable_apply,
    Measure.bind_apply (.singleton m) Measurable.of_discrete.aemeasurable, lintegral_fintype]

variable [IsFiniteMeasure μ]

theorem L1_apply_singleton_ne_zero_iff (hα : 0 < α) {r : R} {u : U} (hf : ∀ m, f r u m ≠ ∞)
    (m : M) : L1 μ f α κ r u {m} ≠ 0 ↔ f r u m ≠ 0 ∧ μ {m} ≠ 0 := by
  rw [L1, RSA.listener_apply_singleton_ne_zero_iff, S1,
    speaker_dirac_apply_singleton_ne_zero_iff hα, L0,
    Kernel.ofDensity_apply_singleton_ne_zero_iff μ hf]
  exact and_iff_right_of_imp And.right

variable [Fintype R] [MeasurableSpace R] [DiscreteMeasurableSpace R]

/-- The pragmatic listener interprets an utterance as a meaning exactly when the meaning has
positive prior and some strategy of positive posterior weight admits it at the utterance. -/
theorem listener_apply_singleton_ne_zero_iff (hα : 0 < α) {u : U} (hf : ∀ r m, f r u m ≠ ∞)
    (ρ : Kernel U R) (m : M) :
    listener μ f α κ ρ u {m} ≠ 0 ↔ μ {m} ≠ 0 ∧ ∃ r, ρ u {r} ≠ 0 ∧ f r u m ≠ 0 := by
  have h : listener μ f α κ ρ u {m} ≠ 0 ↔ ∃ r, L1 μ f α κ r u {m} ≠ 0 ∧ ρ u {r} ≠ 0 := by
    simp only [listener_apply_singleton, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ,
      true_implies, mul_eq_zero, not_forall, not_or]
  simp only [h, L1_apply_singleton_ne_zero_iff μ f α κ hα (hf _)]
  grind

end Framework

/-! ### Question-under-discussion RSA as a special case -/

section QUD

variable {G X : Type*}

/-- The rhetorical function of a question (eq. 19) is the literal mass of the meaning's cell over
the prior mass of the meaning, divided by its largest value at the utterance. -/
noncomputable def rhetoricalOfQUD (μ : Measure M) (L : Kernel U M) (q : G → M → X) (g : G)
    (u : U) (m : M) : ℝ≥0∞ :=
  L u (q g ⁻¹' {q g m}) / μ {m} / ⨆ m', L u (q g ⁻¹' {q g m'}) / μ {m'}

theorem rhetoricalOfQUD_le_one (μ : Measure M) (L : Kernel U M) (q : G → M → X) (g : G) (u : U)
    (m : M) : rhetoricalOfQUD μ L q g u m ≤ 1 :=
  ENNReal.div_le_of_le_mul <| by
    rw [one_mul]
    exact le_iSup (fun m' ↦ L u (q g ⁻¹' {q g m'}) / μ {m'}) m

variable [Fintype M] [DiscreteMeasurableSpace M] [Fintype U] [DiscreteMeasurableSpace U]

/-- The literal listener of question-under-discussion RSA (eq. 13) gives a meaning mass
proportional to the literal listener's mass on the meanings with the same answer. -/
noncomputable def qudListener (L : Kernel U M) (q : M → X) : Kernel U M :=
  Kernel.ofWeights fun u m ↦ L u (q ⁻¹' {q m})

/-- At a prior of positive mass everywhere, the literal listener of question-under-discussion RSA
under a question is that of the question's rhetorical function (Lemma 1). -/
theorem L0_rhetoricalOfQUD (μ : Measure M) [IsFiniteMeasure μ] (hμ : ∀ m, μ {m} ≠ 0)
    (L : Kernel U M) [IsFiniteKernel L] (q : G → M → X) (g : G) :
    L0 μ (rhetoricalOfQUD μ L q) g = qudListener L (q g) := by
  refine (Kernel.ofDensity_div_iSup μ (fun u m ↦ L u (q g ⁻¹' {q g m}) / μ {m}) fun u ↦
    iSup_ne_top fun m ↦ ENNReal.div_ne_top (measure_ne_top _ _) (hμ m)).trans ?_
  ext u : 1
  refine Measure.ext_of_singleton fun m ↦ ?_
  rw [qudListener, Kernel.ofDensity_apply_singleton, Kernel.ofWeights_apply_singleton]
  simp only [ENNReal.div_mul_cancel (hμ _) (measure_ne_top μ _)]

/-! #### Questions with cells of one size

The cells of a coordinate projection all have one size. The literal listener over meanings is
then the listener over answers up to a constant, so the speakers who address them agree. -/

section EqualCells

variable (L : Kernel U M) [∀ u, IsZeroOrProbabilityMeasure (L u)] (q : M → X) {n : ℕ}
  (hq : ∀ m, (q ⁻¹' {q m}).ncard = n)
include hq

theorem qudListener_apply_singleton_of_ncard (u : U) (m : M) :
    qudListener L q u {m} = L u (q ⁻¹' {q m}) / n := by
  classical
  have hcard : ∀ m, (Finset.univ.filter fun m' ↦ q m = q m').card = n := fun m ↦ by
    rw [← hq m, ← Set.ncard_coe_finset]
    congr 1
    ext m'
    simp [eq_comm]
  have hsum : ∑ m', L u (q ⁻¹' {q m'}) = n * L u Set.univ :=
    calc ∑ m', L u (q ⁻¹' {q m'})
        = ∑ m', ∑ m'', if q m'' = q m' then L u {m''} else 0 := by
          refine Finset.sum_congr rfl fun m' _ ↦ ?_
          rw [← Finset.sum_filter, sum_measure_singleton]
          congr 1
          ext
          simp
      _ = ∑ m'', ∑ m', if q m'' = q m' then L u {m''} else 0 := Finset.sum_comm
      _ = ∑ m'', n * L u {m''} := by
          refine Finset.sum_congr rfl fun m'' _ ↦ ?_
          rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]
      _ = n * L u Set.univ := by rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ]
  rw [qudListener, Kernel.ofWeights_apply_singleton, hsum]
  rcases eq_zero_or_isProbabilityMeasure (L u) with h | h
  · simp [h]
  · rw [measure_univ, mul_one]

variable [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

theorem speaker_qudListener_dirac {α : ℝ} (hα : 0 ≤ α) (κ : U → ℝ) (m : M) :
    speaker α κ (qudListener L q) Measure.dirac m =
      speaker α κ (L.map q) Measure.dirac (q m) := by
  have hn : (n : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← hq m]
    exact Set.ncard_ne_zero_of_mem (a := m) rfl
  have hc0 : ((n : ℝ≥0∞) ^ α)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.rpow_ne_top_of_nonneg hα (ENNReal.natCast_ne_top n))
  have hc : ((n : ℝ≥0∞) ^ α)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hn) hα).ne'
  refine Measure.ext_of_singleton fun u ↦ ?_
  have hw : ∀ u', qudListener L q u' {m} ^ α * ENNReal.ofReal (Real.exp (-(α * κ u'))) =
      ((n : ℝ≥0∞) ^ α)⁻¹ *
        (L.map q u' {q m} ^ α * ENNReal.ofReal (Real.exp (-(α * κ u')))) := fun u' ↦ by
    rw [qudListener_apply_singleton_of_ncard L q hq, Kernel.map_apply_singleton,
      ENNReal.div_rpow_of_nonneg _ _ hα, div_eq_mul_inv, mul_comm (_ ^ α), mul_assoc]
  rw [speaker_dirac_apply_singleton, speaker_dirac_apply_singleton]
  simp only [hw]
  rw [← Finset.mul_sum, ENNReal.mul_div_mul_left _ _ hc0 hc]

end EqualCells

/-! #### The affect-aware models

The questions of Kao and Goodman's irony model and the goals of Kao and colleagues' hyperbole
model have cells of one size, so the speakers of both are speakers of the framework. -/

section AffectAware

private theorem ncard_project_kaoGoodman2015 (q : KaoGoodman2015.QUD)
    (m : KaoGoodman2015.Meaning) :
    (KaoGoodman2015.project q ⁻¹' {KaoGoodman2015.project q m}).ncard =
      if q = .state then 4 else 10 := by
  rw [show KaoGoodman2015.project q ⁻¹' {KaoGoodman2015.project q m} =
    ↑(Finset.univ.filter fun m' ↦ KaoGoodman2015.project q m' = KaoGoodman2015.project q m) by
      ext; simp, Set.ncard_coe_finset]
  revert q m
  decide

private theorem ncard_project_kaoWuEtAl2014 (g : KaoWuEtAl2014.Goal)
    (m : KaoWuEtAl2014.Meaning) :
    (KaoWuEtAl2014.project g ⁻¹' {KaoWuEtAl2014.project g m}).ncard =
      match g with
      | (.exact, .price) => 2 | (.approximate, .price) => 4 | (_, .affect) => 10
      | (.exact, .both) => 1 | (.approximate, .both) => 2 := by
  rw [show KaoWuEtAl2014.project g ⁻¹' {KaoWuEtAl2014.project g m} =
    ↑(Finset.univ.filter fun m' ↦ KaoWuEtAl2014.project g m' = KaoWuEtAl2014.project g m) by
      ext; simp, Set.ncard_coe_finset]
  revert g m
  decide

/-- The question-indexed speaker of Kao and Goodman's irony model is the framework's speaker at
the rhetorical function of the question, at a prior of positive mass everywhere. -/
theorem kaoGoodman2015_S1 (μ : Measure KaoGoodman2015.Meaning) [IsFiniteMeasure μ]
    (hμ : ∀ m, μ {m} ≠ 0) {α : ℝ} (hα : 0 ≤ α) (m : KaoGoodman2015.Meaning)
    (q : KaoGoodman2015.QUD) :
    KaoGoodman2015.S1 μ α (m, q) =
      S1 μ (rhetoricalOfQUD μ (KaoGoodman2015.L0 μ) KaoGoodman2015.project) α 0 q m := by
  have : ∀ u, IsZeroOrProbabilityMeasure (KaoGoodman2015.L0 μ u) := fun u ↦
    inferInstanceAs (IsZeroOrProbabilityMeasure (RSA.listener μ (truthful KaoGoodman2015.sem) u))
  rw [S1, L0_rhetoricalOfQUD μ hμ]
  exact (speaker_qudListener_dirac _ _ (ncard_project_kaoGoodman2015 q) hα 0 m).symm

/-- The goal-indexed speaker of Kao and colleagues' hyperbole model is the framework's speaker
at the rhetorical function of the goal, at a prior of positive mass everywhere. -/
theorem kaoWuEtAl2014_S1 (μ : Measure KaoWuEtAl2014.Meaning) [IsFiniteMeasure μ]
    (hμ : ∀ m, μ {m} ≠ 0) (c : ℝ) (m : KaoWuEtAl2014.Meaning) (g : KaoWuEtAl2014.Goal) :
    KaoWuEtAl2014.S1 μ c (m, g) =
      S1 μ (rhetoricalOfQUD μ (KaoWuEtAl2014.L0 μ) KaoWuEtAl2014.project) 1
        (KaoWuEtAl2014.cost c) g m := by
  have : ∀ u, IsZeroOrProbabilityMeasure (KaoWuEtAl2014.L0 μ u) := fun u ↦
    inferInstanceAs (IsZeroOrProbabilityMeasure (RSA.listener μ (truthful KaoWuEtAl2014.sem) u))
  rw [S1, L0_rhetoricalOfQUD μ hμ]
  exact (speaker_qudListener_dirac _ _ (ncard_project_kaoWuEtAl2014 g) zero_le_one _ m).symm

end AffectAware

/-! #### A literal listener beyond question-under-discussion RSA -/

theorem finite_setOf_qudListener (μ : Measure M) :
    {ν : Measure M | ∃ (sem : U → Set M) (X : Type*) (q : M → X) (u : U),
      ν = qudListener (RSA.listener μ (truthful sem)) q u}.Finite :=
  (Set.finite_range fun p : Set M × (M → Set M) ↦
      (∑ m, μ[|p.1] (p.2 m))⁻¹ • ∑ m, μ[|p.1] (p.2 m) • Measure.dirac m).subset <| by
    rintro ν ⟨sem, X, q, u, rfl⟩
    refine ⟨(sem u, fun m ↦ q ⁻¹' {q m}), ?_⟩
    simp only [qudListener, Kernel.ofWeights, Kernel.ofFunOfCountable_apply,
      listener_truthful_apply]

/-- Over two or more meanings and a prior of positive mass everywhere, some literal listener of the
framework is no question-under-discussion RSA literal listener (Lemma 2). -/
theorem exists_L0_ne_qudListener [Nontrivial M] (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : ∀ m, μ {m} ≠ 0) :
    ∃ f : R → U → M → ℝ≥0∞, (∀ r u m, f r u m ≤ 1) ∧
      ∀ (sem : U → Set M) {X : Type*} (q : M → X) (r : R) (u u' : U),
        L0 μ f r u ≠ qudListener (RSA.listener μ (truthful sem)) q u' := by
  obtain ⟨m₁, m₂, hne⟩ := exists_pair_ne M
  set ν : ℝ≥0∞ → Measure M := fun t ↦ t • Measure.dirac m₁ + (1 - t) • Measure.dirac m₂ with hν
  have huniv : ∀ t ∈ Set.Ioo (0 : ℝ≥0∞) 1, ν t Set.univ = 1 := fun t ht ↦ by
    simp [hν, add_tsub_cancel_of_le ht.2.le]
  have hval : ∀ t ∈ Set.Ioo (0 : ℝ≥0∞) 1, (ν t)[|Set.univ] {m₁} = t := fun t ht ↦ by
    rw [cond_apply MeasurableSet.univ, huniv t ht, inv_one, one_mul, Set.univ_inter]
    simp [hν, Set.indicator, hne.symm]
  have hinj : Set.InjOn (fun t ↦ (ν t)[|Set.univ]) (Set.Ioo 0 1) := fun a ha b hb h ↦ by
    have h' : (ν a)[|Set.univ] = (ν b)[|Set.univ] := h
    rw [← hval a ha, ← hval b hb, h']
  obtain ⟨_, ⟨t, ht, rfl⟩, hnot⟩ := (((Set.Ioo_infinite zero_lt_one).image hinj).sdiff
    (finite_setOf_qudListener (U := U) μ)).nonempty
  have hfin : ∀ (r : R) (u : U) (m : M), ν t {m} / μ {m} ≠ ∞ := fun _ _ m ↦
    ENNReal.div_ne_top ((measure_mono (Set.subset_univ _)).trans_lt
      ((huniv t ht).trans_lt ENNReal.one_lt_top)).ne (hμ m)
  obtain ⟨f, hf, hL0⟩ := exists_le_one_and_L0_eq μ hfin
  refine ⟨f, hf, fun sem X q r u u' h ↦ hnot ⟨sem, X, q, u', ?_⟩⟩
  rw [← h, hL0, L0, Kernel.ofDensity_div μ hμ (fun _ ↦ ν t)]

end QUD

/-! ### The running example

A speaker says *the weather is amazing* in a blizzard. The paper gives the rhetorical functions
of irony and hyperbole at this utterance at two meanings each, and the statements assume no more
of them. -/

section Weather

open KaoGoodman2015 (Weather)

/-- The rhetorical strategies of the running example. -/
inductive WeatherStrategy
  | literal | irony | hyperbole
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace WeatherStrategy := ⊤
instance : DiscreteMeasurableSpace WeatherStrategy := ⟨fun _ ↦ trivial⟩

variable (μ : Measure Weather) (f : WeatherStrategy → Weather → Weather → ℝ≥0∞) (α : ℝ)
  (κ : Weather → ℝ)

theorem literal_strategy_apply_eq_zero (hα : 0 < α)
    (hliteral : f .literal = fun u ↦ ({u} : Set Weather).indicator 1) {m : Weather}
    (hm : m ≠ .amazing) : L1 μ f α κ .literal .amazing {m} = 0 :=
  L1_indicator_apply_singleton_of_notMem μ f α κ hα (fun u ↦ {u}) hliteral hm

variable [IsFiniteMeasure μ] (ρ : Kernel Weather WeatherStrategy)

/-- The listener keeps the literal reading of *the weather is amazing* exactly when the strategy
posterior gives the literal strategy weight, since the ironic and the hyperbolic strategy both
exclude amazing weather at this utterance. -/
theorem literal_reading_iff (hα : 0 < α) (hf : ∀ r m, f r .amazing m ≠ ∞)
    (hliteral : f .literal .amazing .amazing ≠ 0) (hirony : f .irony .amazing .amazing = 0)
    (hhyperbole : f .hyperbole .amazing .amazing = 0) (hμ : μ {.amazing} ≠ 0) :
    listener μ f α κ ρ .amazing {.amazing} ≠ 0 ↔ ρ .amazing {.literal} ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff μ f α κ hα hf]
  constructor
  · rintro ⟨-, _ | _ | _, hr, hfr⟩
    · exact hr
    · exact absurd hirony hfr
    · exact absurd hhyperbole hfr
  · exact fun h ↦ ⟨hμ, .literal, h, hliteral⟩

theorem ironic_reading (hα : 0 < α) (hf : ∀ r m, f r .amazing m ≠ ∞)
    (hirony : f .irony .amazing .terrible ≠ 0) (hμ : μ {.terrible} ≠ 0)
    (hρ : ρ .amazing {.irony} ≠ 0) : listener μ f α κ ρ .amazing {.terrible} ≠ 0 :=
  (listener_apply_singleton_ne_zero_iff μ f α κ hα hf ρ _).mpr ⟨hμ, .irony, hρ, hirony⟩

theorem hyperbolic_reading (hα : 0 < α) (hf : ∀ r m, f r .amazing m ≠ ∞)
    (hhyperbole : f .hyperbole .amazing .good ≠ 0) (hμ : μ {.good} ≠ 0)
    (hρ : ρ .amazing {.hyperbole} ≠ 0) : listener μ f α κ ρ .amazing {.good} ≠ 0 :=
  (listener_apply_singleton_ne_zero_iff μ f α κ hα hf ρ _).mpr ⟨hμ, .hyperbole, hρ, hhyperbole⟩

end Weather

end SpinosoDiPianoEtAl2025
