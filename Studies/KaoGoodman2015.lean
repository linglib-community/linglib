module

public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Pragmatics.Probabilistic.QUD

/-!
# Kao and Goodman (2015): Let's Talk (Ironically) About the Weather

Kao and Goodman model irony with the question-under-discussion model that Kao and colleagues gave
for hyperbole, over meanings that pair a weather state with the speaker's valence and arousal
toward it. A weather context is a prior $\pi$ over states and the affect prior a kernel $\kappa$
from states to affect, so the literal listener who hears a state named believes $\kappa$ there
whatever the context, and [the speaker is the same in every
context](##KaoGoodman2015.S1_compProd_congr). The context enters at the pragmatic listener, who
[keeps the prior odds among the states the utterance does not
name](##KaoGoodman2015.nonliteral_odds): one "terrible" is hyperbole where bad weather is expected
and irony where amazing weather is. The affect space decides which affect she infers. With valence
the only affect in question, the utterance at whose state positive valence is least likely [never
raises its probability](##KaoGoodman2015.valence_le_prior). A speaker who addresses her arousal
[prefers the utterance at whose state her arousal is likelier](##KaoGoodman2015.S1_arousal_lt_iff),
and through the high arousal of terrible weather [a positive reading is
reached](##KaoGoodman2015.irony).

## Implementation notes

* Priors are arguments. The definitions take one measure on meanings, and the results about
  contexts take it as $\pi \otimes \kappa$, the state prior of a weather context composed with
  the affect prior of Experiment 1. The question prior is a measure on questions.
* Experiment 1's priors give every state and every affect positive probability, and then every
  meaning of positive prior is possible after every utterance. The results on possible meanings,
  `irony` and `valence_flip_needs_arousal`, describe priors with zeros, the limit in which an
  affect is excluded at a state.
* The model's fits to Experiment 2 are not stated.

## References

* [kao-goodman-2015]
* [kao-etal-2014-hyperbole]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoGoodman2015

/-- The weather states, which are also the utterances. -/
inductive Weather
  | terrible | bad | neutral | good | amazing
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Weather := ⊤
instance : DiscreteMeasurableSpace Weather := ⟨fun _ ↦ trivial⟩
instance : Nonempty Weather := ⟨.neutral⟩

/-- The speaker's affect records positive valence and high arousal. -/
abbrev Affect := Bool × Bool

/-- A meaning pairs the weather state with the speaker's affect toward it. -/
abbrev Meaning := Weather × Affect

/-- The question under discussion asks for the state or for a dimension of affect. -/
inductive QUD
  | state | valence | arousal
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨fun _ ↦ trivial⟩
instance : Nonempty QUD := ⟨.state⟩

/-- The projection of a question (eq. 1) reads off the state, the valence, or the arousal. -/
def project : QUD → Meaning → Weather ⊕ Bool
  | .state, m => .inl m.1
  | .valence, m => .inr m.2.1
  | .arousal, m => .inr m.2.2

/-- An utterance is true of the meanings whose state it names. -/
def sem (u : Weather) : Set Meaning := Prod.fst ⁻¹' {u}

/-- The literal listener conditions the prior on the state named. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Weather Meaning :=
  literalListener μ sem

instance (μ : Measure Meaning) : IsFiniteKernel (L0 μ) :=
  inferInstanceAs (IsFiniteKernel (literalListener _ _))

/-- The question-indexed speaker knows the answer to her question and is informative about the
literal listener's belief about it (eq. 1), at rationality `α` and no utterance cost. -/
noncomputable def S1 (μ : Measure Meaning) (α : ℝ) (p : Meaning × QUD) : Measure Weather :=
  qudSpeaker α 0 (L0 μ) (project p.2) p.1

instance (μ : Measure Meaning) (α : ℝ) (p : Meaning × QUD) : IsFiniteMeasure (S1 μ α p) :=
  inferInstanceAs (IsFiniteMeasure (qudSpeaker _ _ _ _ _))

/-- The pragmatic listener over meaning and question inverts the speaker against the product of
the meaning prior and the question prior; its first marginal is the meaning listener. -/
noncomputable def L1 (μ : Measure Meaning) (ν : Measure QUD) (α : ℝ) :
    Kernel Weather (Meaning × QUD) :=
  listener (μ.prod ν) (S1 μ α)

section Listener

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure QUD)
  [IsProbabilityMeasure ν] (α : ℝ)

theorem listener_ne_zero_iff (hα : 0 < α) (u : Weather) (m : Meaning) :
    (L1 μ ν α u).fst {m} ≠ 0 ↔ μ {m} ≠ 0 ∧
      ∃ q, ν {q} ≠ 0 ∧ ∃ m', project q m' = project q m ∧ m'.1 = u ∧ μ {m'} ≠ 0 :=
  listener_prod_fst_qudSpeaker_literalListener_apply_singleton_ne_zero_iff hα 0 μ ν sem
    project u m

-- Under the valence question, "terrible" can hyperbolically mean bad weather with negative
-- valence, through the negative valence of terrible weather.
theorem hyperbole (hα : 0 < α) (hν : ν {.valence} ≠ 0) {a a' : Bool}
    (hbad : μ {(.bad, false, a)} ≠ 0) (hterrible : μ {(.terrible, false, a')} ≠ 0) :
    (L1 μ ν α .terrible).fst {(.bad, false, a)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα]
  exact ⟨hbad, .valence, hν, (.terrible, false, a'), rfl, rfl, hterrible⟩

/-- Under the arousal question, "terrible" can ironically mean amazing weather with positive
valence and high arousal, through the high arousal of terrible weather. -/
theorem irony (hα : 0 < α) (hν : ν {.arousal} ≠ 0) {v : Bool}
    (hamazing : μ {(.amazing, true, true)} ≠ 0) (hterrible : μ {(.terrible, v, true)} ≠ 0) :
    (L1 μ ν α .terrible).fst {(.amazing, true, true)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα]
  exact ⟨hamazing, .arousal, hν, (.terrible, v, true), rfl, rfl, hterrible⟩

-- Without the arousal question, a positive-valence reading of "terrible" needs positive valence
-- to be possible at terrible weather itself.
theorem valence_flip_needs_arousal (hα : 0 < α) (hν : ∀ q, ν {q} ≠ 0 → q ≠ .arousal)
    {s : Weather} {a : Bool} (h : (L1 μ ν α .terrible).fst {(s, true, a)} ≠ 0) :
    ∃ a', μ {(.terrible, true, a')} ≠ 0 := by
  obtain ⟨hm, q, hq, ⟨s', v', a'⟩, hm', hs', hμ⟩ := (listener_ne_zero_iff μ ν α hα _ _).mp h
  simp only at hs'
  subst hs'
  rcases q with _ | _ | _
  · obtain rfl : Weather.terrible = s := Sum.inl.inj hm'
    exact ⟨a, hm⟩
  · obtain rfl : v' = true := Sum.inr.inj hm'
    exact ⟨a', hμ⟩
  · exact absurd rfl (hν _ hq)

omit [IsProbabilityMeasure ν] in
theorem S1_state_apply_singleton_of_ne (hα : 0 < α) {s u : Weather} (h : s ≠ u) (A : Affect) :
    S1 μ α ((s, A), .state) {u} = 0 := by
  by_contra h'
  obtain ⟨m', hm', hu, -⟩ := (qudSpeaker_literalListener_apply_singleton_ne_zero_iff hα 0
    μ sem (project .state) (s, A) u).mp h'
  exact h ((Sum.inl.inj hm').symm.trans hu)

omit [IsProbabilityMeasure ν] in
/-- Among the states an utterance does not name, at one affect, the listener keeps the prior
odds: the speaker says the same of them under every question, so which nonliteral state the
listener infers is decided by the weather context and the affect prior. -/
theorem nonliteral_odds (hα : 0 < α) {u s s' : Weather} (hs : s ≠ u) (hs' : s' ≠ u) (A : Affect) :
    (L1 μ ν α u).fst {(s, A)} * μ {(s', A)} = (L1 μ ν α u).fst {(s', A)} * μ {(s, A)} := by
  refine listener_prod_fst_apply_singleton_mul_eq μ ν (S1 μ α) fun q _ ↦ ?_
  cases q
  · rw [S1_state_apply_singleton_of_ne μ α hα hs, S1_state_apply_singleton_of_ne μ α hα hs']
  · rfl
  · rfl

end Listener

section Context

variable (π π' : Measure Weather) [IsProbabilityMeasure π] [IsProbabilityMeasure π']
  (κ : Kernel Weather Affect) [IsMarkovKernel κ] (ν : Measure QUD) [IsProbabilityMeasure ν] (α : ℝ)

omit [IsProbabilityMeasure π'] in
-- The literal listener who hears a state named believes that state and the affect prior there.
theorem L0_compProd {u : Weather} (hu : π {u} ≠ 0) :
    L0 (π ⊗ₘ κ) u = Measure.dirac u ⊗ₘ κ :=
  literalListener_preimage_fst_compProd π κ hu

/-- The speaker does not depend on the weather context: two contexts that leave every state
possible and share the affect prior have the same speaker, so the context enters an interpretation
through Bayes' rule at the pragmatic listener alone. -/
theorem S1_compProd_congr (hπ : ∀ u, π {u} ≠ 0) (hπ' : ∀ u, π' {u} ≠ 0) (p : Meaning × QUD) :
    S1 (π ⊗ₘ κ) α p = S1 (π' ⊗ₘ κ) α p := by
  have h : L0 (π ⊗ₘ κ) = L0 (π' ⊗ₘ κ) :=
    literalListener_preimage_fst_compProd_congr π π' κ hπ hπ'
  rw [S1, S1, h]

omit [IsProbabilityMeasure π'] in
private theorem map_L0_state (hπ : ∀ u, π {u} ≠ 0) (u s : Weather) :
    (L0 (π ⊗ₘ κ)).map (project .state) u {.inl s} = if u = s then 1 else 0 := by
  rw [Kernel.map_apply_singleton, L0_compProd π κ (hπ u),
    Measure.dirac_compProd_apply .of_discrete]
  split_ifs with h
  · rw [show Prod.mk u ⁻¹' (project .state ⁻¹' {Sum.inl s}) = Set.univ by ext; simp [project, h],
      measure_univ]
  · rw [show Prod.mk u ⁻¹' (project .state ⁻¹' {Sum.inl s}) = ∅ by ext; simp [project, h],
      measure_empty]

omit [IsProbabilityMeasure π'] in
private theorem map_L0_valence (hπ : ∀ u, π {u} ≠ 0) (u : Weather) (v : Bool) :
    (L0 (π ⊗ₘ κ)).map (project .valence) u {.inr v} = κ u (Prod.fst ⁻¹' {v}) := by
  rw [Kernel.map_apply_singleton, L0_compProd π κ (hπ u),
    Measure.dirac_compProd_apply .of_discrete]
  congr 1
  ext ⟨v', a⟩
  simp [project]

omit [IsProbabilityMeasure π'] in
private theorem S1_state_apply_self (hπ : ∀ u, π {u} ≠ 0) (hα : 0 < α) (t : Weather)
    (A : Affect) : S1 (π ⊗ₘ κ) α ((t, A), .state) {t} = 1 := by
  have h1 : (L0 (π ⊗ₘ κ)).map (project .state) t {.inl t} ≠ 0 := by
    simp [map_L0_state π κ hπ]
  have h2 : ∀ u' ≠ t, (L0 (π ⊗ₘ κ)).map (project .state) u' {.inl t} = 0 := fun u' hu' ↦ by
    simp [map_L0_state π κ hπ, hu']
  exact speaker_dirac_apply_singleton_eq_one hα h1 h2

omit [IsProbabilityMeasure π'] in
private theorem S1_valence_apply (hπ : ∀ u, π {u} ≠ 0) (m : Meaning) (t : Weather) :
    S1 (π ⊗ₘ κ) α (m, .valence) {t} =
      κ t (Prod.fst ⁻¹' {m.2.1}) ^ α / ∑ u, κ u (Prod.fst ⁻¹' {m.2.1}) ^ α := by
  rw [S1, qudSpeaker, speaker_dirac_zero_apply_singleton]
  simp only [project, map_L0_valence π κ hπ]

omit [IsProbabilityMeasure π'] in
private theorem map_L0_arousal (hπ : ∀ u, π {u} ≠ 0) (u : Weather) (a : Bool) :
    (L0 (π ⊗ₘ κ)).map (project .arousal) u {.inr a} = κ u (Prod.snd ⁻¹' {a}) := by
  rw [Kernel.map_apply_singleton, L0_compProd π κ (hπ u),
    Measure.dirac_compProd_apply .of_discrete]
  congr 1
  ext ⟨v, a'⟩
  simp [project]

omit [IsProbabilityMeasure π'] in
/-- A speaker who addresses her arousal prefers the utterance at whose state her arousal is
likelier. Where arousal is high at both extremes of the weather, "terrible" is a good utterance
for a speaker excited by amazing weather. -/
theorem S1_arousal_lt_iff (hπ : ∀ u, π {u} ≠ 0) (hα : 0 < α) (m : Meaning) {u u' : Weather} :
    (S1 (π ⊗ₘ κ) α (m, .arousal)).real {u} < (S1 (π ⊗ₘ κ) α (m, .arousal)).real {u'} ↔
      κ u (Prod.snd ⁻¹' {m.2.2}) < κ u' (Prod.snd ⁻¹' {m.2.2}) := by
  have hL (w : Weather) : (L0 (π ⊗ₘ κ)).map (project .arousal) w {project .arousal m} =
      κ w (Prod.snd ⁻¹' {m.2.2}) := map_L0_arousal π κ hπ w m.2.2
  rw [S1, qudSpeaker, speaker_dirac_real_singleton_lt_iff hα.le]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one,
    ENNReal.rpow_lt_rpow_iff hα, hL]

private theorem sum_qud (f : QUD → ℝ≥0∞) : ∑ q, f q = f .state + f .valence + f .arousal := by
  rw [show (Finset.univ : Finset QUD) = {.state, .valence, .arousal} from rfl]
  simp [add_assoc]

omit [IsProbabilityMeasure π'] [IsProbabilityMeasure ν] in
/-- With valence the only affect in question, the utterance at whose state positive valence is
least likely never raises the listener's probability of positive valence above its prior: the
speaker has no reason to choose a negative utterance to express positive affect. -/
theorem valence_le_prior (hπ : ∀ u, π {u} ≠ 0) (hα : 0 < α) (hν : ν {.arousal} = 0) {t : Weather}
    (ht : ∀ u, κ t (Prod.fst ⁻¹' {true}) ≤ κ u (Prod.fst ⁻¹' {true})) :
    (L1 (π ⊗ₘ κ) ν α t).fst {m | m.2.1 = true} ≤ (π ⊗ₘ κ) {m | m.2.1 = true} := by
  set Q : Set Affect := Prod.fst ⁻¹' {true} with hQ
  set P : Set Meaning := Prod.snd ⁻¹' Q with hP
  set σ : Bool → ℝ≥0∞ := fun v ↦
    κ t (Prod.fst ⁻¹' {v}) ^ α / ∑ u, κ u (Prod.fst ⁻¹' {v}) ^ α with hσ
  change (L1 (π ⊗ₘ κ) ν α).fst t P ≤ (π ⊗ₘ κ) P
  have hQc : (Prod.fst ⁻¹' {false} : Set Affect) = Qᶜ := by ext ⟨v, a⟩; cases v <;> simp [hQ]
  have hcompl : ∀ u, κ u Qᶜ ≤ κ t Qᶜ := fun u ↦ by
    rw [prob_compl_eq_one_sub .of_discrete, prob_compl_eq_one_sub .of_discrete]
    exact tsub_le_tsub_left (ht u) 1
  -- the speaker's mass on `t`, summed over questions
  have hg : ∀ m : Meaning, (∑ q, ν {q} • S1 (π ⊗ₘ κ) α (m, q)) {t} =
      ν {.state} * (sem t).indicator 1 m + ν {.valence} * σ m.2.1 := fun ⟨s, A⟩ ↦ by
    simp only [sum_apply, smul_apply, sum_qud, smul_eq_mul, hν, zero_mul,
      add_zero, S1_valence_apply π κ α hπ, hσ]
    by_cases hs : s = t
    · subst hs
      rw [S1_state_apply_self π κ α hπ hα, Set.indicator_of_mem (by simp [sem]), Pi.one_apply]
    · rw [S1_state_apply_singleton_of_ne _ α hα hs,
        Set.indicator_of_notMem (by simpa [sem] using hs)]
  -- the masses of the four cells
  have hμP : (π ⊗ₘ κ) P = ∫⁻ a, κ a Q ∂π := Measure.compProd_apply .of_discrete
  have hμN : (π ⊗ₘ κ) Pᶜ = ∫⁻ a, κ a Qᶜ ∂π := Measure.compProd_apply .of_discrete
  have hTP : (π ⊗ₘ κ) (sem t ∩ P) = π {t} * κ t Q := by
    rw [show sem t ∩ P = {t} ×ˢ Q by ext; simp [sem, hP],
      Measure.compProd_apply_prod .of_discrete .of_discrete, Measure.restrict_singleton,
      lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hTN : (π ⊗ₘ κ) (sem t ∩ Pᶜ) = π {t} * κ t Qᶜ := by
    rw [show sem t ∩ Pᶜ = {t} ×ˢ Qᶜ by ext; simp [sem, hP],
      Measure.compProd_apply_prod .of_discrete .of_discrete, Measure.restrict_singleton,
      lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hle : κ t Q ≤ (π ⊗ₘ κ) P := by
    rw [hμP]
    calc κ t Q = ∫⁻ _, κ t Q ∂π := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ a, κ a Q ∂π := lintegral_mono ht
  have hge : (π ⊗ₘ κ) Pᶜ ≤ κ t Qᶜ := by
    rw [hμN]
    calc ∫⁻ a, κ a Qᶜ ∂π ≤ ∫⁻ _, κ t Qᶜ ∂π := lintegral_mono hcompl
      _ = κ t Qᶜ := by rw [lintegral_const, measure_univ, mul_one]
  -- the two integrals of the speaker's mass
  have hA : ∫⁻ m in P, ν {.state} * (sem t).indicator 1 m + ν {.valence} * σ m.2.1 ∂(π ⊗ₘ κ) =
      ν {.state} * (π {t} * κ t Q) + ν {.valence} * σ true * (π ⊗ₘ κ) P := by
    rw [lintegral_add_left (.of_discrete), lintegral_const_mul _ (.of_discrete),
      lintegral_indicator_one .of_discrete, Measure.restrict_apply .of_discrete, hTP,
      setLIntegral_congr_fun (g := fun _ ↦ ν {.valence} * σ true) .of_discrete
        (fun m hm ↦ by rw [show m.2.1 = true from hm]), setLIntegral_const]
  have hB : ∫⁻ m in Pᶜ, ν {.state} * (sem t).indicator 1 m + ν {.valence} * σ m.2.1 ∂(π ⊗ₘ κ) =
      ν {.state} * (π {t} * κ t Qᶜ) + ν {.valence} * σ false * (π ⊗ₘ κ) Pᶜ := by
    rw [lintegral_add_left (.of_discrete), lintegral_const_mul _ (.of_discrete),
      lintegral_indicator_one .of_discrete, Measure.restrict_apply .of_discrete, hTN,
      setLIntegral_congr_fun (g := fun _ ↦ ν {.valence} * σ false) .of_discrete
        (fun m hm ↦ by rw [show m.2.1 = false from Bool.not_eq_true _ ▸ hm]), setLIntegral_const]
  -- the least likely affect gets at most the uniform share, its complement at least that
  have hσle : (π ⊗ₘ κ) Pᶜ ≠ 0 → σ true ≤ σ false := fun hN ↦ by
    have hY0 : ∑ u, κ u Qᶜ ^ α ≠ 0 := fun h0 ↦ hN <| by
      rw [hμN]
      refine (lintegral_eq_zero_iff (.of_discrete)).2 (.of_forall fun u ↦ ?_)
      exact (ENNReal.rpow_eq_zero_iff_of_pos hα).1
        ((Finset.sum_eq_zero_iff.1 h0) u (Finset.mem_univ u))
    have hY : ∑ u, κ u Qᶜ ^ α ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun u _ ↦ ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _)
    calc σ true ≤ (Fintype.card Weather : ℝ≥0∞)⁻¹ := by
          simpa [hσ] using Kernel.ofWeights_apply_singleton_le_inv_card
            (w := fun (_ : Unit) u ↦ κ u Q ^ α) (a := ()) (b := t)
            fun u ↦ ENNReal.rpow_le_rpow (ht u) hα.le
      _ ≤ σ false := by
          simpa [hσ, hQc] using Kernel.inv_card_le_ofWeights_apply_singleton
            (w := fun (_ : Unit) u ↦ κ u Qᶜ ^ α) (a := ()) (b := t)
            (fun u ↦ ENNReal.rpow_le_rpow (hcompl u) hα.le) hY0 hY
  -- Bayes' rule
  rw [L1, listener_prod_fst]
  refine listener_apply_le_of_setLIntegral_mul_le .of_discrete ?_
  simp_rw [hg]
  rw [hA, hB, add_mul, add_mul]
  refine add_le_add ?_ ?_
  · calc ν {.state} * (π {t} * κ t Q) * (π ⊗ₘ κ) Pᶜ
        ≤ ν {.state} * (π {t} * (π ⊗ₘ κ) P) * κ t Qᶜ := by gcongr
      _ = ν {.state} * (π {t} * κ t Qᶜ) * (π ⊗ₘ κ) P := by ring
  · rcases eq_or_ne ((π ⊗ₘ κ) Pᶜ) 0 with hN | hN
    · simp [hN]
    · calc ν {.valence} * σ true * (π ⊗ₘ κ) P * (π ⊗ₘ κ) Pᶜ
          ≤ ν {.valence} * σ false * (π ⊗ₘ κ) P * (π ⊗ₘ κ) Pᶜ := by gcongr; exact hσle hN
        _ = ν {.valence} * σ false * (π ⊗ₘ κ) Pᶜ * (π ⊗ₘ κ) P := by ring

end Context

end KaoGoodman2015
