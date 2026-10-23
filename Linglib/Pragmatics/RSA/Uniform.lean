module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Data.Multiset.Dominates
public import Linglib.Core.Probability.UniformOn

/-!
# Rational speech acts at a uniform prior

Franke and Bergen's model has finitely many states, Boolean meanings, a uniform prior and no
cost. Its literal listener is then uniform on the extension of the utterance, and its speaker
weighs each true utterance by the inverse size of its extension to the power of her rationality.
Her masses are ratios of inverse-power sums over informativity profiles, the multisets of
extension sizes of the utterances true at a state, so a comparison between two states is a
comparison of multisets of naturals. It holds at every rationality when one multiset dominates
the other, and at a natural rationality it is an inequality of naturals.

## Main definitions

* `RSA.profile sem A w`: the extension sizes of the utterances in `A` true at `w`.

## Main results

* `RSA.listener_uniformOn_truthful_apply`: the literal listener is uniform on the extension.
* `RSA.speaker_uniformOn_dirac_real_singleton_lt_of_card_lt`: of two true utterances the
  speaker prefers the one with the smaller extension.
* `RSA.speaker_uniformOn_dirac_real_finset_lt_of_strictDominates`: the speaker is likelier to
  choose within a set of utterances at one state than at another, at every rationality, when the
  products of their profiles are ordered by dominance.
* `RSA.listener_speaker_uniformOn_real_singleton_lt_of_strictDominates`: the pragmatic listener's
  preference between two states under the same condition.

## Implementation notes

* There are no new kernels. The literal listener is `RSA.listener` at the uniform prior and the
  truthful channel, and the speaker is `RSA.speaker` at no cost; this file abbreviates them
  `L₀` and `S₁[α]`.
* Meanings are `Finset`-valued, so that extension sizes, and with them the hypotheses of the
  comparison lemmas, are decidable.
* The comparison lemmas are stated for the speaker's mass on a set of utterances. The pragmatic
  listener is the case of a singleton, and the listener who hears only the form of the speaker's
  choice the case of the fibre of the form.

## References

* [franke-bergen-2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

/-! ### Informativity profiles -/

section Profile

variable {W U : Type*} [DecidableEq W] (sem : U → Finset W)

/-- The informativity profile of a state over a set `A` of utterances is the multiset of
extension sizes of the utterances in `A` true at the state. -/
def profile (A : Finset U) (w : W) : Multiset ℕ :=
  (A.filter (w ∈ sem ·)).val.map fun u ↦ (sem u).card

variable {sem} {A : Finset U} {w : W}

theorem zero_notMem_profile : 0 ∉ profile sem A w := by
  simp only [profile, Multiset.mem_map, Finset.mem_val, Finset.mem_filter, not_exists, not_and]
  exact fun u hu h ↦ Finset.card_ne_zero_of_mem hu.2 h

theorem profile_eq_zero_iff : profile sem A w = 0 ↔ ∀ u ∈ A, w ∉ sem u := by
  simp [profile]

theorem card_mem_profile {u : U} (hu : u ∈ A) (h : w ∈ sem u) : (sem u).card ∈ profile sem A w :=
  Multiset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨hu, h⟩)

variable (sem A w) in
theorem profile_add_profile_compl [Fintype U] [DecidableEq U] :
    profile sem A w + profile sem Aᶜ w = profile sem Finset.univ w := by
  have h₁ : A.filter (w ∈ sem ·) = (Finset.univ.filter (w ∈ sem ·)).filter (· ∈ A) := by
    ext; simp [and_comm]
  have h₂ : Aᶜ.filter (w ∈ sem ·) = (Finset.univ.filter (w ∈ sem ·)).filter (· ∉ A) := by
    ext; simp [and_comm]
  simp only [profile, h₁, h₂, ← Multiset.map_add, Finset.filter_val, Multiset.filter_add_not]

theorem profile_le_profile_univ [Fintype U] [DecidableEq U] :
    profile sem A w ≤ profile sem Finset.univ w :=
  profile_add_profile_compl sem A w ▸ le_self_add

end Profile

private theorem support_nonempty {W X : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] {b : X → Measure W} {x : X} [IsProbabilityMeasure (b x)]
    {S : Finset W} (hS : ∀ w, b x {w} ≠ 0 ↔ w ∈ S) : S.Nonempty := by
  by_contra h
  refine one_ne_zero (α := ℝ≥0∞) ?_
  rw [← measure_univ (μ := b x), ← Finset.coe_univ, ← sum_measure_singleton]
  exact Finset.sum_eq_zero fun w _ ↦ not_not.1 fun hw ↦ h ⟨w, (hS w).1 hw⟩

private theorem sum_div_lt_sum_div_of_cleared {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b z : ι → ℕ} (hb : ∀ i, b i ≠ 0 → z i ≠ 0)
    (hlt : ∑ i, a i * ∏ j ∈ Finset.univ.erase i, z j < ∑ i, b i * ∏ j ∈ Finset.univ.erase i, z j) :
    ∑ i, (a i : ℝ) / z i < ∑ i, (b i : ℝ) / z i := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_zero_of_lt hlt)
  have hz (i : ι) : (0 : ℝ) < z i := by
    rcases eq_or_ne i i₀ with rfl | hi
    · exact_mod_cast Nat.pos_of_ne_zero (hb i (left_ne_zero_of_mul hi₀))
    · exact_mod_cast Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi₀) i
        (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩))
  have key (f : ι → ℕ) : (∑ i, (f i : ℝ) / z i) * ∏ j, (z j : ℝ) =
      ((∑ i, f i * ∏ j ∈ Finset.univ.erase i, z j : ℕ) : ℝ) := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [div_mul_eq_mul_div, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← mul_assoc,
      mul_div_assoc, div_self (hz i).ne', mul_one]
  rw [← mul_lt_mul_iff_left₀ (Finset.prod_pos fun j _ ↦ hz j), key, key]
  exact_mod_cast hlt

section

variable {W U : Type*} (sem : U → Finset W) {α : ℝ} {w : W} {u : U}

private theorem inv_card_rpow_pos (h : w ∈ sem u) (α : ℝ) : (0 : ℝ) < ((sem u).card : ℝ)⁻¹ ^ α :=
  Real.rpow_pos_of_pos (inv_pos.2 (Nat.cast_pos.2 (Finset.card_pos.2 ⟨w, h⟩))) α

variable [DecidableEq W]

variable {sem} in
private theorem ite_inv_card_rpow_ne_top (hα : 0 ≤ α) :
    (if w ∈ sem u then ((sem u).card : ℝ≥0∞)⁻¹ ^ α else 0) ≠ ∞ := by
  split_ifs with h
  exacts [ENNReal.rpow_ne_top_of_nonneg hα (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2
    (Finset.card_ne_zero_of_mem h))), ENNReal.zero_ne_top]

private theorem toReal_invPowSum_profile (hα : 0 ≤ α) (A : Finset U) (w : W) :
    ((profile sem A w).invPowSum α).toReal =
      ∑ u ∈ A, if w ∈ sem u then ((sem u).card : ℝ)⁻¹ ^ α else 0 := by
  rw [Multiset.invPowSum_toReal hα zero_notMem_profile, profile, Multiset.map_map,
    ← Finset.sum_filter, Finset.sum_eq_multiset_sum]
  rfl

end

section Model

variable {W U : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W] [Fintype U]
  [MeasurableSpace U] [DiscreteMeasurableSpace U] (sem : U → Finset W)

/-! ### The literal listener -/

/-- The literal listener at a uniform prior. -/
local notation "L₀" => listener (uniformOn (Set.univ : Set W)) (truthful fun u ↦ (sem u : Set W))

/-- The literal listener at a uniform prior (eq. 5) is uniform on the extension of the
utterance. -/
theorem listener_uniformOn_truthful_apply (u : U) : L₀ u = uniformOn ↑(sem u) := by
  rw [listener_truthful_apply, uniformOn_cond Set.finite_univ .of_discrete, Set.univ_inter]

section

variable [DecidableEq W]

theorem listener_uniformOn_truthful_apply_singleton (u : U) (w : W) :
    L₀ u {w} = if w ∈ sem u then ((sem u).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [listener_uniformOn_truthful_apply, uniformOn_finset_apply_singleton]

theorem listener_uniformOn_truthful_real_singleton (u : U) (w : W) :
    (L₀ u).real {w} = if w ∈ sem u then ((sem u).card : ℝ)⁻¹ else 0 := by
  rw [measureReal_def, listener_uniformOn_truthful_apply_singleton]
  split <;> simp

end

/-! ### The speaker

The speaker of eq. 7 knows the state and addresses the literal listener at no cost. -/

/-- The speaker at a uniform prior and no cost. -/
local notation "S₁[" α "]" => speaker α 0 L₀ Measure.dirac

section Speaker

variable {α : ℝ}

theorem speaker_uniformOn_dirac_apply_singleton_ne_zero_iff (hα : 0 < α) (C : U → ℝ) (w : W)
    (u : U) : speaker α C L₀ Measure.dirac w {u} ≠ 0 ↔ w ∈ sem u := by
  rw [speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff hα]
  exact and_iff_left (uniformOn_univ_singleton_ne_zero w)

variable [DecidableEq W]

private theorem sum_rpow_listener (hα : 0 < α) (A : Finset U) (w : W) :
    ∑ u ∈ A, L₀ u {w} ^ α = (profile sem A w).invPowSum α := by
  simp_rw [listener_uniformOn_truthful_apply_singleton, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, ← Finset.sum_filter]
  rw [profile, Multiset.invPowSum, Multiset.map_map]
  rfl

theorem speaker_uniformOn_dirac_apply_finset (hα : 0 < α) (w : W) (A : Finset U) :
    S₁[α] w ↑A = (profile sem A w).invPowSum α / (profile sem Finset.univ w).invPowSum α := by
  rw [← sum_measure_singleton]
  simp_rw [speaker_dirac_zero_apply_singleton, div_eq_mul_inv]
  rw [← Finset.sum_mul, sum_rpow_listener sem hα, sum_rpow_listener sem hα]

/-- The speaker weighs each true utterance by the inverse size of its extension to the power
`α` (eq. 7). -/
theorem speaker_uniformOn_dirac_apply_singleton (hα : 0 < α) (w : W) (u : U) :
    S₁[α] w {u} = (if w ∈ sem u then ((sem u).card : ℝ≥0∞)⁻¹ ^ α else 0) /
      ∑ u', if w ∈ sem u' then ((sem u').card : ℝ≥0∞)⁻¹ ^ α else 0 := by
  simp only [speaker_dirac_zero_apply_singleton, listener_uniformOn_truthful_apply_singleton,
    apply_ite (· ^ α), ENNReal.zero_rpow_of_pos hα]

theorem speaker_uniformOn_dirac_real_singleton (hα : 0 < α) (w : W) (u : U) :
    (S₁[α] w).real {u} = (if w ∈ sem u then ((sem u).card : ℝ)⁻¹ ^ α else 0) /
      ∑ u', if w ∈ sem u' then ((sem u').card : ℝ)⁻¹ ^ α else 0 := by
  rw [measureReal_def, speaker_uniformOn_dirac_apply_singleton sem hα, ENNReal.toReal_div,
    ENNReal.toReal_sum fun u' _ ↦ ite_inv_card_rpow_ne_top hα.le]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- Of two true utterances, the speaker produces the one with the smaller extension more often
at every positive rationality, the qualitative claim of eq. 7. -/
theorem speaker_uniformOn_dirac_real_singleton_lt_of_card_lt (hα : 0 < α) {w : W} {u u' : U}
    (h : w ∈ sem u) (h' : w ∈ sem u') (hcard : (sem u').card < (sem u).card) :
    (S₁[α] w).real {u} < (S₁[α] w).real {u'} := by
  rw [speaker_uniformOn_dirac_real_singleton sem hα, speaker_uniformOn_dirac_real_singleton sem hα,
    ite_eq_left h, ite_eq_left h', ← toReal_invPowSum_profile sem hα.le]
  exact div_lt_div_of_pos_right (Real.rpow_lt_rpow (by positivity)
      (inv_strictAnti₀ (Nat.cast_pos.2 (Finset.card_pos.2 ⟨w, h'⟩)) (Nat.cast_lt.2 hcard)) hα)
    (ENNReal.toReal_pos (Multiset.invPowSum_pos hα.le fun h0 ↦
        profile_eq_zero_iff.1 h0 u (Finset.mem_univ u) h).ne'
      (Multiset.invPowSum_ne_top hα.le zero_notMem_profile))

theorem speaker_uniformOn_dirac_apply_singleton_of_profile_eq (hα : 0 < α) {w w' : W}
    (hprof : profile sem Finset.univ w = profile sem Finset.univ w') {u : U} (h : w ∈ sem u)
    (h' : w' ∈ sem u) : S₁[α] w {u} = S₁[α] w' {u} := by
  rw [speaker_dirac_zero_apply_singleton, speaker_dirac_zero_apply_singleton,
    sum_rpow_listener sem hα, sum_rpow_listener sem hα, hprof,
    listener_uniformOn_truthful_apply_singleton, listener_uniformOn_truthful_apply_singleton,
    ite_eq_left h, ite_eq_left h']

theorem speaker_uniformOn_dirac_real_singleton_lt_iff_invPowSum (hα : 0 < α) {w w' : W} {u : U}
    (h : w ∈ sem u) (h' : w' ∈ sem u) :
    (S₁[α] w').real {u} < (S₁[α] w).real {u} ↔
      (profile sem Finset.univ w).invPowSum α < (profile sem Finset.univ w').invPowSum α := by
  have htop (s : W) : (profile sem Finset.univ s).invPowSum α ≠ ∞ :=
    Multiset.invPowSum_ne_top hα.le zero_notMem_profile
  have hpos (s : W) (hs : s ∈ sem u) : 0 < ((profile sem Finset.univ s).invPowSum α).toReal :=
    ENNReal.toReal_pos (Multiset.invPowSum_pos hα.le fun h0 ↦
      profile_eq_zero_iff.1 h0 u (Finset.mem_univ u) hs).ne' (htop s)
  rw [speaker_uniformOn_dirac_real_singleton sem hα, speaker_uniformOn_dirac_real_singleton sem hα,
    ← toReal_invPowSum_profile sem hα.le, ← toReal_invPowSum_profile sem hα.le, ite_eq_left h,
    ite_eq_left h', ← ENNReal.toReal_lt_toReal (htop w) (htop w')]
  exact div_lt_div_iff_of_pos_left (inv_card_rpow_pos sem h α) (hpos w' h') (hpos w h)

theorem speaker_uniformOn_dirac_real_singleton_lt_of_ssubset (hα : 0 < α) {w w' : W} {u : U}
    (h : w ∈ sem u) (hsub : Finset.univ.filter (w ∈ sem ·) ⊂ Finset.univ.filter (w' ∈ sem ·)) :
    (S₁[α] w').real {u} < (S₁[α] w).real {u} := by
  have hmono (v : U) (hv : w ∈ sem v) : w' ∈ sem v := by simpa using hsub.1 (by simpa using hv)
  have hnonneg (s : W) (v : U) :
      (0 : ℝ) ≤ if s ∈ sem v then ((sem v).card : ℝ)⁻¹ ^ α else 0 := by
    split_ifs with hv
    exacts [(inv_card_rpow_pos sem hv α).le, le_rfl]
  obtain ⟨v₀, hv₀', hv₀⟩ := Finset.exists_of_ssubset hsub
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₀' hv₀
  rw [speaker_uniformOn_dirac_real_singleton sem hα, speaker_uniformOn_dirac_real_singleton sem hα,
    ite_eq_left h, ite_eq_left (hmono u h)]
  refine div_lt_div_of_pos_left (inv_card_rpow_pos sem h α) (Finset.sum_pos' (fun v _ ↦ hnonneg w v)
    ⟨u, Finset.mem_univ u, by rw [ite_eq_left h]; exact inv_card_rpow_pos sem h α⟩)
    (Finset.sum_lt_sum (fun v _ ↦ ?_) ⟨v₀, Finset.mem_univ v₀, ?_⟩)
  · by_cases hv : w ∈ sem v
    · rw [ite_eq_left hv, ite_eq_left (hmono v hv)]
    · rw [ite_eq_right hv]
      exact hnonneg w' v
  · rw [ite_eq_right hv₀, ite_eq_left hv₀']
    exact inv_card_rpow_pos sem hv₀' α

theorem speaker_uniformOn_dirac_real_singleton_of_profile_replicate (hα : 0 < α) {w : W} {u : U}
    {m n : ℕ} (hprof : profile sem Finset.univ w = Multiset.replicate m n) (h : w ∈ sem u) :
    (S₁[α] w).real {u} = (m : ℝ)⁻¹ := by
  have hn : (sem u).card = n :=
    Multiset.eq_of_mem_replicate (hprof ▸ card_mem_profile (Finset.mem_univ u) h)
  rw [speaker_uniformOn_dirac_real_singleton sem hα, ← toReal_invPowSum_profile sem hα.le,
    ite_eq_left h, hprof, hn, Multiset.invPowSum_replicate, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    div_mul_eq_div_div_swap, div_self (hn ▸ inv_card_rpow_pos sem h α).ne', one_div]

theorem tendsto_speaker_uniformOn_dirac_real_singleton_nhdsGT_zero (w : W) (u : U) :
    Filter.Tendsto (fun α : ℝ ↦ (S₁[α] w).real {u}) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((if w ∈ sem u then 1 else 0) / ((Finset.univ.filter (w ∈ sem ·)).card : ℝ))) := by
  have hlim (v : U) :
      Filter.Tendsto (fun α : ℝ ↦ if w ∈ sem v then ((sem v).card : ℝ)⁻¹ ^ α else 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (if w ∈ sem v then 1 else 0)) := by
    split_ifs with h
    · have := (Real.continuous_const_rpow (inv_card_rpow_pos sem h 1).ne').tendsto 0
      rw [Real.rpow_one] at this
      simpa using this.mono_left nhdsWithin_le_nhds
    · exact tendsto_const_nhds
  have hsum : Filter.Tendsto
      (fun α : ℝ ↦ ∑ v, if w ∈ sem v then ((sem v).card : ℝ)⁻¹ ^ α else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Finset.univ.filter (w ∈ sem ·)).card : ℝ)) := by
    simpa [Finset.sum_boole] using tendsto_finsetSum Finset.univ fun v _ ↦ hlim v
  by_cases h0 : (Finset.univ.filter (w ∈ sem ·)).card = 0
  · have hu : w ∉ sem u := fun h ↦
      Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ u, h⟩) h0
    rw [ite_eq_right hu, zero_div]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [speaker_uniformOn_dirac_real_singleton sem hα, ite_eq_right hu, zero_div]
  · refine Filter.Tendsto.congr' ?_ ((hlim u).div hsum (by exact_mod_cast h0))
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [speaker_uniformOn_dirac_real_singleton sem hα]
    rfl

theorem speaker_uniformOn_dirac_real_singleton_divPowSum {k D : ℕ} [NeZero k] [NeZero D] {w : W}
    (hdvd : ∀ n ∈ profile sem Finset.univ w, n ∣ D) (u : U) :
    (S₁[(k : ℝ)] w).real {u} = ((if w ∈ sem u then (D / (sem u).card) ^ k else 0 : ℕ) : ℝ) /
      ((profile sem Finset.univ w).divPowSum D k : ℝ) := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  rw [speaker_uniformOn_dirac_real_singleton sem hα, ← toReal_invPowSum_profile sem hα.le,
    Multiset.invPowSum_toReal_eq (NeZero.ne D) k hdvd]
  split_ifs with h
  · have hcard : (sem u).card ∣ D := hdvd _ (card_mem_profile (Finset.mem_univ u) h)
    rw [Real.rpow_natCast, Nat.cast_pow, Nat.cast_div hcard (Nat.cast_ne_zero.2
      (Finset.card_ne_zero_of_mem h)), div_pow, inv_pow, div_div_eq_mul_div, inv_mul_eq_div]
  · rw [Nat.cast_zero, zero_div, zero_div]

end Speaker

/-! ### A speaker who entertains several states

A speaker with a probability belief, facing the literal listener at no cost, weighs an utterance
by the support `S` of her belief alone. She says only the utterances true throughout `S`, each
with weight the inverse size of its extension to the power `α`. -/

section Belief

variable [DecidableEq W] {X : Type*} {α : ℝ} {b : X → Measure W} {x : X}
  [IsProbabilityMeasure (b x)] {S : Finset W}

private theorem weight_eq (hα : 0 < α) (hS : ∀ w, b x {w} ≠ 0 ↔ w ∈ S) (u : U) :
    (b x).geomMean (fun w ↦ L₀ u {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * (0 : U → ℝ) u))) =
      if S ⊆ sem u then ((sem u).card : ℝ≥0∞)⁻¹ ^ α else 0 := by
  rw [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  split_ifs with h
  · rw [Measure.geomMean_of_forall_eq fun w hw ↦ by
      rw [listener_uniformOn_truthful_apply_singleton, ite_eq_left (h ((hS w).1 hw))]]
  · obtain ⟨w, hw, hwu⟩ := Finset.not_subset.1 h
    rw [Measure.geomMean_eq_zero_iff.2 ⟨w, (hS w).2 hw, by
      rw [listener_uniformOn_truthful_apply_singleton, ite_eq_right hwu]⟩,
      ENNReal.zero_rpow_of_pos hα]

variable [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]

theorem speaker_uniformOn_apply_singleton (hα : 0 < α) (hS : ∀ w, b x {w} ≠ 0 ↔ w ∈ S) (u : U) :
    speaker α 0 L₀ b x {u} = (if S ⊆ sem u then ((sem u).card : ℝ≥0∞)⁻¹ ^ α else 0) /
      ∑ u', if S ⊆ sem u' then ((sem u').card : ℝ≥0∞)⁻¹ ^ α else 0 := by
  simp only [speaker_apply_singleton, weight_eq sem hα hS]

theorem speaker_uniformOn_real_singleton (hα : 0 < α) (hS : ∀ w, b x {w} ≠ 0 ↔ w ∈ S) (u : U) :
    (speaker α 0 L₀ b x).real {u} = (if S ⊆ sem u then ((sem u).card : ℝ)⁻¹ ^ α else 0) /
      ∑ u', if S ⊆ sem u' then ((sem u').card : ℝ)⁻¹ ^ α else 0 := by
  have hne (u' : U) : (if S ⊆ sem u' then ((sem u').card : ℝ≥0∞)⁻¹ ^ α else 0) ≠ ∞ := by
    split_ifs with h
    exacts [ENNReal.rpow_ne_top_of_nonneg hα.le (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2
      (Finset.card_ne_zero.2 ((support_nonempty hS).mono h)))), ENNReal.zero_ne_top]
  rw [measureReal_def, speaker_uniformOn_apply_singleton sem hα hS, ENNReal.toReal_div,
    ENNReal.toReal_sum fun u' _ ↦ hne u']
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem speaker_uniformOn_apply_eq_dirac (hα : 0 < α) (hS : ∀ w, b x {w} ≠ 0 ↔ w ∈ S) {w : W}
    (h : ∀ u, S ⊆ sem u ↔ w ∈ sem u) : speaker α 0 L₀ b x = S₁[α] w :=
  Measure.ext_of_singleton fun u ↦ by
    simp only [speaker_uniformOn_apply_singleton sem hα hS,
      speaker_uniformOn_dirac_apply_singleton sem hα, h]

end Belief

/-! ### Comparing two states

How likely the speaker is to choose within a set `A` of utterances at one state against another
is a comparison of profile sums. It holds at every positive rationality when the products of the
profile of `A` at one state with the profile of the remaining utterances at the other are ordered
by dominance, and at a natural rationality it is an inequality of naturals. The pragmatic
listener at a uniform prior ranks two states as the speaker produces what she heard. -/

section Compare

variable [DecidableEq W] [DecidableEq U] {α : ℝ} {A : Finset U} {w₁ w₂ : W}

theorem speaker_uniformOn_dirac_real_finset_lt_iff (hα : 0 < α) (A : Finset U) (w₂ : W)
    (h₁ : profile sem Finset.univ w₁ ≠ 0) :
    (S₁[α] w₁).real ↑A < (S₁[α] w₂).real ↑A ↔
      (profile sem A w₁).invPowSum α * (profile sem Finset.univ w₂).invPowSum α <
        (profile sem A w₂).invPowSum α * (profile sem Finset.univ w₁).invPowSum α := by
  have htop (B : Finset U) (w : W) : (profile sem B w).invPowSum α ≠ ∞ :=
    Multiset.invPowSum_ne_top hα.le zero_notMem_profile
  rw [measureReal_def, measureReal_def,
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _),
    speaker_uniformOn_dirac_apply_finset sem hα, speaker_uniformOn_dirac_apply_finset sem hα,
    ENNReal.div_lt_iff (.inl (Multiset.invPowSum_pos hα.le h₁).ne') (.inl (htop _ _))]
  rcases eq_or_ne (profile sem Finset.univ w₂) 0 with h₂ | h₂
  · simp [h₂, Multiset.le_zero.1 (h₂ ▸ profile_le_profile_univ (A := A))]
  · rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt
      (.inl (Multiset.invPowSum_pos hα.le h₂).ne') (.inl (htop _ _))]

/-- The speaker is likelier to choose within `A` at `w₂` than at `w₁`, at every positive
rationality, when the products of profiles are ordered by strict dominance. -/
theorem speaker_uniformOn_dirac_real_finset_lt_of_strictDominates (hα : 0 < α)
    (h : ((profile sem A w₂).prodMul (profile sem Aᶜ w₁)).StrictDominates
      ((profile sem A w₁).prodMul (profile sem Aᶜ w₂))) :
    (S₁[α] w₁).real ↑A < (S₁[α] w₂).real ↑A := by
  have htop (B : Finset U) (w : W) : (profile sem B w).invPowSum α ≠ ∞ :=
    Multiset.invPowSum_ne_top hα.le zero_notMem_profile
  have h₁ : profile sem Finset.univ w₁ ≠ 0 := fun h0 ↦ h.ne_zero <|
    Multiset.prodMul_eq_zero_iff.2 <| .inr <| Multiset.le_zero.1 (h0 ▸ profile_le_profile_univ)
  have hodds : (profile sem A w₁).invPowSum α * (profile sem Aᶜ w₂).invPowSum α <
      (profile sem A w₂).invPowSum α * (profile sem Aᶜ w₁).invPowSum α := by
    rw [← Multiset.invPowSum_prodMul hα.le, ← Multiset.invPowSum_prodMul hα.le]
    exact h.invPowSum_lt hα (Multiset.zero_notMem_prodMul zero_notMem_profile zero_notMem_profile)
  rw [speaker_uniformOn_dirac_real_finset_lt_iff sem hα A w₂ h₁,
    ← profile_add_profile_compl sem A w₁, ← profile_add_profile_compl sem A w₂,
    Multiset.invPowSum_add, Multiset.invPowSum_add, mul_add, mul_add,
    mul_comm ((profile sem A w₂).invPowSum α)]
  exact ENNReal.add_lt_add_left (ENNReal.mul_ne_top (htop _ _) (htop _ _)) hodds

theorem speaker_uniformOn_dirac_real_finset_lt_of_divPowSum {k D : ℕ} [NeZero k] [NeZero D]
    (hdvd₁ : ∀ n ∈ profile sem Finset.univ w₁, n ∣ D)
    (hdvd₂ : ∀ n ∈ profile sem Finset.univ w₂, n ∣ D)
    (hlt : (profile sem A w₁).divPowSum D k * (profile sem Finset.univ w₂).divPowSum D k <
      (profile sem A w₂).divPowSum D k * (profile sem Finset.univ w₁).divPowSum D k) :
    (S₁[(k : ℝ)] w₁).real ↑A < (S₁[(k : ℝ)] w₂).real ↑A := by
  have hα : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have htop (B : Finset U) (w : W) : (profile sem B w).invPowSum k ≠ ∞ :=
    Multiset.invPowSum_ne_top hα.le zero_notMem_profile
  have hsub (w : W) (n : ℕ) (hn : n ∈ profile sem A w) : n ∈ profile sem Finset.univ w :=
    Multiset.mem_of_le profile_le_profile_univ hn
  rw [speaker_uniformOn_dirac_real_finset_lt_iff sem hα A w₂ (Multiset.ne_zero_of_divPowSum_ne_zero
      (right_ne_zero_of_mul (Nat.ne_zero_of_lt hlt))),
    ← ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (htop _ _) (htop _ _))
      (ENNReal.mul_ne_top (htop _ _) (htop _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul,
    Multiset.invPowSum_toReal_eq (NeZero.ne D) k fun n hn ↦ hdvd₁ n (hsub w₁ n hn),
    Multiset.invPowSum_toReal_eq (NeZero.ne D) k hdvd₂,
    Multiset.invPowSum_toReal_eq (NeZero.ne D) k fun n hn ↦ hdvd₂ n (hsub w₂ n hn),
    Multiset.invPowSum_toReal_eq (NeZero.ne D) k hdvd₁, div_mul_div_comm, div_mul_div_comm,
    div_lt_div_iff_of_pos_right (by have := NeZero.ne D; positivity)]
  exact_mod_cast hlt

/-- Hearing an utterance, the pragmatic listener at a uniform prior prefers `w₂` to `w₁` at every
positive rationality when the products of profiles are ordered by strict dominance. -/
theorem listener_speaker_uniformOn_real_singleton_lt_of_strictDominates (hα : 0 < α) {u : U}
    (h : ((profile sem {u} w₂).prodMul (profile sem {u}ᶜ w₁)).StrictDominates
      ((profile sem {u} w₁).prodMul (profile sem {u}ᶜ w₂))) :
    (listener (uniformOn Set.univ) S₁[α] u).real {w₁} <
      (listener (uniformOn Set.univ) S₁[α] u).real {w₂} := by
  rw [listener_uniformOn_real_lt_iff]
  simpa using speaker_uniformOn_dirac_real_finset_lt_of_strictDominates sem hα h

end Compare

/-! ### The listener who hears the form

When the listener hears only the form `obs u` of the speaker's choice (eqs. 18b and 21b), her
belief about the state compares how likely the speaker is to choose within the fibre of the form,
and her belief about the choice compares how likely the states together are to produce it. -/

section Form

variable [DecidableEq W] {O : Type*} [MeasurableSpace O] [MeasurableSingletonClass O]
  [Countable O] [DecidableEq O] (obs : U → O) {α : ℝ} {o : O} {w₁ w₂ : W} {k D : ℕ} [NeZero k]
  [NeZero D]

/-- Hearing a form at a natural rationality, the listener's preference between two choices with
that form is an inequality of naturals. Each side is the choice's weight times, summed over the
states it is true at, the product of the other states' profile sums. -/
theorem listener_compProd_speaker_uniformOn_snd_real_lt_of_divPowSum
    (hdvd : ∀ w : W, ∀ n ∈ profile sem Finset.univ w, n ∣ D) {u₁ u₂ : U} (h₁ : obs u₁ = o)
    (h₂ : obs u₂ = o)
    (hlt : (D / (sem u₁).card) ^ k * ∑ w ∈ sem u₁, ∏ w' ∈ Finset.univ.erase w,
        (profile sem Finset.univ w').divPowSum D k <
      (D / (sem u₂).card) ^ k * ∑ w ∈ sem u₂, ∏ w' ∈ Finset.univ.erase w,
        (profile sem Finset.univ w').divPowSum D k) :
    (listener (uniformOn Set.univ ⊗ₘ S₁[(k : ℝ)]) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real
        {u₁} <
      (listener (uniformOn Set.univ ⊗ₘ S₁[(k : ℝ)]) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real
        {u₂} := by
  have key (u : U) : ∑ w, (if w ∈ sem u then (D / (sem u).card) ^ k else 0) *
        ∏ w' ∈ Finset.univ.erase w, (profile sem Finset.univ w').divPowSum D k =
      (D / (sem u).card) ^ k * ∑ w ∈ sem u, ∏ w' ∈ Finset.univ.erase w,
        (profile sem Finset.univ w').divPowSum D k := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  have := sum_div_lt_sum_div_of_cleared
    (z := fun w ↦ (profile sem Finset.univ w).divPowSum D k)
    (a := fun w ↦ if w ∈ sem u₁ then (D / (sem u₁).card) ^ k else 0)
    (b := fun w ↦ if w ∈ sem u₂ then (D / (sem u₂).card) ^ k else 0)
    (fun w hw ↦ (Multiset.divPowSum_pos (NeZero.ne D) (hdvd w) fun h0 ↦
      profile_eq_zero_iff.1 h0 u₂ (Finset.mem_univ u₂) (by_contra fun h ↦ hw (ite_eq_right h))).ne')
    (by rw [key, key]; exact hlt)
  rw [listener_uniformOn_compProd_dirac_snd_real_lt_iff _ obs h₁ h₂]
  simp_rw [speaker_uniformOn_dirac_real_singleton_divPowSum sem (hdvd _)]
  exact this

variable [DecidableEq U]

/-- Hearing a form, the listener prefers `w₂` to `w₁` at every positive rationality when the
products of profiles over the fibre of the form are ordered by strict dominance. -/
theorem listener_compProd_speaker_uniformOn_fst_real_lt_of_strictDominates (hα : 0 < α)
    (h : ((profile sem (Finset.univ.filter (obs · = o)) w₂).prodMul
        (profile sem (Finset.univ.filter (obs · = o))ᶜ w₁)).StrictDominates
      ((profile sem (Finset.univ.filter (obs · = o)) w₁).prodMul
        (profile sem (Finset.univ.filter (obs · = o))ᶜ w₂))) :
    (listener (uniformOn Set.univ ⊗ₘ S₁[α]) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₁} <
      (listener (uniformOn Set.univ ⊗ₘ S₁[α]) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₂} :=
  (listener_uniformOn_compProd_dirac_fst_real_lt_iff _ obs o w₁ w₂).2
    (speaker_uniformOn_dirac_real_finset_lt_of_strictDominates sem hα h)

/-- Hearing a form at a natural rationality, the listener's preference between two states is an
inequality of naturals. -/
theorem listener_compProd_speaker_uniformOn_fst_real_lt_of_divPowSum
    (hdvd₁ : ∀ n ∈ profile sem Finset.univ w₁, n ∣ D)
    (hdvd₂ : ∀ n ∈ profile sem Finset.univ w₂, n ∣ D)
    (hlt : (profile sem (Finset.univ.filter (obs · = o)) w₁).divPowSum D k *
        (profile sem Finset.univ w₂).divPowSum D k <
      (profile sem (Finset.univ.filter (obs · = o)) w₂).divPowSum D k *
        (profile sem Finset.univ w₁).divPowSum D k) :
    (listener (uniformOn Set.univ ⊗ₘ S₁[(k : ℝ)]) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real
        {w₁} <
      (listener (uniformOn Set.univ ⊗ₘ S₁[(k : ℝ)]) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real
        {w₂} :=
  (listener_uniformOn_compProd_dirac_fst_real_lt_iff _ obs o w₁ w₂).2
    (speaker_uniformOn_dirac_real_finset_lt_of_divPowSum sem hdvd₁ hdvd₂ hlt)

end Form

end Model

/-! ### Latent families

A latent the speaker also knows, a lexicon or a parse, indexes the meaning, and the listener at
a uniform prior over pairs of a state and a latent inverts the speaker of each latent. -/

section Family

variable {W U Λ : Type*} [Fintype W] [DecidableEq W] [MeasurableSpace W]
  [DiscreteMeasurableSpace W] [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
  [Fintype Λ] [DecidableEq Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
  (sem : Λ → U → Finset W) {k D : ℕ} [NeZero k] [NeZero D]

/-- At a natural rationality, the listener's preference between two events of pairs of a state
and a latent is an inequality of naturals. Each side sums, over the pairs of the event, the
utterance's weight at the pair times the product of the other pairs' profile sums. -/
theorem listener_uniformOn_family_real_lt_of_divPowSum
    (hdvd : ∀ l w, ∀ n ∈ profile (sem l) Finset.univ w, n ∣ D) {u : U} {E₁ E₂ : Finset (W × Λ)}
    (hlt : ∑ p ∈ E₁, (if p.1 ∈ sem p.2 u then (D / (sem p.2 u).card) ^ k else 0) *
        ∏ q ∈ Finset.univ.erase p, (profile (sem q.2) Finset.univ q.1).divPowSum D k <
      ∑ p ∈ E₂, (if p.1 ∈ sem p.2 u then (D / (sem p.2 u).card) ^ k else 0) *
        ∏ q ∈ Finset.univ.erase p, (profile (sem q.2) Finset.univ q.1).divPowSum D k) :
    (listener (uniformOn Set.univ) (fun p : W × Λ ↦ speaker (k : ℝ) 0
      (listener (uniformOn Set.univ) (truthful fun u ↦ (sem p.2 u : Set W))) Measure.dirac p.1)
        u).real ↑E₁ <
      (listener (uniformOn Set.univ) (fun p : W × Λ ↦ speaker (k : ℝ) 0
        (listener (uniformOn Set.univ) (truthful fun u ↦ (sem p.2 u : Set W))) Measure.dirac p.1)
          u).real ↑E₂ := by
  have := sum_div_lt_sum_div_of_cleared
    (z := fun p : W × Λ ↦ (profile (sem p.2) Finset.univ p.1).divPowSum D k)
    (a := fun p ↦ if p ∈ E₁ then if p.1 ∈ sem p.2 u then (D / (sem p.2 u).card) ^ k else 0 else 0)
    (b := fun p ↦ if p ∈ E₂ then if p.1 ∈ sem p.2 u then (D / (sem p.2 u).card) ^ k else 0 else 0)
    (fun p hp ↦ (Multiset.divPowSum_pos (NeZero.ne D) (hdvd p.2 p.1) fun h0 ↦
      profile_eq_zero_iff.1 h0 u (Finset.mem_univ u) (by_contra fun h ↦ hp (by simp [h]))).ne')
    (by simpa only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] using hlt)
  rw [listener_uniformOn_real_finset_lt_iff]
  simp_rw [speaker_uniformOn_dirac_real_singleton_divPowSum (sem _) (hdvd _ _)]
  simpa only [Nat.cast_ite, Nat.cast_zero, ite_div, zero_div, Finset.sum_ite_mem,
    Finset.univ_inter] using this

end Family

end RSA
