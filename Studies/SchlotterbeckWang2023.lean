module

public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.UniformOn
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Pragmatics.RSA.Incremental

/-!
# Schlotterbeck & Wang (2023): An incremental RSA model for adjective ordering preferences

This file formalizes the paper's fully incremental Rational Speech Act model (Table 1) and the
qualitative predictions it draws from it for the order of two prenominal adjectives. The
incremental literal listener (`l0`) interprets a word sequence from the noun outward, each word
against the support of the distribution the later words left, so a context-dependent meaning such
as the k%-semantics of a dimension adjective (`kPercent`) can resolve differently in the two
orders. The incremental sequence speaker produces the words left to right, scoring each prefix by
its utility for the referent and each word by a language model (`seqSpeaker`); the global speaker
scores whole sequences, and the incremental utterance speaker is a softmax over the sequence
speaker with an utterance prior.

The paper's theoretical result is the listener-level sanity check: at a context-independent
semantics the incremental listener is the one-shot literal listener at the product meaning,
because Bayesian updates compose, so it cannot distinguish word orders (`l0_perm`), and the
global speaker is then indifferent between them. The speaker-level prediction, the effect of
discriminatory strength, comes from the language model that produces either adjective first and
then the other: with an order-blind listener the sequence speaker's preference between the two
orders is its preference between their first words, and at a uniform prior and Boolean meanings
the more informative first word is the one true of fewer referents
(`seqSpeaker_real_lt_of_card_lt`). The k%-semantics witnesses that the listener does distinguish
orders once meanings depend on the comparison class (`l0_big_blue_ne`).

## Implementation notes

* Meanings are graded and bounded by one; the comparison class is a finset of referents, and
  the support of a distribution is the finset of referents it gives positive mass. Sequences are
  surface-order lists with the noun-adjacent word last, and the speakers over sequences of a
  fixed length are weight kernels on `Fin n → U`.
* The paper leaves the cost function unspecified; here the cost factor `exp (−β c)` depends on
  the sequence length alone, which covers per-word costs and cost zero, and the rationality `β`
  is free rather than pinned to the paper's one.
* With the noise floor `ε > 0` of the paper's color semantics no color word empties the
  support, so in the paper's simulations every later word is interpreted against the whole
  display; the order-sensitivity witness uses a sharp color meaning. The perceptual blur of the
  size distribution manipulation is not modeled.

## References

* [schlotterbeck-wang-2023]
* [cohn-gordon-goodman-potts-2019]
* [degen-etal-2020]
* [scontras-degen-goodman-2017]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace SchlotterbeckWang2023

variable {U R : Type*}

private theorem mul_lt_mul_right_iff {a b c : ℝ≥0∞} (h0 : c ≠ 0) (hc : c ≠ ∞) :
    a * c < b * c ↔ a < b :=
  ⟨fun h ↦ lt_of_not_ge fun hba ↦ h.not_ge (mul_le_mul' hba le_rfl),
    ENNReal.mul_lt_mul_left h0 hc⟩

private theorem mul_lt_mul_left_iff {a b c : ℝ≥0∞} (h0 : c ≠ 0) (hc : c ≠ ∞) :
    c * a < c * b ↔ a < b :=
  ⟨fun h ↦ lt_of_not_ge fun hba ↦ h.not_ge (mul_le_mul' le_rfl hba),
    ENNReal.mul_lt_mul_right h0 hc⟩

private theorem ofFn_pair (x y : U) : List.ofFn ![x, y] = [x, y] := by simp [List.ofFn_succ]

/-! ### Meanings and the language model -/

/-- A Boolean semantics, as graded meanings. -/
noncomputable def sharp (ext : U → Finset R → Finset R) : U → Finset R → R → ℝ≥0∞ :=
  fun u C => ((ext u C : Set R)).indicator 1

theorem sharp_apply_le_one (ext : U → Finset R → Finset R) (u : U) (C : Finset R) (r : R) :
    sharp ext u C r ≤ 1 := by
  unfold sharp Set.indicator
  split_ifs <;> simp

/-- The sequentially intersective update of a Boolean semantics builds the extension of a
sequence from the noun outward. -/
def extSeq [Fintype R] [DecidableEq R] (ext : U → Finset R → Finset R) : List U → Finset R
  | [] => Finset.univ
  | u :: us => extSeq ext us ∩ ext u (extSeq ext us)

/-- The paper's language model puts either adjective first, with equal probability, then the
other. -/
noncomputable def alternation [DecidableEq U] (a b : U) : List U → U → ℝ≥0∞
  | [], u => if u = a ∨ u = b then 2⁻¹ else 0
  | [u'], u => if u' = a ∧ u = b ∨ u' = b ∧ u = a then 1 else 0
  | _, _ => 0

theorem alternation_comm [DecidableEq U] (a b : U) : alternation a b = alternation b a := by
  funext us u
  cases us with
  | nil => simp [alternation, or_comm]
  | cons u' us => cases us <;> simp [alternation, or_comm]

theorem alternation_ne_top [DecidableEq U] {a b : U} (us : List U) (u : U) :
    alternation a b us u ≠ ∞ := by
  cases us with
  | nil => simp only [alternation]; split_ifs <;> simp
  | cons u' us => cases us <;> simp only [alternation] <;> (try split_ifs) <;> simp

open Classical in
/-- The support of a distribution over referents, the comparison class the next word is
interpreted against. -/
noncomputable def supp [Fintype R] [MeasurableSpace R] (ν : Measure R) : Finset R :=
  Finset.univ.filter fun r => ν {r} ≠ 0

theorem mem_supp [Fintype R] [MeasurableSpace R] {ν : Measure R} {r : R} :
    r ∈ supp ν ↔ ν {r} ≠ 0 := by
  simp [supp]

section

variable [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U] [Fintype R] [MeasurableSpace R]

/-! ### The incremental listener (rows 1–2) -/

/-- The incremental literal listener of rows (1)–(2) reads a word sequence in surface order,
the noun-adjacent word last. That word is interpreted first, against the prior's support, and
each earlier word against the support of the distribution the later words left. -/
noncomputable def l0 (μ : Measure R) (sem : U → Finset R → R → ℝ≥0∞) : List U → Measure R
  | [] => μ
  | u :: us => Kernel.ofDensity (l0 μ sem us) (fun u' => sem u' (supp (l0 μ sem us))) u

theorem l0_apply_le_one {μ : Measure R} {sem : U → Finset R → R → ℝ≥0∞} [IsProbabilityMeasure μ]
    (us : List U) (s : Set R) :
    l0 μ sem us s ≤ 1 := by
  cases us with
  | nil => exact prob_le_one (μ := μ)
  | cons u us => rw [l0, Kernel.ofDensity_apply]; exact prob_le_one

/-! ### Utilities and sequence weights (rows 4–5 and 7) -/

variable (μ : Measure R) (sem : U → Finset R → R → ℝ≥0∞)

/-- The utility of row (7) scores the sequence `us` for the referent `r` at rationality `β`,
with `cost n` the cost factor `exp (−β c)` of an `n`-word sequence. -/
noncomputable def utility (β : ℝ) (cost : ℕ → ℝ≥0∞) (us : List U) (r : R) : ℝ≥0∞ :=
  l0 μ sem us {r} ^ β * cost us.length

/-- Unrolling rows (4)–(5), the weight of producing `us` word by word scores each prefix by its
utility and each word by the language model's probability given the words before it. -/
noncomputable def seqWeight (β : ℝ) (cost : ℕ → ℝ≥0∞) (pLang : List U → U → ℝ≥0∞) (r : R)
    (us : List U) : ℝ≥0∞ :=
  ∏ i : Fin us.length, utility μ sem β cost (us.take (i.1 + 1)) r * pLang (us.take i.1) us[i]

variable {μ : Measure R} {sem : U → Finset R → R → ℝ≥0∞} {β : ℝ} {cost : ℕ → ℝ≥0∞}
  {pLang : List U → U → ℝ≥0∞} {r : R} {a b : U}

theorem utility_ne_top [IsProbabilityMeasure μ] (hβ : 0 ≤ β) (hcost : ∀ n, cost n ≠ ∞)
    (us : List U) : utility μ sem β cost us r ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hβ
    (ne_top_of_le_ne_top ENNReal.one_ne_top (l0_apply_le_one us _))) (hcost _)

/-! ### Two adjectives -/

theorem seqWeight_pair_alternation [DecidableEq U] (r : R) (a b : U) :
    seqWeight μ sem β cost (alternation a b) r [a, b] =
      2⁻¹ * (utility μ sem β cost [a] r * utility μ sem β cost [a, b] r) := by
  simp [seqWeight, Fin.prod_univ_two, alternation]
  ring

theorem seqWeight_pair_lt_iff [DecidableEq U] (r : R) (a b : U) :
    seqWeight μ sem β cost (alternation a b) r [a, b] <
        seqWeight μ sem β cost (alternation a b) r [b, a] ↔
      utility μ sem β cost [a] r * utility μ sem β cost [a, b] r <
        utility μ sem β cost [b] r * utility μ sem β cost [b, a] r := by
  rw [seqWeight_pair_alternation, alternation_comm, seqWeight_pair_alternation]
  exact mul_lt_mul_left_iff (by simp) (by simp)

theorem seqWeight_pair_lt_iff_of_l0_eq [DecidableEq U] [IsProbabilityMeasure μ] (hβ : 0 ≤ β)
    (hcost : ∀ n, cost n ≠ ∞) (hl : l0 μ sem [a, b] = l0 μ sem [b, a])
    (hne : utility μ sem β cost [a, b] r ≠ 0) :
    seqWeight μ sem β cost (alternation a b) r [a, b] <
        seqWeight μ sem β cost (alternation a b) r [b, a] ↔
      utility μ sem β cost [a] r < utility μ sem β cost [b] r := by
  rw [seqWeight_pair_lt_iff, show utility μ sem β cost [b, a] r = utility μ sem β cost [a, b] r by
    simp only [utility, ← hl, List.length_cons, List.length_nil]]
  exact mul_lt_mul_right_iff hne (utility_ne_top hβ hcost _)

theorem utility_single_lt_iff (hβ : 0 < β) (h0 : cost 1 ≠ 0) (htop : cost 1 ≠ ∞) :
    utility μ sem β cost [a] r < utility μ sem β cost [b] r ↔
      l0 μ sem [a] {r} < l0 μ sem [b] {r} := by
  simp only [utility, List.length_singleton]
  rw [mul_lt_mul_right_iff h0 htop, ENNReal.rpow_lt_rpow_iff hβ]

end

section

variable [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U] [Fintype R] [MeasurableSpace R]
  [DiscreteMeasurableSpace R]
  {μ : Measure R} {sem : U → Finset R → R → ℝ≥0∞} {β : ℝ} {cost : ℕ → ℝ≥0∞}
  {pLang : List U → U → ℝ≥0∞} {r : R} {a b : U}

/-! ### Order-blind listeners -/

theorem l0_contextFree [IsProbabilityMeasure μ] (m : U → R → ℝ≥0∞) (hm : ∀ u r, m u r ≤ 1)
    (us : List U) :
    l0 μ (fun u _ => m u) us = (μ.withDensity (prodMeaning m us))[|Set.univ] := by
  induction us with
  | nil =>
    rw [show prodMeaning m [] = 1 from funext (prodMeaning_nil m), withDensity_one, cond_univ]
    rfl
  | cons u us ih =>
    have hfin : μ.withDensity (prodMeaning m us) Set.univ ≠ ∞ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      calc ∫⁻ r, prodMeaning m us r ∂μ
          ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun r => prodMeaning_le_one hm us r
        _ = 1 := by simp
    simp only [l0, Kernel.ofDensity_apply]
    rw [ih, cond_univ_withDensity_mul _ (measurable_of_countable _) (measurable_of_countable _)
      hfin, show prodMeaning m us * m u = prodMeaning m (u :: us) from
        funext fun r => by simp [prodMeaning_cons, mul_comm]]

theorem l0_perm [IsProbabilityMeasure μ] (m : U → R → ℝ≥0∞) (hm : ∀ u r, m u r ≤ 1)
    {us us' : List U} (h : us.Perm us') :
    l0 μ (fun u _ => m u) us = l0 μ (fun u _ => m u) us' := by
  rw [l0_contextFree m hm, l0_contextFree m hm, funext (prodMeaning_perm (lex := m) h)]

theorem supp_uniformOn (S : Finset R) :
    supp (uniformOn (S : Set R)) = S := by
  ext r
  simp [mem_supp, uniformOn_eq_zero_iff S.finite_toSet, Set.inter_singleton_eq_empty]

theorem l0_indicator [DecidableEq R] (ext : U → Finset R → Finset R) (us : List U) :
    l0 (uniformOn Set.univ) (sharp ext) us = uniformOn (extSeq ext us : Set R) := by
  induction us with
  | nil => simp [l0, extSeq]
  | cons u us ih =>
    have h := (listener_truthful_eq_ofDensity (uniformOn (extSeq ext us : Set R))
      fun u' ↦ ((ext u' (extSeq ext us) : Set R))).symm
    simp only [l0, sharp]
    rw [ih, supp_uniformOn, h, listener_truthful_apply, extSeq, Finset.coe_inter, uniformOn,
      uniformOn, cond_cond_eq_cond_inter' .of_discrete .of_discrete
        (by rw [Measure.count_apply_finite _ (Finset.finite_toSet _)]
            exact ENNReal.natCast_ne_top _)]

theorem l0_single_lt_iff [DecidableEq R] (ext : U → Finset R → Finset R)
    (ha : r ∈ ext a Finset.univ)
    (hb : r ∈ ext b Finset.univ) :
    l0 (uniformOn Set.univ) (sharp ext) [a] {r} < l0 (uniformOn Set.univ) (sharp ext) [b] {r} ↔
      (ext b Finset.univ).card < (ext a Finset.univ).card := by
  simp [l0_indicator, extSeq, uniformOn_finset_apply_singleton, ha, hb, ENNReal.inv_lt_inv]

/-! ### The speaker kernels (rows 3–6) -/

variable (μ sem)

/-- The incremental sequence speaker of rows (4)–(5) chooses among sequences of length `n`. -/
noncomputable def seqSpeaker (β : ℝ) (cost : ℕ → ℝ≥0∞) (pLang : List U → U → ℝ≥0∞) (n : ℕ) :
    Kernel R (Fin n → U) :=
  Kernel.ofWeights fun r v => seqWeight μ sem β cost pLang r (List.ofFn v)

/-- The global speaker of row (3) chooses among sequences of length `n` with utterance
prior `P`. -/
noncomputable def globalSpeaker (β : ℝ) (cost : ℕ → ℝ≥0∞) {n : ℕ} (P : (Fin n → U) → ℝ≥0∞) :
    Kernel R (Fin n → U) :=
  Kernel.ofWeights fun r v => utility μ sem β cost (List.ofFn v) r * P v

/-- The incremental utterance speaker of row (6) is a softmax at rationality `α` over the
sequence speaker with utterance prior `P`. -/
noncomputable def uttSpeaker (β : ℝ) (cost : ℕ → ℝ≥0∞) (pLang : List U → U → ℝ≥0∞) (α : ℝ)
    {n : ℕ} (P : (Fin n → U) → ℝ≥0∞) : Kernel R (Fin n → U) :=
  Kernel.ofWeights fun r v => seqWeight μ sem β cost pLang r (List.ofFn v) ^ α * P v

variable {μ sem}

theorem seqSpeaker_real_lt_iff [IsProbabilityMeasure μ] (hβ : 0 ≤ β) (hcost : ∀ n, cost n ≠ ∞)
    (hp : ∀ us u, pLang us u ≠ ∞) {n : ℕ}
    (h0 : ∃ v : Fin n → U, seqWeight μ sem β cost pLang r (List.ofFn v) ≠ 0) {v v' : Fin n → U} :
    (seqSpeaker μ sem β cost pLang n r).real {v} <
        (seqSpeaker μ sem β cost pLang n r).real {v'} ↔
      seqWeight μ sem β cost pLang r (List.ofFn v) <
        seqWeight μ sem β cost pLang r (List.ofFn v') :=
  Kernel.ofWeights_real_singleton_lt_iff r
    (fun h => let ⟨v₀, hv₀⟩ := h0; hv₀ (Finset.sum_eq_zero_iff.mp h v₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.prod_ne_top fun _ _ =>
      ENNReal.mul_ne_top (utility_ne_top hβ hcost _) (hp _ _))

-- (3)
theorem globalSpeaker_apply_singleton_eq {n : ℕ} {P : (Fin n → U) → ℝ≥0∞} {v v' : Fin n → U}
    (hl : l0 μ sem (List.ofFn v) = l0 μ sem (List.ofFn v')) (hP : P v = P v') :
    globalSpeaker μ sem β cost P r {v} = globalSpeaker μ sem β cost P r {v'} := by
  simp only [globalSpeaker, Kernel.ofWeights_apply_singleton, utility, hl, hP, List.length_ofFn]

-- (6)
theorem uttSpeaker_real_lt_iff [IsProbabilityMeasure μ] (hβ : 0 ≤ β) (hcost : ∀ n, cost n ≠ ∞)
    (hp : ∀ us u, pLang us u ≠ ∞) {α : ℝ} (hα : 0 ≤ α) {n : ℕ} {P : (Fin n → U) → ℝ≥0∞}
    (hP : ∀ v, P v ≠ ∞)
    (h0 : ∃ v : Fin n → U, seqWeight μ sem β cost pLang r (List.ofFn v) ^ α * P v ≠ 0)
    {v v' : Fin n → U} :
    (uttSpeaker μ sem β cost pLang α P r).real {v} <
        (uttSpeaker μ sem β cost pLang α P r).real {v'} ↔
      seqWeight μ sem β cost pLang r (List.ofFn v) ^ α * P v <
        seqWeight μ sem β cost pLang r (List.ofFn v') ^ α * P v' :=
  Kernel.ofWeights_real_singleton_lt_iff r
    (fun h => let ⟨v₀, hv₀⟩ := h0; hv₀ (Finset.sum_eq_zero_iff.mp h v₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun v _ => ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hα (ENNReal.prod_ne_top fun _ _ =>
        ENNReal.mul_ne_top (utility_ne_top hβ hcost _) (hp _ _))) (hP v))

/-- At a uniform prior, sharp context-independent meanings and the paper's language model, the
sequence speaker prefers first the adjective true of fewer referents, the relevance effect. -/
theorem seqSpeaker_real_lt_of_card_lt [DecidableEq U] [DecidableEq R] (hβ : 0 < β)
    (hcost0 : ∀ n, cost n ≠ 0)
    (hcost : ∀ n, cost n ≠ ∞) (ext : U → Finset R) (ha : r ∈ ext a) (hb : r ∈ ext b)
    (hcard : (ext a).card < (ext b).card) :
    (seqSpeaker (uniformOn Set.univ) (sharp fun u _ => ext u) β cost (alternation a b) 2 r).real
        {![b, a]} <
      (seqSpeaker (uniformOn Set.univ) (sharp fun u _ => ext u) β cost (alternation a b) 2 r).real
        {![a, b]} := by
  have : Nonempty R := ⟨r⟩
  have hl0 : ∀ us, r ∈ extSeq (fun u _ => ext u) us →
      l0 (uniformOn Set.univ) (sharp fun u _ => ext u) us {r} ≠ 0 := fun us hus => by
    rw [l0_indicator, uniformOn_finset_apply_singleton, ite_eq_left hus]
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have hu : ∀ us, r ∈ extSeq (fun u _ => ext u) us →
      utility (uniformOn Set.univ) (sharp fun u _ => ext u) β cost us r ≠ 0 := fun us hus =>
    mul_ne_zero ((ENNReal.rpow_eq_zero_iff_of_pos hβ).not.2 (hl0 us hus)) (hcost0 _)
  have hl : l0 (uniformOn Set.univ) (sharp fun u _ => ext u) [b, a] =
      l0 (uniformOn Set.univ) (sharp fun u _ => ext u) [a, b] :=
    l0_perm (m := fun u ↦ ((ext u : Set R)).indicator 1)
      (sharp_apply_le_one (fun u _ ↦ ext u) · ∅)
      (List.Perm.swap a b [])
  rw [seqSpeaker_real_lt_iff hβ.le hcost (fun _ _ => alternation_ne_top _ _)
    ⟨![a, b], by
      rw [ofFn_pair, seqWeight_pair_alternation]
      exact mul_ne_zero (by simp) (mul_ne_zero (hu _ (by simp [extSeq, ha]))
        (hu _ (by simp [extSeq, ha, hb])))⟩,
    ofFn_pair, ofFn_pair, alternation_comm,
    seqWeight_pair_lt_iff_of_l0_eq hβ.le hcost hl (hu _ (by simp [extSeq, ha, hb])),
    utility_single_lt_iff hβ (hcost0 1) (hcost 1), l0_single_lt_iff (fun u _ => ext u) hb ha]
  exact hcard


end

/-! ### The k%-semantics (3a) distinguishes the orders -/

/-- Under the k%-semantics (3a) of a dimension adjective against the comparison class `C`, an
object is big when its size exceeds the maximum of `C` less `k`% of the range of `C`. -/
def kPercent [Fintype R] (k : ℕ) (size : R → ℕ) (C : Finset R) : Finset R :=
  Finset.univ.filter fun x =>
    ∃ hC : C.Nonempty, 100 * C.sup' hC size < 100 * size x + k * (C.sup' hC size - C.inf' hC size)

/-- The display has three blue stickers of sizes 6, 5 and 1, and a green one of size 10. -/
inductive Sticker
  | blue6
  | blue5
  | blue1
  | green10
  deriving DecidableEq, Fintype

instance : MeasurableSpace Sticker := ⊤
instance : DiscreteMeasurableSpace Sticker := ⟨fun _ => trivial⟩

/-- A sticker's size. -/
def Sticker.size : Sticker → ℕ
  | .blue6 => 6
  | .blue5 => 5
  | .blue1 => 1
  | .green10 => 10

/-- The two adjectives of the paper's stimuli. -/
inductive Adj
  | big
  | blue
  deriving DecidableEq, Fintype

instance : MeasurableSpace Adj := ⊤
instance : DiscreteMeasurableSpace Adj := ⟨fun _ => trivial⟩

/-- *big* by the 50%-semantics of the paper's simulations, and *blue* sharply. -/
def Adj.ext : Adj → Finset Sticker → Finset Sticker
  | .big, C => kPercent 50 Sticker.size C
  | .blue, _ => {.blue6, .blue5, .blue1}

theorem l0_big_blue_ne :
    l0 (uniformOn Set.univ) (sharp Adj.ext) [.big, .blue] ≠
      l0 (uniformOn Set.univ) (sharp Adj.ext) [.blue, .big] := by
  rw [l0_indicator, l0_indicator, show extSeq Adj.ext [.big, .blue] = {.blue6, .blue5} by decide,
    show extSeq Adj.ext [.blue, .big] = {.blue6} by decide]
  intro h
  have := congrArg (· {Sticker.blue5}) h
  rw [uniformOn_finset_apply_singleton, uniformOn_finset_apply_singleton] at this
  simp at this

end SchlotterbeckWang2023
