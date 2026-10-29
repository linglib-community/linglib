module

public import Linglib.Pragmatics.RSA.LexicalUncertainty
public import Linglib.Pragmatics.Bidirectional
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Bergen, Levy and Goodman (2016): Pragmatic reasoning through semantic inference

An M-implicature pairs the costlier of two synonymous utterances with the less probable meaning:
*John has the ability to finish the homework* suggests he will not. In the Horn game a cheap and
a costly utterance are both true of a frequent and a rare meaning. The Rational Speech Act model
cannot pair them with meanings: [two utterances its literal listener reads alike are read alike
at every level of the recursion](##step_iterate_short_eq_long), whatever their costs. Under
lexical uncertainty the speaker uses one of the lexica that refine each utterance's meaning, and
the listener, unsure which, inverts the speaker of each. [She then finds the rare meaning
likelier after the costly utterance than after the cheap one](##L1_fst_rare_lt), and so
associates each form with the meaning of its markedness, [the pairs weak bidirection takes to be
super-optimal](##setOf_associates_eq_superoptimalSet).

## Implementation notes

The lexica are the nine pairs of refinements of the cheap and the costly utterance, each a
nonempty set of meanings, under a uniform prior; every lexicon keeps the null utterance true of
both meanings, so the speaker can always speak. The speaker knows the meaning, the simplification
of the paper's Section 4.4. The paper simulates the M-implicature at one setting (Figure 6) and
calls it robust for every rationality above one; here it holds at every positive rationality,
every prior favouring the frequent meaning and every cost of the null utterance. The implicature
is stated across utterances, as the rare meaning's probability after the costly utterance against
its probability after the cheap one, not as the rare meaning's being the likelier one after the
costly utterance. The proof reduces the listener to the speakers' productions summed over the
lexica and shows that the ratio of the costly to the cheap utterance's production falls as the
meaning's prior rises.

## TODO

* The lexica the paper credits with the effect (p. 20:33), those refining exactly one utterance,
  do not carry it alone: with only them and the semantic lexicon the inequality reverses at a
  rationality near 0.12 and a prior near 0.62 for the frequent meaning, numerically. A theorem
  should state this.
* Numerically the ratio also falls with the prior for more meanings and, between the cheapest and
  the costliest, for more synonyms; neither is proved.
* The ignorance implicature (Section 4.6) and compositional lexical uncertainty (Section 5).

## References

* [bergen-levy-goodman-2016]
* [horn-1984]
* [blutner-2000]
-/

@[expose] public section

namespace BergenLevyGoodman2016

open MeasureTheory ProbabilityTheory RSA

/-! ### The Horn game -/

/-- The frequent and the rare meaning. -/
inductive Meaning where
  | freq
  | rare
  deriving DecidableEq, Fintype

instance : MeasurableSpace Meaning := ⊤
instance : DiscreteMeasurableSpace Meaning := ⟨fun _ ↦ trivial⟩

/-- The cheap and the costly utterance, and the null utterance, true of both meanings. -/
inductive Utterance where
  | short
  | long
  | null
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- A refinement of an utterance true of both meanings keeps both or one of them. -/
inductive Refinement where
  | both
  | freq
  | rare
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Refinement := ⊤
instance : DiscreteMeasurableSpace Refinement := ⟨fun _ ↦ trivial⟩

/-- The meanings a refinement keeps. -/
def Refinement.den : Refinement → Set Meaning
  | .both => Set.univ
  | .freq => {.freq}
  | .rare => {.rare}

theorem Refinement.den_injective : Function.Injective Refinement.den := by
  intro a b h
  have hf := Set.ext_iff.1 h .freq
  have hr := Set.ext_iff.1 h .rare
  cases a <;> cases b <;> simp [den] at hf hr ⊢

theorem Refinement.range_den : Set.range Refinement.den = {D | D.Nonempty} := by
  ext D
  refine ⟨?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · rintro ⟨r, rfl⟩
    cases r
    exacts [⟨.freq, trivial⟩, ⟨.freq, rfl⟩, ⟨.rare, rfl⟩]
  by_cases hf : Meaning.freq ∈ D <;> by_cases hr : Meaning.rare ∈ D
  · exact ⟨.both, Set.ext fun m ↦ by cases m <;> simp [den, hf, hr]⟩
  · exact ⟨.freq, Set.ext fun m ↦ by cases m <;> simp [den, hf, hr]⟩
  · exact ⟨.rare, Set.ext fun m ↦ by cases m <;> simp [den, hf, hr]⟩
  · cases m <;> contradiction

/-- A lexicon refines the meanings of the cheap and of the costly utterance. -/
abbrev Lexicon := Refinement × Refinement

/-- The meanings of the utterances in a lexicon. -/
def sem (ℒ : Lexicon) : Utterance → Set Meaning
  | .short => ℒ.1.den
  | .long => ℒ.2.den
  | .null => Set.univ

/-- The semantic lexicon, in which both utterances are true of both meanings. -/
def base : Lexicon := (.both, .both)

variable (α : ℝ) (C : Utterance → ℝ) (μ : Measure Meaning)

/-- The literal listener (26) conditions the prior on the meaning of the utterance in a
lexicon. -/
noncomputable def L0 (ℒ : Lexicon) : Kernel Utterance Meaning := listener μ (truthful (sem ℒ))

instance (ℒ : Lexicon) : IsFiniteKernel (L0 μ ℒ) := inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The speaker (27)–(28) knows the meaning and addresses the literal listener of her lexicon. -/
noncomputable def S1 (ℒ : Lexicon) : Kernel Meaning Utterance :=
  speaker α C (L0 μ ℒ) Measure.dirac

instance (ℒ : Lexicon) : IsFiniteKernel (S1 α C μ ℒ) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-- The listener under lexical uncertainty (29) inverts the speaker of each lexicon, against the
prior over meanings and a uniform prior over the lexica. -/
noncomputable def L1 : Kernel Utterance (Meaning × Lexicon) :=
  listener (μ.prod (uniformOn Set.univ)) fun p ↦ S1 α C μ p.2 p.1

/-- A round of the recursion without lexical uncertainty (6)–(7): the listener of the speaker
who addresses `L`. -/
noncomputable def step (L : Kernel Utterance Meaning) : Kernel Utterance Meaning :=
  listener μ (speaker α C L Measure.dirac)

/-! ### Without lexical uncertainty -/

/-- **Lemma 2.** Without lexical uncertainty the cheap and the costly utterance are interpreted
alike at every level of the recursion, whatever their costs, the rationality and the prior. -/
theorem step_iterate_short_eq_long (n : ℕ) :
    (step α C μ)^[n] (L0 μ base) .short = (step α C μ)^[n] (L0 μ base) .long := by
  induction n with
  | zero =>
    refine (listener_apply_eq_of_apply_singleton_eq_mul one_ne_zero ENNReal.one_ne_top
      fun w ↦ ?_).symm
    simp [truthful_apply_singleton, sem, base, Refinement.den]
  | succ n ih =>
    rw [Function.iterate_succ_apply', step]
    exact (listener_speaker_apply_congr μ ih).symm

/-! ### Under lexical uncertainty -/

/-- The probability that the speaker produces an utterance at a meaning, summed over the
lexica. -/
noncomputable def production (w : Meaning) (u : Utterance) : ℝ :=
  ∑ ℒ : Lexicon, (S1 α C μ ℒ w).real {u}

-- (29)
theorem L1_fst_real_singleton [IsFiniteMeasure μ] (u : Utterance) (w : Meaning) :
    (L1 α C μ u).fst.real {w} =
      μ.real {w} * production α C μ w u / ∑ m, μ.real {m} * production α C μ m u := by
  have hν (ℒ : Lexicon) : (uniformOn (Set.univ : Set Lexicon)).real {ℒ} =
      (Fintype.card Lexicon : ℝ)⁻¹ := uniformOn_univ_real_singleton ℒ
  have hc : (Fintype.card Lexicon : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hden : ∑ p : Meaning × Lexicon, (μ.prod (uniformOn Set.univ)).real {p} *
      (S1 α C μ p.2 p.1).real {u} =
        (Fintype.card Lexicon : ℝ)⁻¹ * ∑ m, μ.real {m} * production α C μ m u := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    simp only [Measure.prod_real_singleton, hν, production, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [L1, listener_prod_fst_real_singleton, hden]
  simp only [hν, ← Finset.mul_sum, production]
  rw [mul_left_comm, mul_div_mul_left _ _ hc]

/-- The weight the speaker at `w` gives an utterance meaning `D`: the literal listener's
probability of `w`, to the power of the rationality. -/
noncomputable def weight (w : Meaning) (D : Set Meaning) : ℝ :=
  D.indicator (fun _ ↦ (μ.real {w} / μ.real D) ^ α) w

private theorem toReal_L0_rpow (hα : 0 < α) [IsFiniteMeasure μ] (ℒ : Lexicon) (u : Utterance)
    (w : Meaning) : (L0 μ ℒ u {w} ^ α).toReal = weight α μ w (sem ℒ u) := by
  by_cases h : w ∈ sem ℒ u
  · rw [L0, listener_truthful_apply_singleton μ _ h, weight, Set.indicator_of_mem h,
      ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul,
      measureReal_def, measureReal_def]
  · rw [L0, listener_truthful_apply_singleton_of_notMem μ _ h, ENNReal.zero_rpow_of_pos hα,
      weight, Set.indicator_of_notMem h, ENNReal.toReal_zero]

theorem S1_real_singleton (hα : 0 < α) [IsFiniteMeasure μ] (ℒ : Lexicon) (w : Meaning)
    (u : Utterance) :
    (S1 α C μ ℒ w).real {u} = weight α μ w (sem ℒ u) * Real.exp (-(α * C u)) /
      ∑ u', weight α μ w (sem ℒ u') * Real.exp (-(α * C u')) := by
  rw [S1, speaker_dirac_real_singleton hα.le]
  simp only [toReal_L0_rpow α μ hα]

theorem weight_univ (w : Meaning) :
    weight α μ w Set.univ = (μ.real {w} / μ.real Set.univ) ^ α :=
  Set.indicator_of_mem (Set.mem_univ w) _

theorem weight_singleton_self [IsFiniteMeasure μ] {w : Meaning} (hw : μ {w} ≠ 0) :
    weight α μ w {w} = 1 := by
  rw [weight, Set.indicator_of_mem (Set.mem_singleton w),
    div_self (show μ.real {w} ≠ 0 from (ENNReal.toReal_pos hw (measure_ne_top _ _)).ne'),
    Real.one_rpow]

theorem weight_singleton_of_ne {w w' : Meaning} (h : w ≠ w') : weight α μ w {w'} = 0 :=
  Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 h) _

private theorem sum_utterance (f : Utterance → ℝ) : ∑ u, f u = f .short + f .long + f .null := by
  rw [show (Finset.univ : Finset Utterance) = {.short, .long, .null} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem production_short (hα : 0 < α) [IsFiniteMeasure μ] (w : Meaning) :
    production α C μ w .short = ∑ ℒ : Lexicon,
      weight α μ w ℒ.1.den * Real.exp (-(α * C .short)) /
        (weight α μ w ℒ.1.den * Real.exp (-(α * C .short)) +
          weight α μ w ℒ.2.den * Real.exp (-(α * C .long)) +
            weight α μ w Set.univ * Real.exp (-(α * C .null))) := by
  simp only [production, S1_real_singleton α C μ hα, sum_utterance]
  rfl

theorem production_long (hα : 0 < α) [IsFiniteMeasure μ] (w : Meaning) :
    production α C μ w .long = ∑ ℒ : Lexicon,
      weight α μ w ℒ.2.den * Real.exp (-(α * C .long)) /
        (weight α μ w ℒ.1.den * Real.exp (-(α * C .short)) +
          weight α μ w ℒ.2.den * Real.exp (-(α * C .long)) +
            weight α μ w Set.univ * Real.exp (-(α * C .null))) := by
  simp only [production, S1_real_singleton α C μ hα, sum_utterance]
  rfl

private theorem sum_meaning (f : Meaning → ℝ) : ∑ m, f m = f .freq + f .rare :=
  Fintype.sum_eq_add Meaning.freq Meaning.rare (by decide) fun m hm ↦ by cases m <;> simp at hm

theorem production_pos (hα : 0 < α) [IsFiniteMeasure μ] {w : Meaning} (hw : μ {w} ≠ 0)
    (u : Utterance) : 0 < production α C μ w u :=
  Finset.sum_pos' (fun _ _ ↦ measureReal_nonneg) ⟨base, Finset.mem_univ _, ENNReal.toReal_pos
    ((speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff hα C μ _ _ _).2
      ⟨by cases u <;> exact Set.mem_univ w, hw⟩) (measure_ne_top _ _)⟩

theorem L1_fst_rare_lt_iff (hα : 0 < α) [IsFiniteMeasure μ] (hf : μ {.freq} ≠ 0)
    (hr : μ {.rare} ≠ 0) :
    (L1 α C μ .short).fst.real {.rare} < (L1 α C μ .long).fst.real {.rare} ↔
      production α C μ .rare .short * production α C μ .freq .long <
        production α C μ .rare .long * production α C μ .freq .short := by
  have hf' : 0 < μ.real {.freq} := ENNReal.toReal_pos hf (measure_ne_top _ _)
  have hr' : 0 < μ.real {.rare} := ENNReal.toReal_pos hr (measure_ne_top _ _)
  have hfS := production_pos α C μ hα hf .short
  have hfL := production_pos α C μ hα hf .long
  have hrS := production_pos α C μ hα hr .short
  have hrL := production_pos α C μ hα hr .long
  rw [L1_fst_real_singleton, L1_fst_real_singleton, sum_meaning, sum_meaning,
    div_lt_div_iff₀ (by nlinarith) (by nlinarith), ← sub_pos, ← sub_pos (b := _ * _)]
  constructor <;> intro h
  · have h' : 0 < μ.real {.rare} * μ.real {.freq} *
        (production α C μ .rare .long * production α C μ .freq .short -
          production α C μ .rare .short * production α C μ .freq .long) := by linarith
    exact (pos_iff_pos_of_mul_pos h').1 (mul_pos hr' hf')
  · nlinarith [mul_pos hr' hf']

/-! ### The inequality

Write `s`, `l` and `m` for the cost weights `exp (-(α * C u))` of the cheap, the costly and the null
utterance, and `t` for the weight `(μ {w} / μ univ) ^ α` that the speaker at `w` gives the
unrefined meaning against her own. Her production of the cheap utterance, summed over the lexica,
is `s * A s l m ε (t * m)` with `ε = (1 - t) ^ 2 / (2 * t * (s + l + m))`, and her production of the
costly one is `l * A l s m ε (t * m)`, the same with the two cost weights exchanged. The four
lexica that refine exactly one utterance to the speaker's meaning depend on `t` only through `ε`,
the others only through the null utterance's weight `t * m`. In `ε` the ratio of the two
productions is a Möbius map with positive determinant, so it rises; in `t * m` it falls along the
model's curve, by a bound on its derivative; and so it falls as `t` grows. -/

section Inequality

/-- The part of `A` that does not depend on `ε`. -/
private noncomputable def A₀ (s l m n : ℝ) : ℝ :=
  2 / (s + l + m) + (s + m)⁻¹ + (n + s + l)⁻¹ + (n + s)⁻¹

/-- The cheap utterance's production at a meaning, summed over the lexica and divided by its cost
weight, in terms of `ε` and the null utterance's weight `n`. -/
private noncomputable def A (s l m ε n : ℝ) : ℝ :=
  A₀ s l m n + (1 + 2 * l * (l + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹

private theorem mobius_lt {a b c d x y : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hdet : a * d < b * c)
    (hx : 0 ≤ x) (hxy : x < y) : (a + x * b) / (c + x * d) < (a + y * b) / (c + y * d) := by
  rw [div_lt_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_pos (sub_pos.2 hdet) (sub_pos.2 hxy)]

variable {s l m : ℝ}

private theorem A_eq (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {ε n : ℝ} (hε : 0 ≤ ε) (hn : 0 < n) :
    A s l m ε n = (A₀ s l m n * (n + s + l) + 1 +
      ε * (2 * s * l * A₀ s l m n + 2 * l * (l + m) / (s + l + m))) /
        (n + s + l + 2 * s * l * ε) := by
  have h1 : (n + s + l + 2 * s * l * ε) ≠ 0 := by positivity
  rw [eq_div_iff h1, A]
  field_simp
  ring

private theorem ratio_eq (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {ε n : ℝ} (hε : 0 ≤ ε)
    (hn : 0 < n) :
    A l s m ε n / A s l m ε n =
      (A₀ l s m n * (n + s + l) + 1 +
          ε * (2 * s * l * A₀ l s m n + 2 * s * (s + m) / (s + l + m))) /
        (A₀ s l m n * (n + s + l) + 1 +
          ε * (2 * s * l * A₀ s l m n + 2 * l * (l + m) / (s + l + m))) := by
  rw [A_eq hs hl hm hε hn, A_eq hl hs hm hε hn]
  have h1 : (n + s + l + 2 * s * l * ε) ≠ 0 := by positivity
  have h2 : (n + l + s + 2 * l * s * ε) = n + s + l + 2 * s * l * ε := by ring
  rw [h2, div_div_div_cancel_right₀ h1]
  congr 1
  ring

private theorem A₀_pos (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {n : ℝ} (hn : 0 < n) :
    0 < A₀ s l m n := by
  unfold A₀
  positivity

private theorem A₀_swap_sub (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {n : ℝ} (hn : 0 < n) :
    A₀ l s m n - A₀ s l m n = (s - l) * ((l + m)⁻¹ * (s + m)⁻¹ + (n + l)⁻¹ * (n + s)⁻¹) := by
  unfold A₀
  field_simp
  ring

private theorem key_le (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {n : ℝ} (hn : 0 < n) :
    l * ((l + m)⁻¹ * (s + m)⁻¹ + (n + l)⁻¹ * (n + s)⁻¹) * (n * (l + m) + l * m) ≤
      (s + l + m) * (n + s + l) * A₀ s l m n := by
  have hK : n * (l + m) + l * m ≤ (l + m) * (n + l) := by nlinarith
  have hK₁ : l * (n * (l + m) + l * m) ≤ (s + l + m) * (n + s + l) * (l + m) := by
    have : l * (n + l) ≤ (s + l + m) * (n + s + l) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hK hl.le, mul_le_mul_of_nonneg_left this
      (show 0 ≤ l + m by positivity)]
  have hK₂ : l * (n * (l + m) + l * m) ≤ (s + l + m) * (n + s + l) * (n + l) := by
    have : l * (l + m) ≤ (s + l + m) * (n + s + l) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hK hl.le, mul_le_mul_of_nonneg_left this
      (show 0 ≤ n + l by positivity)]
  have hX : (s + m)⁻¹ + (n + s)⁻¹ ≤ A₀ s l m n := by
    unfold A₀
    have : 0 < (n + s + l)⁻¹ := by positivity
    have : 0 < 2 / (s + l + m) := by positivity
    linarith
  calc l * ((l + m)⁻¹ * (s + m)⁻¹ + (n + l)⁻¹ * (n + s)⁻¹) * (n * (l + m) + l * m)
      = (s + m)⁻¹ * (l * (n * (l + m) + l * m) / (l + m)) +
          (n + s)⁻¹ * (l * (n * (l + m) + l * m) / (n + l)) := by field_simp
    _ ≤ (s + m)⁻¹ * ((s + l + m) * (n + s + l)) + (n + s)⁻¹ * ((s + l + m) * (n + s + l)) := by
        gcongr
        · rw [div_le_iff₀ (by positivity)]; exact hK₁
        · rw [div_le_iff₀ (by positivity)]; exact hK₂
    _ = (s + l + m) * (n + s + l) * ((s + m)⁻¹ + (n + s)⁻¹) := by ring
    _ ≤ (s + l + m) * (n + s + l) * A₀ s l m n := by gcongr

private theorem ratio_lt_of_lt (hl : 0 < l) (hls : l < s) (hm : 0 < m) {n ε₁ ε₂ : ℝ} (hn : 0 < n)
    (h₁ : 0 ≤ ε₁) (h₁₂ : ε₁ < ε₂) :
    A l s m ε₁ n / A s l m ε₁ n < A l s m ε₂ n / A s l m ε₂ n := by
  have hs : 0 < s := hl.trans hls
  rw [ratio_eq hs hl hm h₁ hn, ratio_eq hs hl hm (h₁.trans h₁₂.le) hn]
  have hX := A₀_pos hs hl hm hn
  have hY := A₀_pos hl hs hm hn
  have hsub := A₀_swap_sub hs hl hm hn
  have hkey := key_le hs hl hm hn
  refine mobius_lt (by positivity) (by positivity) ?_ h₁ h₁₂
  set Δ := (l + m)⁻¹ * (s + m)⁻¹ + (n + l)⁻¹ * (n + s)⁻¹
  have hΔ : 0 ≤ Δ := by positivity
  have hY' : A₀ l s m n = A₀ s l m n + (s - l) * Δ := by linarith
  rw [hY', ← sub_pos]
  have hc : 0 < s + l + m := by positivity
  have hdet : (2 * s * l * (A₀ s l m n + (s - l) * Δ) + 2 * s * (s + m) / (s + l + m)) *
      (A₀ s l m n * (n + s + l) + 1) -
      ((A₀ s l m n + (s - l) * Δ) * (n + s + l) + 1) *
        (2 * s * l * A₀ s l m n + 2 * l * (l + m) / (s + l + m)) =
      2 * (s - l) / (s + l + m) * ((s + l + m) * (A₀ s l m n * (n + s + l) + 1) +
        l * Δ * (s ^ 2 - l ^ 2) - l * Δ * (n * (l + m) + l * m)) := by
    field_simp
    ring
  rw [hdet]
  have : 0 ≤ l * Δ * (s ^ 2 - l ^ 2) := by
    have : 0 ≤ s ^ 2 - l ^ 2 := by nlinarith
    positivity
  have : 0 < 2 * (s - l) / (s + l + m) := div_pos (by linarith) hc
  have : 0 < (s + l + m) * (A₀ s l m n * (n + s + l) + 1) + l * Δ * (s ^ 2 - l ^ 2) -
      l * Δ * (n * (l + m) + l * m) := by nlinarith
  positivity

/-- Minus the derivative of `A s l m ε` in the weight of the null utterance. -/
private noncomputable def negDerivA (s l m ε n : ℝ) : ℝ :=
  (n + s + l)⁻¹ ^ 2 + (n + s)⁻¹ ^ 2 +
    (1 + 2 * l * (l + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹ ^ 2

private theorem A_swap (s l m ε n : ℝ) :
    A l s m ε n = 2 / (s + l + m) + (l + m)⁻¹ + (n + s + l)⁻¹ + (n + l)⁻¹ +
      (1 + 2 * s * (s + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹ := by
  unfold A A₀
  ring

private theorem negDerivA_swap (s l m ε n : ℝ) :
    negDerivA l s m ε n = (n + s + l)⁻¹ ^ 2 + (n + l)⁻¹ ^ 2 +
      (1 + 2 * s * (s + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹ ^ 2 := by
  unfold negDerivA
  ring

private theorem hasDerivAt_A (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {ε n : ℝ} (hε : 0 ≤ ε)
    (hn : 0 < n) :
    HasDerivAt (fun n ↦ A s l m ε n) (-negDerivA s l m ε n) n := by
  have h₁ := ((hasDerivAt_id' n).add_const s |>.add_const l).fun_inv (by positivity)
  have h₂ := ((hasDerivAt_id' n).add_const s).fun_inv (by positivity)
  have h₃ := (((hasDerivAt_id' n).add_const s |>.add_const l).add_const
    (2 * s * l * ε)).fun_inv (by positivity)
  have := (((hasDerivAt_const n (2 / (s + l + m) + (s + m)⁻¹)).add h₁).add h₂).add
    (h₃.const_mul (1 + 2 * l * (l + m) * ε / (s + l + m)))
  convert this using 1
  · ext x
    simp only [A, A₀, Pi.add_apply]
  · simp only [negDerivA]
    field_simp
    ring

private theorem refined_le (hs : 0 < s) (hl : 0 < l) (hm : 0 < m) {ε n : ℝ} (hε : 0 ≤ ε)
    (hn : 0 < n) (hεn : 2 * n * (s + l + m) * ε ≤ m) :
    (1 + 2 * l * (l + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹ ^ 2 ≤
      (n + s + l)⁻¹ * (n + s)⁻¹ := by
  have hc : 0 < s + l + m := by positivity
  have h1 : 2 * (l + m) * ε * n ≤ s + l + m := by nlinarith
  have h2 : 2 * (l + m) * ε * s ≤ 4 * (s + l + m) * s * ε := by
    nlinarith [mul_nonneg (mul_nonneg hs.le hε) (show 0 ≤ 2 * s + l + m by positivity)]
  have key : (s + l + m + 2 * l * (l + m) * ε) * ((n + s + l) * (n + s)) ≤
      (s + l + m) * (n + s + l + 2 * s * l * ε) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hl.le (show 0 ≤ n + s + l by positivity))
      (show 0 ≤ s + l + m + 4 * (s + l + m) * s * ε - 2 * (l + m) * ε * (n + s) by nlinarith),
      mul_nonneg (mul_nonneg hc.le (sq_nonneg (s * l))) (sq_nonneg ε)]
  rw [show (1 + 2 * l * (l + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹ ^ 2 =
      (s + l + m + 2 * l * (l + m) * ε) / ((s + l + m) * (n + s + l + 2 * s * l * ε) ^ 2) by
        field_simp,
    show (n + s + l)⁻¹ * (n + s)⁻¹ = 1 / ((n + s + l) * (n + s)) by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [key]

private theorem swap_le (hl : 0 < l) (hls : l < s) (hm : 0 < m) {n : ℝ} (hn : 0 < n) (hnm : n ≤ m) :
    ((l + m)⁻¹ * (s + m)⁻¹ + (n + l)⁻¹ * (n + s)⁻¹) *
        ((n + s + l)⁻¹ ^ 2 + (n + s + l)⁻¹ * (n + s)⁻¹ + (n + s)⁻¹ ^ 2) ≤
      (1 / (s + l + m) + (s + m)⁻¹ + (n + s + l)⁻¹ + (n + s)⁻¹) *
        ((n + s)⁻¹ * (n + l)⁻¹ * ((n + s)⁻¹ + (n + l)⁻¹)) := by
  obtain ⟨E, hE, rfl⟩ : ∃ E, 0 < E ∧ s = l + E := ⟨s - l, by linarith, by ring⟩
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ m = n + d := ⟨m - n, by linarith, by ring⟩
  rw [← sub_nonneg]
  field_simp
  ring_nf
  positivity

private theorem refined_swap_le (hl : 0 < l) (hls : l < s) (hm : 0 < m) {ε n : ℝ} (hε : 0 ≤ ε)
    (hn : 0 < n) (hεn : 2 * n * (s + l + m) * ε ≤ m) :
    (l + n) * (1 / (s + l + m) + (1 + 2 * s * (s + m) * ε / (s + l + m)) *
      (n + s + l + 2 * s * l * ε)⁻¹) ≤ (s + n) * (1 / (s + l + m) +
        (1 + 2 * l * (l + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹) := by
  have hs : 0 < s := hl.trans hls
  have hc : 0 < s + l + m := by positivity
  have hL : 0 < n + s + l + 2 * s * l * ε := by positivity
  rw [← sub_nonneg]
  have : (s + n) * (1 / (s + l + m) + (1 + 2 * l * (l + m) * ε / (s + l + m)) *
      (n + s + l + 2 * s * l * ε)⁻¹) - (l + n) * (1 / (s + l + m) +
        (1 + 2 * s * (s + m) * ε / (s + l + m)) * (n + s + l + 2 * s * l * ε)⁻¹) =
      (s - l) * (n + s + l + 2 * s * l * ε)⁻¹ *
        (n + s + l + (s + l + m) - 2 * ε * n * (s + l + m)) / (s + l + m) := by
    field_simp
    ring
  rw [this]
  have : 0 ≤ n + s + l + (s + l + m) - 2 * ε * n * (s + l + m) := by nlinarith
  have : 0 ≤ s - l := by linarith
  positivity

private theorem rest_swap_le (hl : 0 < l) (hls : l < s) {n : ℝ} (hn : 0 < n) :
    (s + n) * ((n + s + l)⁻¹ ^ 2 + (n + s)⁻¹ ^ 2) ≤
      (l + n) * ((n + s + l)⁻¹ ^ 2 + (n + l)⁻¹ ^ 2) := by
  have hs : 0 < s := hl.trans hls
  rw [← sub_nonneg]
  have : (l + n) * ((n + s + l)⁻¹ ^ 2 + (n + l)⁻¹ ^ 2) -
      (s + n) * ((n + s + l)⁻¹ ^ 2 + (n + s)⁻¹ ^ 2) =
      (s - l) * ((n + s)⁻¹ * (n + l)⁻¹ - (n + s + l)⁻¹ ^ 2) := by
    field_simp
    ring
  rw [this]
  have h1 : (n + s + l)⁻¹ ≤ (n + s)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h2 : (n + s + l)⁻¹ ≤ (n + l)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h3 : (n + s + l)⁻¹ ^ 2 ≤ (n + s)⁻¹ * (n + l)⁻¹ := by
    rw [sq]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  exact mul_nonneg (by linarith) (sub_nonneg.2 h3)

private theorem negDerivA_combine {s l n c e gA gB a b γA γB lam : ℝ} (hls : l < s) (hc : 0 < c)
    (he : 0 < e) (hgA : 0 < gA) (hgB : 0 < gB) (ha : 0 < a) (hb : 0 < b) (hγA : 0 < γA)
    (hlam : 0 < lam) (hln : 0 < l + n)
    (q1 : gB ^ 2 - gA ^ 2 = (s - l) * (gA * gB * (gA + gB)))
    (q2 : (a - b) + (gB - gA) = (s - l) * (a * b + gB * gA))
    (q3 : γA * lam ^ 2 ≤ e * gA)
    (q4 : (a * b + gB * gA) * (e ^ 2 + e * gA + gA ^ 2) ≤
      (1 / c + b + e + gA) * (gA * gB * (gA + gB)))
    (q5 : γA ≤ γB)
    (q6 : (l + n) * (1 / c + γB * lam) ≤ (s + n) * (1 / c + γA * lam))
    (q7 : (s + n) * (e ^ 2 + gA ^ 2) ≤ (l + n) * (e ^ 2 + gB ^ 2)) :
    (2 / c + a + e + gB + γB * lam) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) ≤
      (2 / c + b + e + gA + γA * lam) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) := by
  have hsl : 0 ≤ s - l := by linarith
  have hY : 0 ≤ (a - b) + (gB - gA) := by rw [q2]; positivity
  have hT1 : 0 ≤ (1 / c + b + e + gA) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
      (1 / c + a + e + gB) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) := by
    have h2 : ((a - b) + (gB - gA)) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) ≤
        ((a - b) + (gB - gA)) * (e ^ 2 + e * gA + gA ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hY
    have h3 : ((a - b) + (gB - gA)) * (e ^ 2 + e * gA + gA ^ 2) ≤
        (1 / c + b + e + gA) * (gB ^ 2 - gA ^ 2) := by
      rw [q2, q1, mul_assoc, mul_left_comm (1 / c + b + e + gA)]
      exact mul_le_mul_of_nonneg_left q4 hsl
    have h4 : 0 ≤ (1 / c + b + e + gA) * lam ^ 2 * (γB - γA) :=
      mul_nonneg (by positivity) (sub_nonneg.2 q5)
    have : (1 / c + b + e + gA) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
        (1 / c + a + e + gB) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) =
        (1 / c + b + e + gA) * (gB ^ 2 - gA ^ 2) + (1 / c + b + e + gA) * lam ^ 2 * (γB - γA) -
          ((a - b) + (gB - gA)) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) := by ring
    linarith
  have hT2 : 0 ≤ (1 / c + γA * lam) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
      (1 / c + γB * lam) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) := by
    have k1 := mul_le_mul_of_nonneg_left q7 (show 0 ≤ 1 / c + γA * lam by positivity)
    have k2 := mul_le_mul_of_nonneg_right q6 (show 0 ≤ e ^ 2 + gA ^ 2 by positivity)
    have h2 : 0 ≤ (1 / c + γA * lam) * (e ^ 2 + gB ^ 2) -
        (1 / c + γB * lam) * (e ^ 2 + gA ^ 2) := by
      refine nonneg_of_mul_nonneg_right ?_ hln
      have : (l + n) * ((1 / c + γA * lam) * (e ^ 2 + gB ^ 2) -
          (1 / c + γB * lam) * (e ^ 2 + gA ^ 2)) =
          (1 / c + γA * lam) * ((l + n) * (e ^ 2 + gB ^ 2)) -
            (l + n) * (1 / c + γB * lam) * (e ^ 2 + gA ^ 2) := by ring
      have : (1 / c + γA * lam) * ((s + n) * (e ^ 2 + gA ^ 2)) =
          (s + n) * (1 / c + γA * lam) * (e ^ 2 + gA ^ 2) := by ring
      linarith
    have h3 : 0 ≤ lam ^ 2 * (γB - γA) * (1 / c) :=
      mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.2 q5)) (by positivity)
    have : (1 / c + γA * lam) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
        (1 / c + γB * lam) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) =
        ((1 / c + γA * lam) * (e ^ 2 + gB ^ 2) - (1 / c + γB * lam) * (e ^ 2 + gA ^ 2)) +
          lam ^ 2 * (γB - γA) * (1 / c) := by ring
    linarith
  have : (2 / c + b + e + gA + γA * lam) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
      (2 / c + a + e + gB + γB * lam) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2) =
      ((1 / c + b + e + gA) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
        (1 / c + a + e + gB) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2)) +
      ((1 / c + γA * lam) * (e ^ 2 + gB ^ 2 + γB * lam ^ 2) -
        (1 / c + γB * lam) * (e ^ 2 + gA ^ 2 + γA * lam ^ 2)) := by ring
  linarith

private theorem A_mul_negDerivA_le (hl : 0 < l) (hls : l < s) (hm : 0 < m) {ε n : ℝ}
    (hε : 0 ≤ ε) (hn : 0 < n) (hnm : n ≤ m) (hεn : 2 * n * (s + l + m) * ε ≤ m) :
    A l s m ε n * negDerivA s l m ε n ≤ A s l m ε n * negDerivA l s m ε n := by
  have hs : 0 < s := hl.trans hls
  rw [A_swap s l m ε n, negDerivA_swap s l m ε n]
  unfold A A₀ negDerivA
  refine negDerivA_combine (s := s) (l := l) (n := n) (c := s + l + m) (e := (n + s + l)⁻¹)
    (gA := (n + s)⁻¹) (gB := (n + l)⁻¹) (a := (l + m)⁻¹) (b := (s + m)⁻¹)
    (γA := 1 + 2 * l * (l + m) * ε / (s + l + m)) (γB := 1 + 2 * s * (s + m) * ε / (s + l + m))
    (lam := (n + s + l + 2 * s * l * ε)⁻¹) hls (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) ?_ ?_
    (refined_le hs hl hm hε hn (by nlinarith)) ?_ ?_ (refined_swap_le hl hls hm hε hn hεn)
    (rest_swap_le hl hls hn)
  · field_simp
    ring
  · field_simp
    ring
  · refine Eq.trans_le ?_ (swap_le hl hls hm hn hnm)
    ring
  · have : l * (l + m) ≤ s * (s + m) := by nlinarith
    gcongr 1 + ?_ / _
    nlinarith

private theorem ratio_antitoneOn (hl : 0 < l) (hls : l < s) (hm : 0 < m) {ε n₁ n₂ : ℝ} (hε : 0 ≤ ε)
    (hn₁ : 0 < n₁) (hn₂ : n₂ ≤ m) (hεn : 2 * n₂ * (s + l + m) * ε ≤ m) :
    AntitoneOn (fun n ↦ A l s m ε n / A s l m ε n) (Set.Icc n₁ n₂) := by
  have hs : 0 < s := hl.trans hls
  have hD : ∀ n, 0 < n → 0 < A s l m ε n := fun n hn ↦ by unfold A A₀; positivity
  have hder : ∀ n, 0 < n → HasDerivAt (fun n ↦ A l s m ε n / A s l m ε n)
      ((-negDerivA l s m ε n * A s l m ε n - A l s m ε n * -negDerivA s l m ε n) /
        A s l m ε n ^ 2) n :=
    fun n hn ↦ (hasDerivAt_A hl hs hm hε hn).fun_div (hasDerivAt_A hs hl hm hε hn) (hD n hn).ne'
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (f' := fun n ↦ (-negDerivA l s m ε n * A s l m ε n - A l s m ε n * -negDerivA s l m ε n) /
      A s l m ε n ^ 2)
    (fun x hx ↦ (hder x (hn₁.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Icc] at hx
    exact (hder x (hn₁.trans hx.1)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    have hx0 : 0 < x := hn₁.trans hx.1
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have hc : 0 ≤ (s + l + m) * ε := by positivity
    have := A_mul_negDerivA_le hl hls hm hε hx0 (hx.2.le.trans hn₂)
      (by nlinarith [mul_le_mul_of_nonneg_right hx.2.le hc])
    linarith

private theorem ratio_lt (hl : 0 < l) (hls : l < s) (hm : 0 < m) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁)
    (h₁₂ : t₁ < t₂) (ht₂ : t₂ ≤ 1) :
    A l s m ((1 - t₂) ^ 2 / (2 * t₂ * (s + l + m))) (t₂ * m) /
        A s l m ((1 - t₂) ^ 2 / (2 * t₂ * (s + l + m))) (t₂ * m) <
      A l s m ((1 - t₁) ^ 2 / (2 * t₁ * (s + l + m))) (t₁ * m) /
        A s l m ((1 - t₁) ^ 2 / (2 * t₁ * (s + l + m))) (t₁ * m) := by
  have hs : 0 < s := hl.trans hls
  have hc : 0 < s + l + m := by positivity
  have ht₂0 : 0 < t₂ := ht₁.trans h₁₂
  have hε₂ : 0 ≤ (1 - t₂) ^ 2 / (2 * t₂ * (s + l + m)) := by positivity
  have hε : (1 - t₂) ^ 2 / (2 * t₂ * (s + l + m)) < (1 - t₁) ^ 2 / (2 * t₁ * (s + l + m)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 - t₂) ^ 2 ≤ (1 - t₁) ^ 2 := by nlinarith
    have h2 : 0 < (1 - t₁) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * t₁ * (s + l + m) by positivity),
      mul_lt_mul_of_pos_left h₁₂ (show 0 < 2 * (s + l + m) * (1 - t₁) ^ 2 by positivity)]
  have hεn : 2 * (t₂ * m) * (s + l + m) * ((1 - t₂) ^ 2 / (2 * t₂ * (s + l + m))) ≤ m := by
    rw [show 2 * (t₂ * m) * (s + l + m) * ((1 - t₂) ^ 2 / (2 * t₂ * (s + l + m))) =
      m * (1 - t₂) ^ 2 by field_simp]
    have : (1 - t₂) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hm.le]
  calc _ ≤ A l s m ((1 - t₂) ^ 2 / (2 * t₂ * (s + l + m))) (t₁ * m) /
        A s l m ((1 - t₂) ^ 2 / (2 * t₂ * (s + l + m))) (t₁ * m) :=
      ratio_antitoneOn hl hls hm hε₂ (by positivity) (by nlinarith) hεn
        ⟨le_rfl, by nlinarith⟩ ⟨by nlinarith, le_rfl⟩ (by nlinarith)
    _ < _ := ratio_lt_of_lt hl hls hm (by positivity) hε₂ hε

end Inequality

private theorem sum_refinement (f : Refinement → ℝ) :
    ∑ r, f r = f .both + f .freq + f .rare := by
  rw [show (Finset.univ : Finset Refinement) = {.both, .freq, .rare} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

private theorem real_univ_pos [IsFiniteMeasure μ] {w : Meaning} (hw : μ {w} ≠ 0) :
    0 < μ.real Set.univ :=
  (ENNReal.toReal_pos hw (measure_ne_top _ _)).trans_le (measureReal_mono (Set.subset_univ _))

private theorem production_eq (hα : 0 < α) [IsFiniteMeasure μ] {w : Meaning} (hw : μ {w} ≠ 0)
    {s l m t : ℝ} (hs : Real.exp (-(α * C .short)) = s) (hl : Real.exp (-(α * C .long)) = l)
    (hm : Real.exp (-(α * C .null)) = m) (ht : weight α μ w Set.univ = t) :
    production α C μ w .short = s * A s l m ((1 - t) ^ 2 / (2 * t * (s + l + m))) (t * m) ∧
      production α C μ w .long = l * A l s m ((1 - t) ^ 2 / (2 * t * (s + l + m))) (t * m) := by
  have hs0 : 0 < s := hs ▸ Real.exp_pos _
  have hl0 : 0 < l := hl ▸ Real.exp_pos _
  have hm0 : 0 < m := hm ▸ Real.exp_pos _
  have ht0 : 0 < t := ht ▸ (weight_univ α μ w).symm ▸ Real.rpow_pos_of_pos
    (div_pos (ENNReal.toReal_pos hw (measure_ne_top _ _)) (real_univ_pos μ hw)) _
  rw [production_short α C μ hα, production_long α C μ hα]
  simp only [Fintype.sum_prod_type, sum_refinement, Refinement.den, ht, hs, hl, hm]
  cases w
  · simp only [weight_singleton_self α μ hw,
      weight_singleton_of_ne α μ (by decide : Meaning.freq ≠ .rare), zero_mul, zero_div, add_zero,
      zero_add, one_mul]
    constructor <;>
    · unfold A A₀
      field_simp
      ring
  · simp only [weight_singleton_self α μ hw,
      weight_singleton_of_ne α μ (by decide : Meaning.rare ≠ .freq), zero_mul, zero_div, add_zero,
      zero_add, one_mul]
    constructor <;>
    · unfold A A₀
      field_simp
      ring

/-- **M-implicature.** Under lexical uncertainty the listener who hears the costly utterance
takes the rare meaning to be likelier than the listener who hears the cheap one, at every
rationality, every prior favouring the frequent meaning and every cost of the null utterance. -/
theorem L1_fst_rare_lt (hα : 0 < α) (hC : C .short < C .long) [IsFiniteMeasure μ]
    (hμ : μ {.rare} < μ {.freq}) (hr : μ {.rare} ≠ 0) :
    (L1 α C μ .short).fst.real {.rare} < (L1 α C μ .long).fst.real {.rare} := by
  have hf : μ {.freq} ≠ 0 := (zero_le.trans_lt hμ).ne'
  rw [L1_fst_rare_lt_iff α C μ hα hf hr]
  obtain ⟨hFS, hFL⟩ := production_eq α C μ hα hf rfl rfl rfl rfl
  obtain ⟨hrS, hrL⟩ := production_eq α C μ hα hr rfl rfl rfl rfl
  rw [hFS, hFL, hrS, hrL]
  set s := Real.exp (-(α * C .short))
  set l := Real.exp (-(α * C .long))
  set m := Real.exp (-(α * C .null))
  have hl : 0 < l := Real.exp_pos _
  have hm : 0 < m := Real.exp_pos _
  have hls : l < s := Real.exp_lt_exp.2 (by nlinarith)
  have hs : 0 < s := hl.trans hls
  have hU := real_univ_pos μ hf
  have hfr : μ.real {.rare} < μ.real {.freq} :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hμ
  have hr0 : 0 < μ.real {.rare} := ENNReal.toReal_pos hr (measure_ne_top _ _)
  have htr : 0 < weight α μ .rare Set.univ := by
    rw [weight_univ]; exact Real.rpow_pos_of_pos (div_pos hr0 hU) _
  have htrF : weight α μ .rare Set.univ < weight α μ .freq Set.univ := by
    rw [weight_univ, weight_univ]
    exact Real.rpow_lt_rpow (div_pos hr0 hU).le (div_lt_div_of_pos_right hfr hU) hα
  have htF : weight α μ .freq Set.univ ≤ 1 := by
    rw [weight_univ]
    exact Real.rpow_le_one (div_pos (hr0.trans hfr) hU).le
      ((div_le_one hU).2 (measureReal_mono (Set.subset_univ _))) hα.le
  have key := ratio_lt hl hls hm htr htrF htF
  set tF := weight α μ .freq Set.univ
  set tr := weight α μ .rare Set.univ
  have hApos : ∀ {s l : ℝ}, 0 < s → 0 < l → ∀ {t : ℝ}, 0 < t →
      0 < A s l m ((1 - t) ^ 2 / (2 * t * (s + l + m))) (t * m) := by
    intro s l hs hl t ht
    unfold A A₀
    positivity
  rw [div_lt_div_iff₀ (hApos hs hl (htr.trans htrF)) (hApos hs hl htr)] at key
  have := mul_lt_mul_of_pos_left key (mul_pos hs hl)
  rw [show s + l + m = l + s + m by ring] at *
  nlinarith [this]

/-! ### Weak bidirection

The paper relates the M-implicature to Horn's division of pragmatic labour, which weak
bidirectional optimality theory derives by pairing the unmarked form with the unmarked meaning
and the marked form with the marked one. Forms are marked by cost and meanings by rarity. -/

/-- The two forms of the Horn game, the cheap one unmarked. -/
inductive Form where
  | short
  | long
  deriving DecidableEq, Fintype

/-- The utterance of a form. -/
def Form.toUtterance : Form → Utterance
  | .short => .short
  | .long => .long

/-- The competing form. -/
def Form.other : Form → Form
  | .short => .long
  | .long => .short

/-- The markedness of a form: the costly one is marked. -/
def Form.markedness : Form → ℕ
  | .short => 0
  | .long => 1

/-- The markedness of a meaning: the rare one is marked. -/
def Meaning.markedness : Meaning → ℕ
  | .freq => 0
  | .rare => 1

instance : LinearOrder Form := LinearOrder.lift' Form.markedness (by decide)

instance : LinearOrder Meaning := LinearOrder.lift' Meaning.markedness (by decide)

/-- The iconic pairing of forms and meanings by markedness. -/
def iconicity : Form ≃o Meaning where
  toFun | .short => .freq | .long => .rare
  invFun | .freq => .short | .rare => .long
  left_inv a := by cases a <;> rfl
  right_inv b := by cases b <;> rfl
  map_rel_iff' {a b} := by cases a <;> cases b <;> decide

/-- The listener under lexical uncertainty associates a form with a meaning when, having heard
it, she finds the meaning likelier than she does having heard the competing form. -/
def Associates (p : Form × Meaning) : Prop :=
  (L1 α C μ p.1.other.toUtterance).fst.real {p.2} < (L1 α C μ p.1.toUtterance).fst.real {p.2}

private theorem L1_fst_real_freq_add_rare (hα : 0 < α) [IsFiniteMeasure μ] (hf : μ {.freq} ≠ 0)
    (u : Form) :
    (L1 α C μ u.toUtterance).fst.real {.freq} + (L1 α C μ u.toUtterance).fst.real {.rare} = 1 := by
  have : IsProbabilityMeasure (L1 α C μ u.toUtterance) :=
    isProbabilityMeasure_listener_of_ne_zero _ _ (w := (.freq, base))
      (by rw [← Set.singleton_prod_singleton, Measure.prod_prod]
          exact mul_ne_zero hf (uniformOn_univ_singleton_ne_zero _))
      ((speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff hα C μ _ _ _).2
        ⟨by cases u <;> simp [sem, base, Refinement.den, Form.toUtterance], hf⟩)
  have h := sum_measureReal_singleton_eq_one (L1 α C μ u.toUtterance).fst
  rwa [Fintype.sum_eq_add Meaning.freq Meaning.rare (by decide)
    fun m hm ↦ by cases m <;> simp at hm] at h

/-- **The division of pragmatic labour.** Under lexical uncertainty the listener associates each
form with the meaning of the same markedness, exactly the pairs that weak bidirection takes to be
super-optimal under every harmony strictly monotone in markedness. -/
theorem setOf_associates_eq_superoptimalSet (hα : 0 < α) (hC : C .short < C .long)
    [IsFiniteMeasure μ] (hμ : μ {.rare} < μ {.freq}) (hr : μ {.rare} ≠ 0) {β : Type*}
    [Preorder β] {f : Form × Meaning → β} (hf : StrictMono f) :
    {p | Associates α C μ p} = BidirectionalOT.superoptimalSet Set.univ f := by
  rw [BidirectionalOT.superoptimalSet_eq_graphOn _ iconicity hf Set.finite_univ.isWF
    (Set.subset_univ _)]
  have h := L1_fst_rare_lt α C μ hα hC hμ hr
  have hf0 : μ {.freq} ≠ 0 := (zero_le.trans_lt hμ).ne'
  have hS := L1_fst_real_freq_add_rare α C μ hα hf0 .short
  have hL := L1_fst_real_freq_add_rare α C μ hα hf0 .long
  ext ⟨a, b⟩
  simp only [Set.mem_ofPred_eq, Set.mem_graphOn, Set.mem_univ, true_and, Associates]
  cases a <;> cases b <;> simp only [Form.other, Form.toUtterance] at hS hL ⊢ <;>
    first
    | exact iff_of_true (by linarith) rfl
    | exact iff_of_false (by linarith) (by decide)

end BergenLevyGoodman2016
